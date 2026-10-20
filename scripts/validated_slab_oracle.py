"""Untrusted oracle for PlasmaLean/Design/ValidatedSlabEquilibrium.lean.

Equation (normalized slab Grad-Shafranov with exponential pressure):
    phi'' + a (exp(phi) - 1) = 0,   2*pi-periodic, even,   a = 51/50.
Fourier (Z-indexed, nu = 1):  -k^2 phi_k + a((e^phi)_k - delta_k) = 0.
Zero-finding map on l^1(Z):  F(phi) = -phi + Lam(phi + a(e^phi - 1)),  Lam_k = 1/(1+k^2),
symmetrized as Ft(u) = F(P_e u) - P_o u (removes the translation symmetry).

Prints (all exact rationals):
  * candidate numerators ubar_0..ubar_M over DU,
  * Taylor terms P_0..P_N (numerators over DP, even, support |k| <= K) with defects rho_n,
  * the block of A (numerators over DA),
  * the bounds Y0, Zblock, cAL, normEbar, inj defect.
Nothing here is trusted: Lean re-checks every bound by exact rational arithmetic.
Usage: python3 scripts/validated_slab_oracle.py
"""
from fractions import Fraction as Fr
import math, sys

a = Fr(51, 50)
M = 10          # candidate modes |k| <= M
K = 16          # support of Taylor terms
N = 16          # Taylor degree
DU = 10**14
DP = 10**16
DA = 10**5

def conv(x, y, trunc=None):
    out = {}
    for i, u in x.items():
        if u == 0: continue
        for j, v in y.items():
            if v == 0: continue
            k = i + j
            if trunc is not None and abs(k) > trunc: continue
            out[k] = out.get(k, 0) + u * v
    return out

# ---------- float Newton ----------
def fexp(p, T, terms=60):
    E = {0: 1.0}; t = {0: 1.0}
    for n in range(1, terms):
        t = conv(t, p, T); t = {k: v / n for k, v in t.items()}
        for k, v in t.items(): E[k] = E.get(k, 0) + v
    return E

def solve_lin(A, b):
    n = len(b); Mx = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(Mx[r][c])); Mx[c], Mx[p] = Mx[p], Mx[c]
        for r in range(n):
            if r != c:
                f = Mx[r][c] / Mx[c][c]
                for j in range(c, n + 1): Mx[r][j] -= f * Mx[c][j]
    return [Mx[i][n] / Mx[i][i] for i in range(n)]

def inv(A):
    n = len(A)
    cols = [solve_lin(A, [1.0 if i == j else 0.0 for i in range(n)]) for j in range(n)]
    return [[cols[j][i] for j in range(n)] for i in range(n)]

NN = 24
af = float(a)
c = [0.0] * (NN + 1); c[1] = 0.25; c[0] = -0.06
for it in range(50):
    p = {k: c[abs(k)] for k in range(-NN, NN + 1)}
    E = fexp(p, 2 * NN)
    F = [-k * k * c[k] + af * (E.get(k, 0) - (1 if k == 0 else 0)) for k in range(NN + 1)]
    J = [[(af * E.get(k, 0) if m == 0 else af * (E.get(k - m, 0) + E.get(k + m, 0)))
          - (k * k if k == m else 0) for m in range(NN + 1)] for k in range(NN + 1)]
    dc = solve_lin(J, [-f for f in F])
    c = [c[i] + dc[i] for i in range(NN + 1)]
    if max(map(abs, dc)) < 1e-17: break

ubarNum = [round(c[k] * DU) for k in range(M + 1)]
ubar = {k: Fr(ubarNum[abs(k)], DU) for k in range(-M, M + 1)}
normU = sum(abs(v) for v in ubar.values())

# ---------- Taylor terms with defects ----------
P = [{0: Fr(1)}]
PNum = [[DP] + [0] * K]
rho = [Fr(0)]
for n in range(1, N + 1):
    ex = conv(ubar, P[-1]); ex = {k: v / n for k, v in ex.items()}
    num = [round(ex.get(k, 0) * DP) for k in range(K + 1)]
    Pn = {k: Fr(num[abs(k)], DP) for k in range(-K, K + 1)}
    r = sum(abs(ex.get(k, 0) - Pn.get(k, 0)) for k in set(ex) | set(Pn))
    P.append(Pn); PNum.append(num); rho.append(r)
Ebar = {}
for Pn in P:
    for k, v in Pn.items(): Ebar[k] = Ebar.get(k, 0) + v
normE = sum(abs(v) for v in Ebar.values())

# error recursion e_n >= ||u^n/n! - P_n||, e_0 = 0
m = normU
e = [Fr(0)]
for n in range(1, N + 1):
    e.append(m * e[-1] / n + rho[n])
q = m / (N + 2)
tail = m ** (N + 1) / math.factorial(N + 1) / (1 - q)
delta = sum(e) + tail

lam = lambda k: Fr(1, 1 + k * k)
blk = list(range(-M, M + 1))
N2 = M + K
blk2 = list(range(-N2, N2 + 1))
d = lambda i, j: 1 if i == j else 0
def Jent(l, mm):
    return -d(l, mm) + lam(l) * (Fr(d(l, mm) + d(l, -mm), 2)
                                 + a * (Ebar.get(l - mm, 0) + Ebar.get(l + mm, 0)) / 2)
Jsq = [[float(Jent(l, mm)) for mm in blk] for l in blk]
Af = inv(Jsq)
ANum = [[round(Af[i][j] * DA) for j in range(len(blk))] for i in range(len(blk))]
Aq = lambda k, l: Fr(ANum[k + M][l + M], DA)

# Zblock
Zblock = max(sum(abs(d(k, mm) - sum(Aq(k, l) * Jent(l, mm) for l in blk)) for k in blk)
             for mm in blk2)
# cAL
cAL = max(max(sum(abs(Aq(k, l) * lam(l)) for k in blk) for l in blk), lam(M + 1))
# inj: I - Jsq A on block
injd = max(sum(abs(d(k, mm) - sum(Jent(k, l) * Aq(l, mm) for l in blk)) for k in blk)
           for mm in blk)
# Fbar = -ubar + Lam(ubar + a(Ebar - delta0))
Fbar = {}
for k in range(-K, K + 1):
    Fbar[k] = -ubar.get(k, 0) + lam(k) * (ubar.get(k, 0) + a * (Ebar.get(k, 0) - d(k, 0)))
AF = sum(abs(sum(Aq(k, l) * Fbar[l] for l in blk)) for k in blk) + \
     sum(abs(Fbar[k]) for k in Fbar if abs(k) > M)
tailZ = (1 + a * normE) * lam(M + 1)
print("ubarNum =", ubarNum)
print("normU =", float(normU))
print("rho =", [float(x) for x in rho])
print("delta =", float(delta), " tail =", tail)
print("normEbar =", float(normE))
print("Zblock =", float(Zblock), " tailZ =", float(tailZ), " cAL =", float(cAL), " inj =", float(injd))
print("AFbar =", float(AF))
Z0 = Zblock + tailZ + a * cAL * delta
Y0 = AF + a * cAL * delta
print("Z0 =", float(Z0), " Y0 =", float(Y0))
Z2 = a * cAL * Fr(272, 100)
print("Z2 (Eb=2.72) =", float(Z2))
disc = (1 - Z0) ** 2 - 4 * Z2 * Y0
print("disc>0:", disc > 0, " rmin ~", float(2 * Y0 / (1 - Z0)), " rmax ~", float((1 - Z0) / Z2))
if len(sys.argv) > 1 and sys.argv[1] == "dump":
    print("PNum =", PNum)
    print("ANum =", ANum)
if len(sys.argv) > 1 and sys.argv[1] == "lean":
    EbarNum = [int(Ebar.get(k, 0) * DP) for k in range(K + 1)]
    assert all(Ebar.get(k, 0) * DP == EbarNum[k] for k in range(K + 1))
    def fmt(l): return "[" + ", ".join(str(v) for v in l) + "]"
    print("ubarNum := " + fmt(ubarNum))
    print("PNum := [" + ",\n   ".join(fmt(r) for r in PNum) + "]")
    print("EbarNum := " + fmt(EbarNum))
    print("ANum := [" + ",\n   ".join(fmt(r) for r in ANum) + "]")
