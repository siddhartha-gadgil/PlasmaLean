"""UNTRUSTED.  Oracle for the surrogate-torus certificates of torus A (KamTorusASurrogate*).

Designs q ~ 1/(D^3 W0^2) on the surrogate torus of KamTorusAFrameData (modes |k| <= 14,
|m| <= 10, coefficients over 2^66), builds the expression trees of 8 D and 128 P (Horner form,
homogenised with t, V), and predicts every kernel computation of KamTorusASurrogateCheck.lean
exactly with big integers (Kronecker images, balanced digits, separable weighted digit sums with
the integer weights kwtS 74315 16 K s).

Usage: python surrogate_emit.py [out.lean]   (default out: /tmp/surr/Data.lean)
"""
import sys
from fractions import Fraction as Fr
import numpy as np
import gmpy2
from gmpy2 import mpz
import surrogate_common as s

sig1 = s.sig1
KQ, MQ = 14, 10          # q window (weight 2: centre (14, 10))
pQ = 66                  # q coefficients over 2^66 (the scale T^2 = sig1^2 u^14 v^10)
rA = 0.1257

# ---------------- design q (floating point) ----------------
Nt, Np = 512, 384
th = 2 * np.pi * np.arange(Nt) / Nt; ps = 2 * np.pi * np.arange(Np) / Np
TH, PS = np.meshgrid(th, ps, indexing='ij')


def ser(g, scale, n=7, m=5):
    F = np.zeros(TH.shape, complex)
    for i in range(len(g)):
        for j in range(len(g[0])):
            if g[i][j]:
                F += g[i][j] * np.exp(1j * ((i - n) * TH + (j - m) * PS))
    return F / scale


u = ser(s.gRc, sig1).real; z = ser(s.gZc, 1j * sig1).real
a = ser(s.gAc, -1j * sig1).real; b = ser(s.gBc, sig1).real
c = -np.sin(PS); sn = np.cos(PS)


def pe(mon):
    F = 0 * TH
    for co, (e0, e1, e2, e3) in mon:
        F = F + float(co) * u ** e0 * z ** e1 * c ** e2 * sn ** e3
    return F


Dv = pe(s.Dmon); Pv = pe(s.Pmon); Wv = a * z - b * u
fh = np.fft.fft2(1 / (Dv ** 3 * Wv ** 2)) / TH.size
# half window list (k = 0..14, m = -10..10, row-major); k = 0, m < 0 entries zero.
listQ = []
for k in range(0, KQ + 1):
    for m in range(-MQ, MQ + 1):
        if k == 0 and m < 0:
            listQ.append(0); continue
        cc = fh[k, m].real * (1 if (k == 0 and m == 0) else 2)
        listQ.append(int(round(cc * 2 ** (pQ - 1))))


def hQ(i, j):
    if KQ <= i <= 2 * KQ and j <= 2 * MQ:
        return listQ[(i - KQ) * (2 * MQ + 1) + j]
    return 0


gQc = [[hQ(i, j) + hQ(2 * KQ - i, 2 * MQ - j) for j in range(2 * MQ + 1)] for i in range(2 * KQ + 1)]

# ---------------- expression trees ----------------
# variables: 0 r, 1 z, 2 C, 3 S, 4 t, 5 V, 6 a, 7 b
WS = {0: (1, 0, 0), 1: (1, 0, 1), 2: (0, 1, 3), 3: (0, 1, 0), 4: (1, 0, 0), 5: (0, 1, 0),
      6: (1, 0, 3), 7: (1, 0, 0)}


def V(i): return ('var', i)
def K(k): return ('cst', k)
def add(e, f): return ('add', e, f)
def sub(e, f): return ('sub', e, f)
def mul(e, f): return ('mul', e, f)


def tpow(e, k):
    for _ in range(k):
        e = mul(e, V(4))
    return e


def horner(mon, scale, T, Vd):
    """Homogeneous Horner tree of scale * (sum of monomials) with weight (T, Vd)."""
    terms = {}
    for co, (ea, eb, eg, ed) in mon:
        k = co * scale; assert k.denominator == 1
        terms.setdefault(ea, {}).setdefault(eb, []).append((int(k), eg, ed))
    pieces = {}
    for ea in sorted(terms):
        bs = terms[ea]; B = max(bs)
        G = None
        for eb in range(B, -1, -1):
            if eb in bs:
                R = None
                for (k, eg, ed) in bs[eb]:
                    mono = K(k)
                    for _ in range(eg): mono = mul(mono, V(2))
                    for _ in range(ed): mono = mul(mono, V(3))
                    for _ in range(Vd - eg - ed): mono = mul(mono, V(5))
                    R = mono if R is None else add(R, mono)
                R = tpow(R, B - eb)
                G = R if G is None else add(mul(G, V(1)), R)
            else:
                G = mul(G, V(1))
        pieces[ea] = tpow(G, T - ea - B)
    amax = max(pieces)
    H = pieces[amax]
    for ea in range(amax - 1, -1, -1):
        H = mul(H, V(0))
        if ea in pieces:
            H = add(H, pieces[ea])
    return H, pieces, amax


def wt(e):
    if e[0] == 'var': return WS.get(e[1], (0, 0, 0))
    if e[0] == 'cst': return (0, 0, 0)
    x, y = wt(e[1]), wt(e[2])
    if x is None or y is None: return None
    if e[0] == 'mul': return (x[0] + y[0], x[1] + y[1], (x[2] + y[2]) % 4)
    if x[0] == y[0] and x[1] == y[1] and (x[2] + y[2]) % 2 == 0: return x
    return None


def sgn(e, f):
    x, y = wt(e), wt(f)
    if x is None or y is None: return 1
    return 1 if x[2] == y[2] else -1


def evH(e, env):
    t = e[0]
    if t == 'var': return env[e[1]]
    if t == 'cst': return mpz(e[1])
    x = evH(e[1], env)
    if t == 'mul': return x * evH(e[2], env)
    y = evH(e[2], env) * sgn(e[1], e[2])
    return x + y if t == 'add' else x - y


def evR(e, env):   # honest real evaluation
    t = e[0]
    if t == 'var': return env[e[1]]
    if t == 'cst': return e[1]
    x, y = evR(e[1], env), evR(e[2], env)
    return x + y if t == 'add' else (x - y if t == 'sub' else x * y)


def majN(e, L):
    t = e[0]
    if t == 'var': return L[e[1]]
    if t == 'cst': return abs(e[1])
    x, y = majN(e[1], L), majN(e[2], L)
    return x * y if t == 'mul' else x + y


eD, piecesD, amaxD = horner(s.Dmon, 8, 5, 1)
eP, piecesP, amaxP = horner(s.Pmon, 128, 11, 2)
eW = sub(mul(V(6), V(1)), mul(V(7), V(0)))
print('[trees] wt D', wt(eD), 'wt P', wt(eP), 'wt W', wt(eW))
# real check of the trees against the monomial forms at a random point
import random
pt = [random.uniform(-.3, .3) for _ in range(4)]
env = {0: pt[0], 1: pt[1], 2: pt[2], 3: pt[3], 4: 1.0, 5: 1.0, 6: 0, 7: 0}
dd = sum(float(co) * pt[0] ** e0 * pt[1] ** e1 * pt[2] ** e2 * pt[3] ** e3 for co, (e0, e1, e2, e3) in s.Dmon)
pp = sum(float(co) * pt[0] ** e0 * pt[1] ** e1 * pt[2] ** e2 * pt[3] ** e3 for co, (e0, e1, e2, e3) in s.Pmon)
print('[trees] real check', evR(eD, env) - 8 * dd, evR(eP, env) - 128 * pp)


def size(e):
    return 1 if e[0] in ('var', 'cst') else 1 + size(e[1]) + size(e[2])


print('[trees] sizes', size(eD), size(eP))

# ---------------- Kronecker computations ----------------


def gridL1(g): return sum(abs(x) for row in g for x in row)


def pack(g, b, W):
    v = mpz(0)
    for i in range(len(g)):
        for j in range(len(g[0])):
            if g[i][j]:
                v += mpz(g[i][j]) << (b * (i + W * j))
    return v


def baseInt(b, W):
    one = mpz(1)
    return {0: pack(s.gRc, b, W), 1: pack(s.gZc, b, W), 2: (one << (b * 2 * W)) - 1,
            3: (one << (b * 2 * W)) + 1, 4: mpz(sig1) << (b * (7 + W * 5)), 5: mpz(2) << (b * W),
            6: pack(s.gAc, b, W), 7: pack(s.gBc, b, W)}


LB = {0: gridL1(s.gRc), 1: gridL1(s.gZc), 2: 2, 3: 2, 4: sig1, 5: 2, 6: gridL1(s.gAc), 7: gridL1(s.gBc)}
LQ = gridL1(gQc)


def digits(X, b, nslots):
    """balanced base-2^b digits of X (nslots of them)."""
    H = mpz(1) << (b - 1)
    off = mpz(0)
    for n in range(nslots):
        off += H << (b * n)
    Y = X + off
    assert Y >= 0 and Y < (mpz(1) << (b * nslots))
    out = []

    def rec(Y, n):
        if n == 1:
            out.append(int(Y) - int(H)); return
        h = n // 2
        lo = Y & ((mpz(1) << (b * h)) - 1)
        rec(lo, h); rec(Y >> (b * h), n - h)
    rec(Y, nslots)
    return out


def kwtS(p, e, Kk, ss): return p ** ss * 2 ** (e * max(Kk - ss, 0))


def wl1(dig, W, rows, i0, j0, Ki, Kj):
    wA = [kwtS(74315, 16, Ki, abs(i - i0)) for i in range(W)]
    tot = 0
    for j in range(rows):
        rs = 0
        for i in range(W):
            d = dig[i + W * j]
            if d: rs += wA[i] * abs(d)
        tot += kwtS(74315, 16, Kj, abs(j - j0)) * rs
    return tot


def ceil_ratio(num, den, digits_=4):
    """smallest c/10^k (k chosen) with num/den <= c/10^k, reported as (c, k)."""
    x = Fr(num, den)
    k = digits_ - 1
    while Fr(1, 10 ** k) > x / 10 ** (digits_ - 1):
        k += 1
    cc = -((-x.numerator * 10 ** k) // x.denominator)
    return cc, k


res = {}
# ---- PW, BigW = PW - c0W u^14 v^10, b, W ----
bW_, WW = 160, 29
env = baseInt(bW_, WW)
kW = evH(eW, env)
digW = digits(kW, bW_, WW * 21)
c0W = digW[14 + WW * 10]
res['c0W'] = c0W
wS = Fr(c0W, sig1 ** 2)
aprW = majN(eW, LB) + abs(c0W)
assert aprW < 2 ** (bW_ - 1)
digWs = list(digW); digWs[14 + WW * 10] = 0
sW = wl1(digWs, WW, 21, 14, 10, 14, 10)
betaW = Fr(sW, sig1 ** 2 * 2 ** (16 * 24))
print('[W] wS = %.8f  betaW = %.6g  apriori bits %d' % (float(wS), float(betaW), aprW.bit_length()))
res['betaW'] = betaW
# ---- PQ alone ----
bQ_, WQ = 96, 29
digQ = digits(pack(gQc, bQ_, WQ), bQ_, WQ * 21)
assert LQ < 2 ** (bQ_ - 1)
sQ = wl1(digQ, WQ, 21, 14, 10, 14, 10)
Bq = Fr(sQ, sig1 ** 2 * 2 ** (16 * 24))
print('[Q] ||q|| <= %.6f' % float(Bq))
res['Bq'] = Bq
# ---- Big4 = PQ PD^3 PW^2 - 512 t^21 V^3 ----
b4, W4 = 720, 295
env = baseInt(b4, W4)
kD = evH(eD, env); kWW = evH(eW, env); kQ = pack(gQc, b4, W4)
big4 = kQ * kD ** 3 * kWW ** 2 - 512 * env[4] ** 21 * env[5] ** 3
apr4 = LQ * majN(eD, LB) ** 3 * majN(eW, LB) ** 2 + 512 * sig1 ** 21 * 8
print('[4] apriori bits', apr4.bit_length(), 'b', b4)
assert apr4 < 2 ** (b4 - 1)
dig4 = digits(big4, b4, W4 * 217)
s4 = wl1(dig4, W4, 217, 147, 108, 147, 108)
eps4 = Fr(s4, 4096 * sig1 ** 21 * 2 ** (16 * (147 + 108)))
print('[4] eps_q = %.6g   centre digit %d' % (float(eps4), dig4[147 + W4 * 108]))
res['eps4'] = eps4
# ---- Big5 = (t + r)^3 PP PQ ----
kP = evH(eP, env)
big5 = (env[4] + env[0]) ** 3 * kP * kQ
apr5 = (sig1 + LB[0]) ** 3 * majN(eP, LB) * LQ
print('[5] apriori bits', apr5.bit_length())
assert apr5 < 2 ** (b4 - 1)
dig5 = digits(big5, b4, W4 * 165)
s5 = wl1(dig5, W4, 165, 112, 82, 112, 82)
c5 = 512 * sig1 ** 16
t5 = Fr(s5, c5 * 2 ** (16 * (112 + 82)))
c0T = dig5[112 + W4 * 82]
print('[5] ||T|| <= %.6f  avg = %.10f  (phase P %s)' % (float(t5), float(Fr(c0T, c5)), wt(eP)))
res['t5'] = t5; res['c0T'] = c0T; res['avg'] = Fr(c0T, c5)
res.update(listQ=listQ, eD=eD, eP=eP, piecesD=piecesD, piecesP=piecesP, amaxD=amaxD,
           amaxP=amaxP, apr4=apr4, apr5=apr5, aprW=aprW, s4=s4, s5=s5, sW=sW, sQ=sQ, b4=b4)


# ---------------- surrogate distance (item 2), big grid b = 128, W = 65 ----------------
import re
dsrc = open(s.ROOT + '/PlasmaLean/Design/KamTorusAData.lean').read()


def lit(name):
    return int(re.search(r'def ' + name + r' : ℕ := (0x[0-9a-fA-F]+)', dsrc).group(1), 16)


N, M, P = 32, 22, 90
dA, dB = lit('dataA'), lit('dataB')


def gridCoeff(data, i, j):
    if N <= i:
        f = (i - N) * (2 * M + 1) + j
        return ((data >> (96 * f)) % (1 << 96)) - (1 << 95)
    return 0


cA = lambda i, j: gridCoeff(dA, i, j)
cB = lambda i, j: gridCoeff(dB, i, j)
sig = 2 ** (P + 1)
sTA, sTB = s.symC(s.tA), s.symS(s.tB)


def bigsum(d):
    tot = 0
    for j in range(2 * M + 1):
        rs = sum(kwtS(74315, 16, 32, abs(i - N)) * abs(d(i, j)) for i in range(2 * N + 1))
        tot += kwtS(74315, 16, 22, abs(j - M)) * rs
    return tot


def gR(i, j): return cA(i, j) + cA(2 * N - i, 2 * M - j)
def gZ(i, j): return cB(i, j) - cB(2 * N - i, 2 * M - j)


dists = {
    'u': lambda i, j: gR(i, j) - 2 ** 58 * sTA(i, j) - (sig if (i, j) == (N, M) else 0),
    'z': lambda i, j: gZ(i, j) - 2 ** 58 * sTB(i, j),
    'a': lambda i, j: (i - N) * gR(i, j) - 2 ** 58 * ((i - N) * sTA(i, j)),
    'b': lambda i, j: (i - N) * gZ(i, j) - 2 ** 58 * ((i - N) * sTB(i, j)),
}
den2 = sig * 2 ** (16 * 54)
for k, d in dists.items():
    v = bigsum(d)
    res['dist_' + k] = Fr(v, den2)
    print('[dist] %s %.4g' % (k, float(Fr(v, den2))))
gl1 = lambda g: sum(abs(g(i, j)) for i in range(2 * N + 1) for j in range(2 * M + 1))
print('[dist] apriori bits', (gl1(gR) + sig + 2 ** 58 * gl1(sTA)).bit_length(),
      (gl1(gZ) + 2 ** 58 * gl1(sTB)).bit_length())


# ---------------- Lean emission ----------------


def lean_ex(e):
    t = e[0]
    if t == 'var': return '(.var %d)' % e[1]
    if t == 'cst': return '(.cst (%d))' % e[1]
    return '(.%s %s %s)' % (t, lean_ex(e[1]), lean_ex(e[2]))


def wrap(sx, ind='  ', width=98):
    out, line = [], ind
    for tok in sx.split(' '):
        if len(line) + len(tok) + 1 > width:
            out.append(line.rstrip()); line = ind + '  '
        line += tok + ' '
    out.append(line.rstrip())
    return '\n'.join(out)


def chain(pieces, amax, name):
    """Horner chain over r referencing the piece defs."""
    H = '%s%d' % (name, amax)
    for ea in range(amax - 1, -1, -1):
        H = '(.mul %s (.var 0))' % H
        if ea in pieces:
            H = '(.add %s %s%d)' % (H, name, ea)
    return H


b5, W5 = 560, 225
H5 = 2 ** (b5 - 1)
e0T = res['c0T'] + H5
assert 0 <= e0T < 2 ** b5
L = []
L.append('''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronExpr

/-!
# Data of the surrogate-torus certificates of torus A (KAM route, final stage)

Untrusted data, produced by `scripts/kam_oracle/surrogate_emit.py`; every property is proved in
`Design/KamTorusASurrogateCheck` and `Design/KamTorusASurrogate`.

* `listQ`: the cosine coefficients (times `2^65`) of a trigonometric polynomial
  `q ≈ 1/(D³ W₀²)` on the surrogate torus of `Design/KamTorusAFrameData`, modes `0 ≤ k ≤ 14`,
  `|m| ≤ 10` (row-major, `k = 0, m < 0` entries zero). Its compact grid `gQc` (centre `(14, 10)`,
  scale `2^66 = σ₁²`) is symmetric under the reflection `(i, j) ↦ (28 − i, 20 − j)`.
* `treeD`, `treeP`: expression trees (Horner form in `r = R − 1`, then `z`) of `8 D` and `128 P`
  (`D = Dp`, `P = Pp` of `Design/KamNewtonField`), homogenized with the scale variables `t`, `V`.
  Variables: `0 r, 1 z, 2 C = cos 2φ, 3 S = sin 2φ, 4 t, 5 V, 6 a = ∂_θ R, 7 b = ∂_θ z`.
* `treeW = a z − b r` (the winding form `W₀`).
* `c0W`, `e0T`: oracle values of the centre coefficient of `Ŵ₀` and of the centre digit of the
  Kronecker image of `(t + r)³ P̂ q̂` (any values are sound: the first is only subtracted, the
  second is checked by the kernel).
-/

@[expose] public section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Certificates.KronExpr
''')
L.append('/-- `2^65 ×` the cosine coefficients of `q` (row-major, `0 ≤ k ≤ 14`, `|m| ≤ 10`). -/')
L.append('def listQ : List ℤ :=\n' + wrap('[' + ', '.join(str(x) for x in res['listQ']) + ']', '  ', 99))
L.append('''
/-- Half-window lookup of `listQ` on the compact `q` grid (`14 ≤ i ≤ 28`, `j ≤ 20`). -/
def hQ (i j : ℕ) : ℤ := if 14 ≤ i ∧ i ≤ 28 ∧ j ≤ 20 then listQ.getD ((i - 14) * 21 + j) 0 else 0

/-- The compact grid of `q̂ = σ₁² u^{14} v^{10} q` (cosine symmetrization of `hQ`). -/
def gQc (i j : ℕ) : ℤ := hQ i j + hQ (28 - i) (20 - j)
''')
for name, pieces, amax, what in [('treeD', res['piecesD'], res['amaxD'], '8 D'),
                                 ('treeP', res['piecesP'], res['amaxP'], '128 P')]:
    for ea in sorted(pieces):
        L.append('/-- Coefficient of `r^%d` in the Horner form of `%s` (homogenized). -/' % (ea, what))
        L.append('def %s%d : Ex :=\n%s\n' % (name, ea, wrap(lean_ex(pieces[ea]))))
    L.append('/-- The tree of `%s` (Horner form in `r`). -/' % what)
    L.append('def %s : Ex :=\n%s\n' % (name, wrap(chain(pieces, amax, name))))
L.append('''/-- The tree of `W₀ = a z − b r`. -/
def treeW : Ex := .sub (.mul (.var 6) (.var 1)) (.mul (.var 7) (.var 0))
''')
L.append('/-- Oracle value of the centre coefficient of `Ŵ₀` (scale `σ₁²`). -/')
L.append('def c0W : ℤ := %d\n' % res['c0W'])
L.append('set_option linter.style.longLine false in')
L.append('/-- Oracle value of the centre digit (`b = 560`, offset `2^559`) of the Kronecker image of\n`(t + r)³ P̂ q̂`. -/')
L.append('def e0T : ℕ := %d\n' % e0T)
L.append('end PlasmaLean.Design.KamNewton\n')
import os
os.makedirs('/tmp/surr', exist_ok=True)
out = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] != 'x' else '/tmp/surr/Data.lean'
open(out, 'w').write('\n'.join(L))
print('[emit] wrote', out, ' c0T =', res['c0T'])
for k in ['betaW', 'Bq', 'eps4', 't5', 'avg', 'dist_u', 'dist_z', 'dist_a', 'dist_b']:
    print('   ', k, float(res[k]))
print('    wS', float(Fr(res['c0W'], sig1 ** 2)))
