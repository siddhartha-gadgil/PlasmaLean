"""Untrusted oracle for PlasmaLean/Design/ValidatedBVP.lean.

Equation: u'' - u + u^2 = beta cos x, Z-indexed Fourier coefficients (nu = 1).
Usage: python3 scripts/validated_bvp_oracle.py K beta den Aden   (used: 3 4/5 100000 1000)
Prints the rounded candidate (numerators over den), the block of A (numerators over Aden)
and the bounds Y0, Z_block, tail, Z2, injectivity defect. Nothing here is trusted: Lean
re-checks every bound by exact rational arithmetic.
"""
from fractions import Fraction as Fr
import sys
# u'' - u + u^2 = f,  f = beta*cos x  =>  f_{+-1} = beta/2
# Z-indexed coefficients a_k = a_{-k}; F(a)_k = a_k - lam_k ((a*a)_k - f_k), lam_k = 1/(1+k^2)
K = int(sys.argv[1]); beta = Fr(sys.argv[2]); den = int(sys.argv[3]); Aden=int(sys.argv[4])
lam = lambda k: Fr(1, 1+k*k)
def conv(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i+j] = out.get(i+j, 0) + x*y
    return out
def F(a):
    aa = conv(a, a)
    f = {1: beta/2, -1: beta/2}
    ks = set(aa) | set(a) | set(f)
    return {k: a.get(k,0) - lam(k)*(aa.get(k,0) - f.get(k,0)) for k in ks}
idx = list(range(-K, K+1))
def jac(a):
    return [[(1 if l==m else 0) - 2*lam(l)*a.get(l-m,0) for m in idx] for l in idx]
def solve(M, v):
    n=len(M); M=[[float(x) for x in r]+[float(v[i])] for i,r in enumerate(M)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(M[r][c])); M[c],M[p]=M[p],M[c]
        for r in range(n):
            if r!=c:
                t=M[r][c]/M[c][c]
                M[r]=[x-t*y for x,y in zip(M[r],M[c])]
    return [M[i][n]/M[i][i] for i in range(n)]
def inv(M):
    n=len(M); cols=[solve(M,[1 if i==j else 0 for i in range(n)]) for j in range(n)]
    return [[cols[j][i] for j in range(n)] for i in range(n)]
a = {k: 0.0 for k in idx}
beta_t=beta
for step in range(1,21):
  beta = beta_t*step/20
  for it in range(30):
    Fa = F({k: Fr(v) for k,v in a.items()})
    d = solve(jac({k:Fr(v) for k,v in a.items()}), [Fa.get(k,0) for k in idx])
    a = {k: a[k]-d[i] for i,k in enumerate(idx)}
beta=beta_t
print('galerkin res', max(abs(float(F({k: Fr(v) for k,v in a.items()}).get(k,0))) for k in idx))
# symmetrize and round
ab = {}
for k in range(0, K+1):
    v = Fr(round((a[k]+a[-k])/2*den), den)
    ab[k]=v; ab[-k]=v
print("abar", {k: float(ab[k]) for k in range(K+1)})
M = jac(ab)
Ai = inv(M)
A = [[Fr(round(x*Aden), Aden) for x in r] for r in Ai]
Fa = F(ab)
# Y0
Y0 = 0
for i,k in enumerate(idx):
    Y0 += abs(sum(A[i][j]*Fa.get(l,0) for j,l in enumerate(idx)))
for k,v in Fa.items():
    if abs(k) > K: Y0 += abs(v)
# C matrix
ext = list(range(-2*K, 2*K+1))
def C(i,k,m):
    s = (1 if k==m else 0)
    for j,l in enumerate(idx):
        s -= A[i][j]*((1 if l==m else 0) - 2*lam(l)*ab.get(l-m,0))
    return s
Zb = max(sum(abs(C(i,k,m)) for i,k in enumerate(idx)) for m in ext)
na = sum(abs(v) for v in ab.values())
Zt = 2*lam(K+1)*na
colA = max(lam(l)*sum(abs(A[i][j]) for i in range(len(idx))) for j,l in enumerate(idx))
Z2 = 2*max(colA, lam(K+1))
Z0 = Zb+Zt
print("Y0",float(Y0),"Zb",float(Zb),"Zt",float(Zt),"Z0",float(Z0),"Z2",float(Z2),"normabar",float(na))
disc = (1-Z0)**2 - 4*Z2*Y0
print("disc",float(disc))
if disc>0:
    import math
    rmin=((1-Z0)-math.sqrt(disc))/(2*Z2); rmax=((1-Z0)+math.sqrt(disc))/(2*Z2)
    print("r interval", rmin, rmax)
# injectivity check: I - M A
n=len(idx)
MA=[[sum(M[i][l]*A[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
inj=max(sum(abs((1 if i==j else 0)-MA[i][j]) for i in range(n)) for j in range(n))
print("inj",float(inj))
print("colA",float(colA),"lam",float(lam(K+1)))
print("abarNum", [int(ab[k]*den) for k in range(K+1)])
print("ANum", [[int(x*Aden) for x in r] for r in A])
print("Y0 exact", Y0)
