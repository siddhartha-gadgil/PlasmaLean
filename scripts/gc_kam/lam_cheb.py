"""UNTRUSTED: Chebyshev coefficients (in lam) of the high-precision tori of lam_tori.py.
Usage: python lam_cheb.py NT MT n [out.npz]"""
import sys, os, math, numpy as np, gmpy2
from gmpy2 import mpfr
gmpy2.get_context().precision = 220
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')
from flow_torus import index_sets
NT, MT, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
A, B = [], []
for k in range(n):
    d = np.load(os.environ.get('LAM_TORI_DIR', '/tmp/lamw/tori') + '/t_%d_%d_%d_%d.npz' % (NT, MT, n, k))
    A.append([mpfr(s) for s in d['a']]); B.append([mpfr(s) for s in d['b']])
PI = gmpy2.const_pi()
def cheb(F):
    out = []
    for j in range(n):
        cj = [mpfr(0)] * len(F[0])
        for k in range(n):
            t = gmpy2.cos(j * PI * (k + mpfr(1) / 2) / n)
            cj = [c + t * f for c, f in zip(cj, F[k])]
        fac = mpfr(1) / n if j == 0 else mpfr(2) / n
        out.append([c * fac for c in cj])
    return out
CA, CB = cheb(A), cheb(B)
Is, Iz = index_sets(NT, MT)
for j in range(n):
    na = sum(abs(float(c)) * math.exp(0.1257 * (abs(k) + abs(m))) for (k, m), c in zip(Is, CA[j]) if j > 0 or (k, m) != (0, 0))
    nb = sum(abs(float(c)) * math.exp(0.1257 * (abs(k) + abs(m))) for (k, m), c in zip(Iz, CB[j]))
    print(j, '%.3e %.3e' % (na, nb))
if len(sys.argv) > 4:
    np.savez(sys.argv[4], CA=np.array([[str(c) for c in r] for r in CA]), CB=np.array([[str(c) for c in r] for r in CB]), NT=NT, MT=MT)
