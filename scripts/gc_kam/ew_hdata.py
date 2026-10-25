"""UNTRUSTED (energy window): the node torus K_j of the high-resolution pipeline from the tori of
ew_tori.py: Chebyshev coefficients in the pitch variable (16 nodes, as lam_cheb.py), truncated to
degree D = 12, rounded to the grid 2^-107 of the layout N = 36, M = 27 (as lam_cert.slice_grids).
Usage: python ew_hdata.py TORI_DIR OUT.pkl"""
import sys, os, pickle, numpy as np, gmpy2
from gmpy2 import mpfr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kam_oracle'))
from flow_torus import index_sets
from fam_ball import encode_slice
gmpy2.get_context().precision = 220
NT, MT, n = 28, 20, 16
N, M, S, D = 36, 27, 107, 12
A, B = [], []
for k in range(n):
    d = np.load(sys.argv[1] + '/t_%d_%d_%d_%d.npz' % (NT, MT, n, k))
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
su, sz = [], []
for jw in range(D + 1):
    fac = mpfr(1) if jw == 0 else mpfr(1) / 2
    GU = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    GZ = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    for (k, m), x in zip(Is, CA[jw]):
        x = x * fac
        if (k, m) == (0, 0):
            xx = x - 1 if jw == 0 else x
            GU[N][M] = int(gmpy2.rint(xx * mpfr(2) ** S / 2)) * 2
        else:
            v = int(gmpy2.rint(x * mpfr(2) ** (S - 1)))
            GU[N + k][M + m] = v
            GU[N - k][M - m] = v
    for (k, m), x in zip(Iz, CB[jw]):
        v = int(gmpy2.rint(x * fac * mpfr(2) ** (S - 1)))
        GZ[N + k][M + m] = v
        GZ[N - k][M - m] = -v
    su.append(encode_slice(GU, N, M, 1)[0])
    sz.append(encode_slice(GZ, N, M, -1)[0])
tail = max(abs(float(c)) for c in CA[D + 1]) if len(CA) > D + 1 else 0
pickle.dump({'su': su, 'sz': sz}, open(sys.argv[2], 'wb'))
print('done; |CA[13]|max = %.2e' % tail)
