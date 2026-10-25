"""UNTRUSTED oracle: invariant tori (iota = iota_A) of the mu > 0 passing guiding-centre field
B~ = B + curl(rho(x) b), rho(x) = rho0 sqrt(1 - lam |B(x)|), rho0 = 1/256, of the rational
stellarator, at the Chebyshev nodes of a cell lam in [0, LAM1].

Pointwise B~ = gcField(rho_eff(x)) with rho_eff = rho0 (1 - lam|B|/2) / sqrt(1 - lam|B|), so the flow
form is that of gcFlow with rho replaced by rho0 F, F = (1 - lam Bm/2)(1 - lam Bm)^(-1/2),
Bm = |B| = sqrt(q)/R^4.  Double-precision Galerkin-Newton, then mpfr refinement (as /tmp/fam).
Usage: python ew_tori.py NT MT n k LAM1num LAM1den   (torus at node k of n)

Energy-window variant (ew_tori.py, adapted from lam_tori.py): the gyro-length is rho = EW_RHO
(a rational 'num/den', default 1/256) instead of rho0 = 1/256; initial guess from EW_INIT
(the certified family torus, decoded from the Lean data by ew_decode_h.py).
"""
import sys, os, numpy as np, gmpy2
from gmpy2 import mpfr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kam_oracle'))
import gc_torus as GT
from flow_torus import resize, index_sets
PREC = 220
gmpy2.get_context().precision = PREC
PI = gmpy2.const_pi()
IOTA = (75 + gmpy2.sqrt(mpfr(5))) / 562
from fractions import Fraction as _Fr
_RJ = _Fr(os.environ.get('EW_RHO', '1/256'))
RHO0 = mpfr(_RJ.numerator) / _RJ.denominator
import sympy as sp
lamf = sp.lambdify((GT.u, GT.z, GT.c, GT.s), [GT.D, GT.nR, GT.nZ, GT.q, GT.KD, GT.KR, GT.KZ], modules=[{}])
lamd = GT.lam


def Fd(qv, uu, L):
    Bm = np.sqrt(qv) / (1 + uu) ** 4
    return (1 - L * Bm / 2) / np.sqrt(1 - L * Bm)


def set_double(L):
    def gp(uu, zz, cc, ss, rho):
        Dv, nRv, nZv, qv, kd, kr, kz = lamd(uu, zz, cc, ss)
        W3 = qv ** (-1.5)
        re = float(RHO0) * Fd(qv, uu, L)
        return Dv + re / 2 * W3 * kd, nRv + re / 2 * W3 * kr, nZv + re / 2 * W3 * kz
    GT.gcparts = gp


class Ctx:
    def __init__(self, N, M, Nt, Np):
        self.N, self.M, self.Nt, self.Np = N, M, Nt, Np
        self.Is, self.Iz = index_sets(N, M)
        th = [2 * PI * i / Nt for i in range(Nt)]; ps = [2 * PI * j / Np for j in range(Np)]
        self.ct = np.array([[gmpy2.cos(k * t) for t in th] for k in range(N + 1)], dtype=object)
        self.st = np.array([[gmpy2.sin(k * t) for t in th] for k in range(N + 1)], dtype=object)
        self.cp = np.array([[gmpy2.cos(m * p) for p in ps] for m in range(-M, M + 1)], dtype=object)
        self.sp_ = np.array([[gmpy2.sin(m * p) for p in ps] for m in range(-M, M + 1)], dtype=object)
        PS = np.array([ps] * Nt, dtype=object)
        self.cc = np.vectorize(lambda p: -gmpy2.sin(p), otypes=[object])(PS)
        self.ss = np.vectorize(lambda p: gmpy2.cos(p), otypes=[object])(PS)


def eval_series(cx, a, b):
    N, M, Nt, Np = cx.N, cx.M, cx.Nt, cx.Np
    zero = mpfr(0)
    R = np.full((Nt, Np), zero, dtype=object); Rth = R.copy(); Rps = R.copy()
    Z = R.copy(); Zth = R.copy(); Zps = R.copy()
    for (k, m), x in zip(cx.Is, a):
        C = np.outer(cx.ct[k], cx.cp[m + M]) - np.outer(cx.st[k], cx.sp_[m + M])
        S_ = np.outer(cx.st[k], cx.cp[m + M]) + np.outer(cx.ct[k], cx.sp_[m + M])
        R += x * C; Rth += (-k * x) * S_; Rps += (-m * x) * S_
    for (k, m), x in zip(cx.Iz, b):
        C = np.outer(cx.ct[k], cx.cp[m + M]) - np.outer(cx.st[k], cx.sp_[m + M])
        S_ = np.outer(cx.st[k], cx.cp[m + M]) + np.outer(cx.ct[k], cx.sp_[m + M])
        Z += x * S_; Zth += (k * x) * C; Zps += (m * x) * C
    return R, Z, Rth, Rps, Zth, Zps


def residual(cx, a, b, L):
    R, Z, Rth, Rps, Zth, Zps = eval_series(cx, a, b)
    U = R - 1
    Dv, nRv, nZv, qv, kd, kr, kz = lamf(U, Z, cx.cc, cx.ss)
    sq = np.vectorize(gmpy2.sqrt, otypes=[object])(qv)
    W3 = 1 / (qv * sq)
    Bm = sq / R ** 4
    Fv = (1 - L * Bm / 2) / np.vectorize(gmpy2.sqrt, otypes=[object])(1 - L * Bm)
    re = RHO0 * Fv
    Dt = Dv + re / 2 * W3 * kd; nRt = nRv + re / 2 * W3 * kr; nZt = nZv + re / 2 * W3 * kz
    LR = 2 * Rps + IOTA * Rth; LZ = 2 * Zps + IOTA * Zth
    return Dt * LR - nRt, Dt * LZ - nZt


def project(cx, r1, r2):
    N, M, Nt, Np = cx.N, cx.M, cx.Nt, cx.Np
    npts = Nt * Np
    out1 = []; out2 = []
    A1c = {m: r1.dot(cx.cp[m + M]) for m in range(-M, M + 1)}; A1s = {m: r1.dot(cx.sp_[m + M]) for m in range(-M, M + 1)}
    A2c = {m: r2.dot(cx.cp[m + M]) for m in range(-M, M + 1)}; A2s = {m: r2.dot(cx.sp_[m + M]) for m in range(-M, M + 1)}
    for (k, m) in cx.Iz:
        v = cx.st[k].dot(A1c[m]) + cx.ct[k].dot(A1s[m]); out1.append(2 * v / npts)
    for (k, m) in cx.Is:
        v = cx.ct[k].dot(A2c[m]) - cx.st[k].dot(A2s[m]); w = 1 if (k, m) == (0, 0) else 2
        out2.append(w * v / npts)
    return np.array(out1 + out2, dtype=object)


def refine(L, a0, b0, N, M, steps=2, verbose=True):
    Nt, Np = 4 * N + 8, 4 * M + 8
    cx = Ctx(N, M, Nt, Np)
    set_double(float(L))
    gD = GT.GalerkinGC(N, M, float(IOTA), 0.0, Nt, Np)
    a = np.array([mpfr(float(x)) for x in a0], dtype=object); b = np.array([mpfr(float(x)) for x in b0], dtype=object)
    J = gD.J(np.array([float(x) for x in a]), np.array([float(x) for x in b]))
    na = len(a)
    for it in range(steps):
        r1, r2 = residual(cx, a, b, L)
        F = project(cx, r1, r2)
        if verbose:
            print('  refine %d |F| = %.3e' % (it, max(abs(float(x)) for x in F)), flush=True)
        scale = mpfr(max(abs(x) for x in F))
        Fs = np.array([float(x / scale) for x in F])
        dd = np.linalg.solve(J, -Fs)
        a = a + np.array([mpfr(float(x)) * scale for x in dd[:na]], dtype=object)
        b = b + np.array([mpfr(float(x)) * scale for x in dd[na:]], dtype=object)
    return a, b


if __name__ == '__main__':
    NT, MT, n, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    L1 = mpfr(int(sys.argv[5])) / int(sys.argv[6])
    x = gmpy2.cos(PI * (k + mpfr(1) / 2) / n)
    L = L1 * (1 + x) / 2
    # initial guess: the certified family torus K(lam) (decoded by ew_decode_h.py) at this node
    d = np.load(os.environ['EW_INIT'], allow_pickle=True)
    xf = float(x)
    Tj = [np.cos(j * np.arccos(xf)) for j in range(len(d['CA']))]
    a0 = sum(t * np.array([float(_Fr(v)) for v in r]) for t, r in zip(Tj, d['CA']))
    b0 = sum(t * np.array([float(_Fr(v)) for v in r]) for t, r in zip(Tj, d['CB']))
    assert (int(d['NT']), int(d['MT'])) == (NT, MT)
    set_double(float(L))
    g = GT.GalerkinGC(NT, MT, float(IOTA), 0.0)
    a0, b0, e = GT.newton(g, a0, b0, steps=20, tol=1e-15)
    a, b = refine(L, a0, b0, NT, MT, 3, verbose=True)
    np.savez(os.environ.get('LAM_TORI_DIR', '/tmp/lamw/tori') + '/t_%d_%d_%d_%d.npz' % (NT, MT, n, k), a=np.array([str(v) for v in a]),
             b=np.array([str(v) for v in b]), x=str(x), lam=str(L))
    print(k, float(x), 'done', flush=True)
