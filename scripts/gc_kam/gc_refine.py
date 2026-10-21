"""UNTRUSTED: high-precision refinement of the guiding-centre torus (gc_torus.py) and estimate of the
weighted l1 norm of its flow-form residual on the strip r_A = 0.1257 (the e0 of the KAM theorem).
Arithmetic: gmpy2 mpfr object arrays (precision PREC bits).  Usage: python gc_refine.py num den [steps]"""
import sys, os, time, json
import numpy as np, sympy as sp, gmpy2
from gmpy2 import mpfr
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')
from flow_torus import index_sets
from gc_torus import GalerkinGC, D, nR, nZ, q, KD, KR, KZ, u, z, c, s
PREC = 200
gmpy2.get_context().precision = PREC
num, den = int(sys.argv[1]), int(sys.argv[2]); steps = int(sys.argv[3]) if len(sys.argv) > 3 else 2
RHO = mpfr(num) / den
PI = gmpy2.const_pi()
IOTA = (75 + gmpy2.sqrt(mpfr(5))) / 562
d = np.load('/tmp/k2work/gc_torus_%d_%d.npz' % (num, den))
a0, b0, N, M = d['a'], d['b'], int(d['N']), int(d['M'])
Is, Iz = index_sets(N, M)
lam = sp.lambdify((u, z, c, s), [D, nR, nZ, q, KD, KR, KZ], modules=[{}])

def trig_tables(Nt, Np):
    th = [2 * PI * i / Nt for i in range(Nt)]; ps = [2 * PI * j / Np for j in range(Np)]
    return th, ps

def eval_series(a, b, Nt, Np):
    """R, z and derivatives on the grid via separable sums (exact in mpfr)."""
    th, ps = trig_tables(Nt, Np)
    K = N; Mx = M
    # cos/sin tables
    ct = np.array([[gmpy2.cos(k * t) for t in th] for k in range(K + 1)], dtype=object)
    st = np.array([[gmpy2.sin(k * t) for t in th] for k in range(K + 1)], dtype=object)
    cp = np.array([[gmpy2.cos(m * p) for p in ps] for m in range(-Mx, Mx + 1)], dtype=object)
    sp_ = np.array([[gmpy2.sin(m * p) for p in ps] for m in range(-Mx, Mx + 1)], dtype=object)
    zero = mpfr(0)
    R = np.full((Nt, Np), zero, dtype=object); Rth = R.copy(); Rps = R.copy()
    Z = R.copy(); Zth = R.copy(); Zps = R.copy()
    for (k, m), x in zip(Is, a):
        x = mpfr(x) if not isinstance(x, type(zero)) else x
        C = np.outer(ct[k], cp[m + Mx]) - np.outer(st[k], sp_[m + Mx])   # cos(k th + m ps)
        S_ = np.outer(st[k], cp[m + Mx]) + np.outer(ct[k], sp_[m + Mx])  # sin
        R += x * C; Rth += (-k * x) * S_; Rps += (-m * x) * S_
    for (k, m), x in zip(Iz, b):
        x = mpfr(x) if not isinstance(x, type(zero)) else x
        C = np.outer(ct[k], cp[m + Mx]) - np.outer(st[k], sp_[m + Mx])
        S_ = np.outer(st[k], cp[m + Mx]) + np.outer(ct[k], sp_[m + Mx])
        Z += x * S_; Zth += (k * x) * C; Zps += (m * x) * C
    PS = np.array([ps] * Nt, dtype=object)
    cc = np.vectorize(lambda p: -gmpy2.sin(p), otypes=[object])(PS)
    ss = np.vectorize(lambda p: gmpy2.cos(p), otypes=[object])(PS)
    return R, Z, Rth, Rps, Zth, Zps, cc, ss, th, ps

def residual(a, b, Nt, Np):
    R, Z, Rth, Rps, Zth, Zps, cc, ss, th, ps = eval_series(a, b, Nt, Np)
    U = R - 1
    Dv, nRv, nZv, qv, kd, kr, kz = lam(U, Z, cc, ss)
    W3 = np.vectorize(lambda t: 1 / (t * gmpy2.sqrt(t)), otypes=[object])(qv)
    Dt = Dv + RHO / 2 * W3 * kd; nRt = nRv + RHO / 2 * W3 * kr; nZt = nZv + RHO / 2 * W3 * kz
    LR = 2 * Rps + IOTA * Rth; LZ = 2 * Zps + IOTA * Zth
    return Dt * LR - nRt, Dt * LZ - nZt, th, ps

def project(r1, r2, th, ps, Nt, Np):
    """Galerkin projection: sine coefficients of r1 on Iz, cosine coefficients of r2 on Is."""
    npts = Nt * Np
    out1 = []; out2 = []
    # separable: first sum over psi
    Mx = M
    cpj = {m: np.array([gmpy2.cos(m * p) for p in ps], dtype=object) for m in range(-Mx, Mx + 1)}
    spj = {m: np.array([gmpy2.sin(m * p) for p in ps], dtype=object) for m in range(-Mx, Mx + 1)}
    cti = {k: np.array([gmpy2.cos(k * t) for t in th], dtype=object) for k in range(N + 1)}
    sti = {k: np.array([gmpy2.sin(k * t) for t in th], dtype=object) for k in range(N + 1)}
    A1c = {m: r1.dot(cpj[m]) for m in cpj}; A1s = {m: r1.dot(spj[m]) for m in spj}
    A2c = {m: r2.dot(cpj[m]) for m in cpj}; A2s = {m: r2.dot(spj[m]) for m in spj}
    for (k, m) in Iz:   # <r1, sin(k th + m ps)> = sum sin(k th) cos(m ps) + cos(k th) sin(m ps)
        v = sti[k].dot(A1c[m]) + cti[k].dot(A1s[m])
        out1.append(2 * v / npts)
    for (k, m) in Is:
        v = cti[k].dot(A2c[m]) - sti[k].dot(A2s[m])
        w = 1 if (k, m) == (0, 0) else 2
        out2.append(w * v / npts)
    return np.array(out1 + out2, dtype=object)

if __name__ == '__main__':
    t0 = time.time()
    a = np.array([mpfr(float(x)) for x in a0], dtype=object); b = np.array([mpfr(float(x)) for x in b0], dtype=object)
    Nt, Np = 4 * N + 8, 4 * M + 8
    gD = GalerkinGC(N, M, float(IOTA), float(RHO), Nt, Np)
    J = gD.J(np.array([float(x) for x in a]), np.array([float(x) for x in b]))
    Jinv = np.linalg.inv(J)
    na = len(a)
    for it in range(steps):
        r1, r2, th, ps = residual(a, b, Nt, Np)
        F = project(r1, r2, th, ps, Nt, Np)
        e = max(abs(float(x)) for x in F)
        print('refine %d: |F| = %.3e (%.0fs)' % (it, e, time.time() - t0), flush=True)
        dlt = Jinv.astype(object).dot(-F) if False else None
        # mixed precision: d = J^{-1}(-F) with F rounded (relative), scale to keep digits
        scale = mpfr(max(abs(x) for x in F))
        Fs = np.array([float(x / scale) for x in F])
        dd = np.linalg.solve(J, -Fs)
        a = a + np.array([mpfr(float(x)) * scale for x in dd[:na]], dtype=object)
        b = b + np.array([mpfr(float(x)) * scale for x in dd[na:]], dtype=object)
    r1, r2, th, ps = residual(a, b, Nt, Np)
    F = project(r1, r2, th, ps, Nt, Np)
    print('final Galerkin |F| = %.3e (%.0fs)' % (max(abs(float(x)) for x in F), time.time() - t0), flush=True)
    # full residual on a finer grid -> weighted l1 norm on the strip (FFT in float of scaled residual)
    Nt2, Np2 = 2 * Nt, 2 * Np
    r1, r2, th, ps = residual(a, b, Nt2, Np2)
    out = {}
    for name, r in [('R', r1), ('Z', r2)]:
        sc = max(abs(x) for x in r.ravel())
        arr = np.array([[float(x / sc) for x in row] for row in r])
        Fq = np.fft.fft2(arr) / arr.size
        kk = np.fft.fftfreq(Nt2, 1 / Nt2); mm = np.fft.fftfreq(Np2, 1 / Np2)
        KK, MM = np.meshgrid(kk, mm, indexing='ij')
        l1 = float(np.sum(np.abs(Fq) * np.exp(0.1257 * (np.abs(KK) + np.abs(MM))))) * float(sc)
        out['l1_' + name] = l1; out['sup_' + name] = float(sc)
        print('%s: sup %.3e  weighted l1 (r=0.1257) %.3e' % (name, float(sc), l1), flush=True)
    json.dump(out, open('/tmp/k2work/gc_refine_%d_%d.json' % (num, den), 'w'), indent=1)
    np.savez('/tmp/k2work/gc_torus_hp_%d_%d.npz' % (num, den), a=np.array([str(x) for x in a]),
             b=np.array([str(x) for x in b]), N=N, M=M)
    print('done %.0fs' % (time.time() - t0))
