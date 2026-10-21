"""UNTRUSTED oracle: invariant torus with iota = iota_A of the guiding-centre field
B~ = field(1/4) + rho curl b, in the flow form of Design/RationalStellaratorGCFlow.lean:

    D~ (d_phi R + iota d_theta R) - n~_R = 0,   D~ (d_phi z + iota d_theta z) - n~_z = 0,

with D~ = D + (rho/2) W^3 R^2 (R nZ q_u - 8 nZ q - R nR q_z), etc., W = q^(-1/2), q = nR^2 + R^2 D^2 + nZ^2.
Galerkin-Newton in double precision (stellarator-symmetric ansatz as scripts/kam_oracle/flow_torus.py),
continuation in rho from torus A (rho = 0).  Usage:  python gc_torus.py <rho_num> <rho_den> [steps]
"""
import sys, os, time, json
import numpy as np
import sympy as sp
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')
from flow_torus import index_sets, resize
from gcmodel import BASE, u, z, c, s

IOTA = (75 + 5 ** 0.5) / 562
R_ = 1 + u
D, nR, nZ = BASE['Dp'], BASE['nRp'], BASE['nZp']
q = sp.expand(nR ** 2 + R_ ** 2 * D ** 2 + nZ ** 2)
def phiP(e): return sp.expand(sp.diff(e, c) * (-2 * s) + sp.diff(e, s) * (2 * c))
qu, qz, qph = sp.diff(q, u), sp.diff(q, z), phiP(q)
KD = R_ ** 2 * (R_ * nZ * qu - 8 * nZ * q - R_ * nR * qz)
KR = R_ ** 5 * D * qz - R_ ** 3 * nZ * qph
KZ = R_ ** 3 * nR * qph - R_ ** 5 * D * qu + 8 * R_ ** 4 * D * q
lam = sp.lambdify((u, z, c, s), [D, nR, nZ, q, KD, KR, KZ], 'numpy')

def gcparts(uu, zz, cc, ss, rho):
    Dv, nRv, nZv, qv, kd, kr, kz = lam(uu, zz, cc, ss)
    W3 = qv ** (-1.5)
    return Dv + rho / 2 * W3 * kd, nRv + rho / 2 * W3 * kr, nZv + rho / 2 * W3 * kz

class GalerkinGC:
    def __init__(self, N, M, iota, rho, Nt=None, Np=None):
        self.N, self.M, self.iota, self.rho = N, M, iota, rho
        self.Is, self.Iz = index_sets(N, M)
        Nt = Nt or 4 * N + 8; Np = Np or 4 * M + 8
        th = 2 * np.pi * np.arange(Nt) / Nt; ps = 2 * np.pi * np.arange(Np) / Np
        T, P = np.meshgrid(th, ps, indexing='ij'); T, P = T.ravel(), P.ravel()
        # c = cos 2phi = -sin psi, s = sin 2phi = cos psi
        self.cc, self.ss = -np.sin(P), np.cos(P)
        ks = np.array([k for k, m in self.Is]); ms = np.array([m for k, m in self.Is])
        kz = np.array([k for k, m in self.Iz]); mz = np.array([m for k, m in self.Iz])
        A = np.outer(T, ks) + np.outer(P, ms); Az = np.outer(T, kz) + np.outer(P, mz)
        self.Cs, self.Ss, self.Cz, self.Sz = np.cos(A), np.sin(A), np.cos(Az), np.sin(Az)
        self.ks, self.ms, self.kz, self.mz = ks, ms, kz, mz
        npts = T.size
        ws = np.where((ks == 0) & (ms == 0), 1.0, 2.0) / npts
        self.Ps_cos = (self.Cs * ws).T; self.Pz_sin = (self.Sz * (2.0 / npts)).T
    def fields(self, a, b):
        R = self.Cs @ a; zz = self.Sz @ b
        Rth = self.Ss @ (-self.ks * a); Rps = self.Ss @ (-self.ms * a)
        zth = self.Cz @ (self.kz * b); zps = self.Cz @ (self.mz * b)
        return R, zz, Rth, Rps, zth, zps
    def res(self, R, zz, LR, Lz):
        Dt, nRt, nZt = gcparts(R - 1, zz, self.cc, self.ss, self.rho)
        return Dt * LR - nRt, Dt * Lz - nZt
    def F(self, a, b):
        R, zz, Rth, Rps, zth, zps = self.fields(a, b)
        r1, r2 = self.res(R, zz, 2 * Rps + self.iota * Rth, 2 * zps + self.iota * zth)
        return np.concatenate([self.Pz_sin @ r1, self.Ps_cos @ r2])
    def J(self, a, b):
        R, zz, Rth, Rps, zth, zps = self.fields(a, b)
        LR = 2 * Rps + self.iota * Rth; Lz = 2 * zps + self.iota * zth
        h = 1e-30
        D0, _, _ = gcparts(R - 1, zz, self.cc, self.ss, self.rho)
        Dc, nRc, nZc = gcparts(R - 1 + 1j * h, zz, self.cc, self.ss, self.rho)
        D_R, nR_R, nZ_R = Dc.imag / h, nRc.imag / h, nZc.imag / h
        Dc, nRc, nZc = gcparts(R - 1, zz + 1j * h, self.cc, self.ss, self.rho)
        D_z, nR_z, nZ_z = Dc.imag / h, nRc.imag / h, nZc.imag / h
        dLs = self.Ss * (-(2 * self.ms + self.iota * self.ks)); dLz = self.Cz * (2 * self.mz + self.iota * self.kz)
        r1a = D0[:, None] * dLs + ((D_R * LR - nR_R)[:, None]) * self.Cs
        r1b = ((D_z * LR - nR_z)[:, None]) * self.Sz
        r2a = ((D_R * Lz - nZ_R)[:, None]) * self.Cs
        r2b = D0[:, None] * dLz + ((D_z * Lz - nZ_z)[:, None]) * self.Sz
        return np.block([[self.Pz_sin @ r1a, self.Pz_sin @ r1b], [self.Ps_cos @ r2a, self.Ps_cos @ r2b]])

def newton(g, a, b, steps=12, tol=1e-14, verbose=False):
    na = len(a)
    for it in range(steps):
        Fv = g.F(a, b); e = abs(Fv).max()
        if verbose: print('   newton', it, '%.2e' % e, flush=True)
        if e < tol: break
        d = np.linalg.lstsq(g.J(a, b), -Fv, rcond=None)[0]
        a, b = a + d[:na], b + d[na:]
    return a, b, abs(g.F(a, b)).max()

def grid_residual(a, b, N, M, iota, rho, Nt=256, Np=192):
    g = GalerkinGC(N, M, iota, rho, Nt, Np)
    R, zz, Rth, Rps, zth, zps = g.fields(a, b)
    r1, r2 = g.res(R, zz, 2 * Rps + iota * Rth, 2 * zps + iota * zth)
    return abs(r1).max(), abs(r2).max(), R, zz

def strip_norm(a, b, N, M, rho_s):
    """weighted l1 norms of u = R - 1 and z on the strip rho_s (|k| + |m| weights, as Bd in Lean)."""
    Is, Iz = index_sets(N, M)
    nu = 0.0; nz = 0.0
    for (k, m), x in zip(Is, a):
        w = np.exp(rho_s * (abs(k) + abs(m)))
        val = x - (1.0 if (k, m) == (0, 0) else 0.0)
        nu += abs(val) * (1 if (k, m) == (0, 0) else 1) * w   # cos -> two modes of half amplitude
    for (k, m), x in zip(Iz, b):
        nz += abs(x) * np.exp(rho_s * (abs(k) + abs(m)))
    return nu, nz

if __name__ == '__main__':
    num, den = int(sys.argv[1]), int(sys.argv[2])
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    rho_t = num / den
    d = np.load('/tmp/k2work/double_A.npz')
    a, b, N, M = d['a'], d['b'], int(d['N']), int(d['M'])
    N2, M2 = 24, 14
    a, b = resize(a, b, N, M, N2, M2); N, M = N2, M2
    t0 = time.time()
    for j in range(1, steps + 1):
        rho = rho_t * j / steps
        g = GalerkinGC(N, M, IOTA, rho)
        a, b, e = newton(g, a, b)
        print('rho = %+.6f  |F| = %.2e  (%.0fs)' % (rho, e, time.time() - t0), flush=True)
    for N2, M2 in [(28, 18), (32, 22)]:
        a, b = resize(a, b, N, M, N2, M2); N, M = N2, M2
        g = GalerkinGC(N, M, IOTA, rho_t)
        a, b, e = newton(g, a, b)
        print('N=%d M=%d |F| = %.2e (%.0fs)' % (N, M, e, time.time() - t0), flush=True)
    r1, r2, R, zz = grid_residual(a, b, N, M, IOTA, rho_t)
    print('grid residual', r1, r2)
    print('R range', R.min(), R.max(), ' z range', zz.min(), zz.max())
    out = {'rho': [num, den], 'N': N, 'M': M, 'res_grid': [r1, r2],
           'R_range': [R.min(), R.max()], 'z_range': [zz.min(), zz.max()]}
    for rs in [0.08, 0.1, 0.1257]:
        nu, nz = strip_norm(a, b, N, M, rs)
        out['strip_%g' % rs] = [nu, nz]
        print('strip %.4f: |u| = %.4f  |z| = %.4f' % (rs, nu, nz))
    np.savez('/tmp/k2work/gc_torus_%d_%d.npz' % (num, den), a=a, b=b, N=N, M=M, rho=rho_t)
    json.dump(out, open('/tmp/k2work/gc_torus_%d_%d.json' % (num, den), 'w'), indent=1)
