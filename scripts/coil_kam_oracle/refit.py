"""UNTRUSTED.  Galerkin-Newton refit of the iota_A torus to the coil field B_c (pilot).

Variables: theta (poloidal) and the geometric toroidal angle phi itself (full period 2 pi: the TF
return legs at x = Lambda break both the 2-fold rotation and the stellarator symmetry sigma at
O(1/Lambda) = 1e-6, so no symmetry is imposed).  `chi` below denotes phi.

Ansatz on the half-plane H = {(0, m): m >= 0} u {(k, m): k >= 1}:
    R = sum_H a_km cos(k theta + m chi) + a'_km sin(k theta + m chi),
    z = sum_H b_km cos(k theta + m chi) + b'_km sin(k theta + m chi)
(the sine coefficients of (0, 0) are absent).  The phase freedom theta -> theta + c is fixed by
a'_{1,0} = 0 (the coefficient of sin(theta) in R).

Flow form (no division; D = B_phi, n = R (B_R, B_z), L = d_chi + iota d_theta):
    E_R = B_phi(K) L R - R B_R(K),     E_z = B_phi(K) L z - R B_z(K).
Galerkin projection onto the cos/sin modes of H (overdetermined by one equation; least squares).

Start: torus A (`/tmp/k2work/double_A.npz`, psi = 2 phi - pi/2, so m_phi = 2 m_psi, with phases).
Output: /tmp/ckwork/coil_torus_N{N}_M{M}.npz.
"""
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from coil import KAP, PP, QQ, seg_factor  # noqa: E402

IOTA = (75 + np.sqrt(5)) / 562
WORK = '/tmp/ckwork'


def half_plane(N, M):
    return [(0, m) for m in range(0, M + 1)] + [(k, m) for k in range(1, N + 1) for m in range(-M, M + 1)]


def field_and_jac(Y):
    """B and dB/dy_j (complex step) at real points Y (n, 3)."""
    h = 1e-20
    B = np.zeros(Y.shape)
    dB = np.zeros(Y.shape + (3,))
    for kap, p, q in zip(KAP, PP, QQ):
        for j in range(4):
            y = Y.astype(complex)
            if j < 3:
                y[:, j] += 1j * h
            a = p - y
            b = q - y
            al = np.sqrt((a * a).sum(-1))
            be = np.sqrt((b * b).sum(-1))
            ab = (a * b).sum(-1)
            f = seg_factor(kap, a, b, al, be, ab)
            v = f[:, None] * np.cross(a, b)
            if j < 3:
                dB[:, :, j] += v.imag / h
            else:
                B += v.real
    return B, dB


class Galerkin:
    def __init__(self, N, M, Nt=None, Np=None):
        self.N, self.M = N, M
        self.H = half_plane(N, M)
        Nt = Nt or 2 * N + 6 + N // 2
        Np = Np or 2 * M + 6 + M // 2
        self.Nt, self.Np = Nt, Np
        th = 2 * np.pi * np.arange(Nt) / Nt
        ch = 2 * np.pi * np.arange(Np) / Np
        T, C = np.meshgrid(th, ch, indexing='ij')
        self.T, self.C = T.ravel(), C.ravel()
        self.phi = self.C
        ks = np.array([k for k, m in self.H])
        ms = np.array([m for k, m in self.H])
        A = np.outer(self.T, ks) + np.outer(self.C, ms)
        self.Cs, self.Sn = np.cos(A), np.sin(A)
        self.ks, self.ms = ks, ms
        self.lam = ms + IOTA * ks
        npts = self.T.size
        w = np.where((ks == 0) & (ms == 0), 1.0, 2.0) / npts
        self.Pc = (self.Cs * w).T
        self.Ps = (self.Sn * (2.0 / npts)).T
        self.i00 = 0           # index of (0,0) in H
        self.i10 = self.H.index((1, 0))
        # unknown layout: a (|H|), a' (|H| minus (0,0) and (1,0)), b (|H|), b' (|H| minus (0,0))
        nH = len(self.H)
        self.maskAp = np.ones(nH, bool); self.maskAp[[self.i00, self.i10]] = False
        self.maskBp = np.ones(nH, bool); self.maskBp[self.i00] = False

    def unpack(self, x):
        nH = len(self.H)
        o = 0
        a = x[o:o + nH]; o += nH
        ap = np.zeros(nH); n = self.maskAp.sum(); ap[self.maskAp] = x[o:o + n]; o += n
        b = x[o:o + nH]; o += nH
        bp = np.zeros(nH); n = self.maskBp.sum(); bp[self.maskBp] = x[o:o + n]; o += n
        return a, ap, b, bp

    def pack(self, a, ap, b, bp):
        return np.concatenate([a, ap[self.maskAp], b, bp[self.maskBp]])

    def torus(self, x):
        a, ap, b, bp = self.unpack(x)
        R = self.Cs @ a + self.Sn @ ap
        Z = self.Cs @ b + self.Sn @ bp
        LR = self.Sn @ (-self.lam * a) + self.Cs @ (self.lam * ap)
        LZ = self.Sn @ (-self.lam * b) + self.Cs @ (self.lam * bp)
        return R, Z, LR, LZ

    def residual(self, x, jac=False):
        R, Z, LR, LZ = self.torus(x)
        cp, sp = np.cos(self.phi), np.sin(self.phi)
        Y = np.stack([R * cp, R * sp, Z], -1)
        if jac:
            B, dB = field_and_jac(Y)
        else:
            from coil import field
            B = field(Y)
        Bphi = -sp * B[:, 0] + cp * B[:, 1]
        BR = cp * B[:, 0] + sp * B[:, 1]
        ER = Bphi * LR - R * BR
        EZ = Bphi * LZ - R * B[:, 2]
        if not jac:
            return ER, EZ
        # derivatives w.r.t. R and Z (y = (R cos, R sin, Z))
        dBdR = dB[:, :, 0] * cp[:, None] + dB[:, :, 1] * sp[:, None]
        dBdZ = dB[:, :, 2]
        dBphi_R = -sp * dBdR[:, 0] + cp * dBdR[:, 1]
        dBphi_Z = -sp * dBdZ[:, 0] + cp * dBdZ[:, 1]
        dBR_R = cp * dBdR[:, 0] + sp * dBdR[:, 1]
        dBR_Z = cp * dBdZ[:, 0] + sp * dBdZ[:, 1]
        ER_R = dBphi_R * LR - BR - R * dBR_R
        ER_Z = dBphi_Z * LR - R * dBR_Z
        EZ_R = dBphi_R * LZ - B[:, 2] - R * dBdR[:, 2]
        EZ_Z = dBphi_Z * LZ - R * dBdZ[:, 2]
        return ER, EZ, Bphi, ER_R, ER_Z, EZ_R, EZ_Z

    def proj(self, E):
        return np.concatenate([self.Pc @ E, self.Ps @ E])

    def F(self, x):
        ER, EZ = self.residual(x)
        return np.concatenate([self.proj(ER), self.proj(EZ)])

    def J(self, x):
        ER, EZ, Bphi, ER_R, ER_Z, EZ_R, EZ_Z = self.residual(x, jac=True)
        Cs, Sn, lam = self.Cs, self.Sn, self.lam
        dLa = Sn * (-lam)          # d(LR)/da
        dLap = Cs * lam            # d(LR)/da'
        # columns: a, a', b, b'
        cols_R = [Cs, Sn[:, self.maskAp]]
        cols_Z = [Cs, Sn[:, self.maskBp]]
        cols_LR = [dLa, dLap[:, self.maskAp]]
        cols_LZ = [dLa, dLap[:, self.maskBp]]
        JR = np.hstack([ER_R[:, None] * cols_R[0] + Bphi[:, None] * cols_LR[0],
                        ER_R[:, None] * cols_R[1] + Bphi[:, None] * cols_LR[1],
                        ER_Z[:, None] * cols_Z[0], ER_Z[:, None] * cols_Z[1]])
        JZ = np.hstack([EZ_R[:, None] * cols_R[0], EZ_R[:, None] * cols_R[1],
                        EZ_Z[:, None] * cols_Z[0] + Bphi[:, None] * cols_LZ[0],
                        EZ_Z[:, None] * cols_Z[1] + Bphi[:, None] * cols_LZ[1]])
        return np.vstack([np.vstack([self.Pc @ JR, self.Ps @ JR]), np.vstack([self.Pc @ JZ, self.Ps @ JZ])])


def from_torusA(g):
    d = np.load('/tmp/k2work/double_A.npz')
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'kam_oracle'))
    from flow_torus import index_sets
    Is, Iz = index_sets(int(d['N']), int(d['M']))
    nH = len(g.H)
    idx = {km: i for i, km in enumerate(g.H)}
    a = np.zeros(nH); b = np.zeros(nH); ap = np.zeros(nH); bp = np.zeros(nH)
    # cos(k th + m psi) = cos(x - m pi/2), x = k th + 2 m phi
    cs = {0: (1, 0), 1: (0, 1), 2: (-1, 0), 3: (0, -1)}
    for (k, m), c in zip(Is, d['a']):
        if (k, 2 * m) in idx:
            cm, sm = cs[m % 4]
            a[idx[(k, 2 * m)]] += c * cm
            ap[idx[(k, 2 * m)]] += c * sm
    for (k, m), c in zip(Iz, d['b']):
        if (k, 2 * m) in idx:
            cm, sm = cs[m % 4]
            bp[idx[(k, 2 * m)]] += c * cm
            b[idx[(k, 2 * m)]] -= c * sm
    return g.pack(a, ap, b, bp)


def regrid(x, g0, g):
    a0, ap0, b0, bp0 = g0.unpack(x)
    d0 = {km: i for i, km in enumerate(g0.H)}
    out = []
    for arr in (a0, ap0, b0, bp0):
        out.append(np.array([arr[d0[km]] if km in d0 else 0.0 for km in g.H]))
    return g.pack(*out)


def newton(g, x, steps=10, tol=1e-14):
    for it in range(steps):
        t = time.time()
        Fv = g.F(x)
        print(f"  N={g.N} M={g.M} it {it}: |F|_inf = {abs(Fv).max():.3e}", flush=True)
        if abs(Fv).max() < tol:
            break
        Jm = g.J(x)
        dx = np.linalg.lstsq(Jm, -Fv, rcond=None)[0]
        x = x + dx
        print(f"     step |dx| = {abs(dx).max():.3e} ({time.time() - t:.1f}s)", flush=True)
    return x


def grid_residual(g, x, Nt, Np):
    """Residual on an independent finer grid (sup norm) and its 2-D Fourier coefficients."""
    h = Galerkin(g.N, g.M, Nt=Nt, Np=Np)
    ER, EZ = h.residual(x)
    ER = ER.reshape(Nt, Np); EZ = EZ.reshape(Nt, Np)
    return ER, EZ


if __name__ == '__main__':
    os.makedirs(WORK, exist_ok=True)
    plan = [(12, 24), (16, 40), (20, 56)]
    if len(sys.argv) > 1:
        plan = [tuple(int(v) for v in s.split('x')) for s in sys.argv[1:]]
    g = Galerkin(*plan[0])
    x = from_torusA(g)
    print('initial |F| (torus A in B_c):', abs(g.F(x)).max())
    for i, (N, M) in enumerate(plan):
        if i > 0:
            g0 = g
            g = Galerkin(N, M)
            x = regrid(x, g0, g)
        x = newton(g, x)
        ER, EZ = grid_residual(g, x, 4 * N + 8, 4 * M + 8)
        print(f"N={N} M={M}: sup|E_R| = {abs(ER).max():.3e}, sup|E_z| = {abs(EZ).max():.3e}")
        a, ap, b, bp = g.unpack(x)
        np.savez(f'{WORK}/coil_torus_N{N}_M{M}.npz', H=np.array(g.H), a=a, ap=ap, b=b, bp=bp, N=N, M=M,
                 iota=IOTA)
