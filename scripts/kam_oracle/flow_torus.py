"""UNTRUSTED.  Flow-form invariant torus A of the rational stellarator, solved by Newton in
double precision and refined in exact dyadic (big-integer) arithmetic.

Torus ansatz (stellarator symmetric), theta in radians, psi = 2 phi - pi/2:
    R(theta, phi) = sum_{(k,m) in Is} a_{km} cos(k theta + m psi)        (R = distance to the z-axis)
    z(theta, phi) = sum_{(k,m) in Iz} b_{km} sin(k theta + m psi)
    Is = {(0,m): 0<=m<=M} u {(k,m): 1<=k<=N, |m|<=M},   Iz = Is \\ {(0,0)}.

Invariance equation (flow form, field-line "time" = toroidal angle phi, multiplied by the
polynomial denominator D = s (1 + eps h_phi)):
    RR := D (d_phi R + iota d_theta R) - 2 eps R Ps = 0,
    Rz := D (d_phi z + iota d_theta z) - eps R^2 Pz = 0,
with s = R^2 in D, Ps, Pz (field.py), d_phi = 2 d_psi and iota = iota_A = (75 + sqrt 5)/562.
(Indeed dR/dphi = (ds/dphi)/(2R) = 2 eps R Ps / D and dz/dphi = eps s Pz / D.)
RR is a sine series and Rz a cosine series (stellarator symmetry); Galerkin projection onto
the modes of Iz resp. Is gives a square system.
"""
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from field import DPP, EPS  # noqa: E402


def index_sets(N, M):
    Is = [(0, m) for m in range(0, M + 1)] + [(k, m) for k in range(1, N + 1) for m in range(-M, M + 1)]
    Iz = Is[1:]
    return Is, Iz


class Galerkin:
    def __init__(self, N, M, iota, Nt=None, Np=None):
        self.N, self.M, self.iota = N, M, iota
        self.Is, self.Iz = index_sets(N, M)
        Nt = Nt or 5 * N + 8
        Np = Np or 5 * M + 8
        th = 2 * np.pi * np.arange(Nt) / Nt
        ps = 2 * np.pi * np.arange(Np) / Np
        T, P = np.meshgrid(th, ps, indexing='ij')
        T, P = T.ravel(), P.ravel()
        self.c, self.sn = np.cos(P), np.sin(P)
        ks = np.array([k for k, m in self.Is]); ms = np.array([m for k, m in self.Is])
        kz = np.array([k for k, m in self.Iz]); mz = np.array([m for k, m in self.Iz])
        A = np.outer(T, ks) + np.outer(P, ms)
        Az = np.outer(T, kz) + np.outer(P, mz)
        self.Cs, self.Ss = np.cos(A), np.sin(A)          # for s
        self.Cz, self.Sz = np.cos(Az), np.sin(Az)        # for z
        self.ks, self.ms, self.kz, self.mz = ks, ms, kz, mz
        npts = T.size
        ws = np.where((ks == 0) & (ms == 0), 1.0, 2.0) / npts
        self.Ps_cos = (self.Cs * ws).T          # projection of a cosine series onto Is
        self.Pz_sin = (self.Sz * (2.0 / npts)).T  # projection of a sine series onto Iz

    def fields(self, a, b):
        s = self.Cs @ a
        z = self.Sz @ b
        sth = self.Ss @ (-self.ks * a)
        sps = self.Ss @ (-self.ms * a)
        zth = self.Cz @ (self.kz * b)
        zps = self.Cz @ (self.mz * b)
        return s, z, sth, sps, zth, zps

    def residual_grid(self, a, b):
        R, z, Rth, Rps, zth, zps = self.fields(a, b)
        D, Ps, Pz = DPP(R * R, z, self.c, self.sn)
        RR = D * (2 * Rps + self.iota * Rth) - 2 * EPS * R * Ps
        Rz = D * (2 * zps + self.iota * zth) - EPS * R * R * Pz
        return RR, Rz

    def F(self, a, b):
        Rs, Rz = self.residual_grid(a, b)
        return np.concatenate([self.Pz_sin @ Rs, self.Ps_cos @ Rz])

    def J(self, a, b):
        R, z, sth, sps, zth, zps = self.fields(a, b)
        s = R * R
        h = 1e-30
        D, Ps, Pz = DPP(s, z, self.c, self.sn)
        Dc, Psc, Pzc = DPP((R + 1j * h) ** 2, z, self.c, self.sn)
        D_s, Ps_s, Pz_s = Dc.imag / h, Psc.imag / h, Pzc.imag / h     # derivatives in R
        Dc, Psc, Pzc = DPP(s, z + 1j * h, self.c, self.sn)
        D_z, Ps_z, Pz_z = Dc.imag / h, Psc.imag / h, Pzc.imag / h
        Ls = 2 * sps + self.iota * sth
        Lz = 2 * zps + self.iota * zth
        # d/da: ds = Cs, d(Ls) = Ss * (-(2m + iota k))
        dLs = self.Ss * (-(2 * self.ms + self.iota * self.ks))
        dLz = self.Cz * (2 * self.mz + self.iota * self.kz)
        Rs_a = D[:, None] * dLs + (D_s * Ls)[:, None] * self.Cs - 2 * EPS * ((Ps + R * Ps_s)[:, None] * self.Cs)
        Rs_b = (D_z * Ls)[:, None] * self.Sz - 2 * EPS * ((R * Ps_z)[:, None] * self.Sz)
        Rz_a = (D_s * Lz)[:, None] * self.Cs - EPS * ((2 * R * Pz + s * Pz_s)[:, None] * self.Cs)
        Rz_b = D[:, None] * dLz + (D_z * Lz)[:, None] * self.Sz - EPS * ((s * Pz_z)[:, None] * self.Sz)
        return np.block([[self.Pz_sin @ Rs_a, self.Pz_sin @ Rs_b], [self.Ps_cos @ Rz_a, self.Ps_cos @ Rz_b]])


def from_fft(FS, FZ, N, M):
    """Coefficients (a, b) of the ansatz from 2-D FFT arrays (index [k_theta, m_psi])."""
    Is, Iz = index_sets(N, M)
    a = np.array([(1 if (k, m) == (0, 0) else 2) * FS[k, m].real for k, m in Is])
    b = np.array([-2 * FZ[k, m].imag for k, m in Iz])
    return a, b


def resize(a, b, N0, M0, N, M):
    Is0, Iz0 = index_sets(N0, M0)
    Is, Iz = index_sets(N, M)
    da = dict(zip(Is0, a)); db = dict(zip(Iz0, b))
    return np.array([da.get(i, 0.0) for i in Is]), np.array([db.get(i, 0.0) for i in Iz])


def newton_double(g, a, b, steps=8, verbose=True):
    na = len(a)
    for it in range(steps):
        Fv = g.F(a, b)
        if verbose:
            print(f"  double Newton {it}: |F|_inf = {abs(Fv).max():.3e}", flush=True)
        if abs(Fv).max() < 1e-15:
            break
        d = np.linalg.solve(g.J(a, b), -Fv)
        a, b = a + d[:na], b + d[na:]
    return a, b


if __name__ == '__main__':
    d = np.load('/tmp/k2work/init_A.npz')
    FS, FZ, iota = d['FS'], d['FZ'], float(d['iota'])
    # init_guess stores the FFT of s = R^2; convert to R
    FS = np.fft.fft2(np.sqrt(np.real(np.fft.ifft2(FS * FS.size)))) / FS.size
    print("symmetry check of initial guess: max|Im FS| =", abs(FS.imag).max(), " max|Re FZ| =", abs(FZ.real).max())
    N, M = 16, 10
    a, b = from_fft(FS, FZ, N, M)
    g = Galerkin(N, M, iota)
    t = time.time()
    a, b = newton_double(g, a, b)
    print(f"N={N} M={M}: done {time.time()-t:.1f}s")
    for N2, M2 in [(24, 14), (28, 18)]:
        a, b = resize(a, b, N, M, N2, M2)
        N, M = N2, M2
        g = Galerkin(N, M, iota)
        t = time.time()
        a, b = newton_double(g, a, b)
        print(f"N={N} M={M}: done {time.time()-t:.1f}s")
    np.savez('/tmp/k2work/double_A.npz', a=a, b=b, N=N, M=M, iota=iota)
