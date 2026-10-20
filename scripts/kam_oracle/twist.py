"""UNTRUSTED.  Twist of torus A (double precision, from the refined dyadic torus; R-form ansatz).

1. ELP-S (JEMS 2025, Def. 6.1) twist constant, with the time reparametrisation of
   notes/theory/kam-route.md section 4 (same recipe as /tmp/laneA7/scripts/twist.py):
   angles normalised to [0,1)^2 (theta/2pi, phi/pi), field-line time.
2. Shear: d iota / d Phi, where Phi is the toroidal flux through the section phi = pi/4
   enclosed by the torus, from neighbouring Galerkin tori at iota_A +- delta.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from flow_torus import Galerkin, index_sets, newton_double  # noqa: E402

EPS = 0.25


def field_cart(x, y, z):
    """B = grad phi + eps grad h in Cartesian coordinates and its Jacobian (finite differences
    of the exact formula would be too crude; use complex-step on each coordinate)."""
    def B(x, y, z):
        r2 = x * x + y * y
        f = ((r2 - 1) ** 2 - 4 * z ** 2) / (4 * r2)
        g = -z * ((r2 - 1) * (r2 - 5) - 4 * z ** 2) / (4 * r2)
        C2 = (x * x - y * y) / r2
        S2 = 2 * x * y / r2
        return f * C2 + g * S2
    h = 1e-30
    hx = (B(x + 1j * h, y, z)).imag / h
    hy = (B(x, y + 1j * h, z)).imag / h
    hz = (B(x, y, z + 1j * h)).imag / h
    r2 = x * x + y * y
    return np.array([-y / r2 + EPS * hx, x / r2 + EPS * hy, EPS * hz])


def jac_cart(x, y, z, d=1e-6):
    cols = []
    for e in np.eye(3):
        Bp = field_cart(x + d * e[0], y + d * e[1], z + d * e[2])
        Bm = field_cart(x - d * e[0], y - d * e[1], z - d * e[2])
        cols.append((Bp - Bm) / (2 * d))
    return np.stack(cols, axis=1)   # [i, j] = dB_i/dx_j


def grid_eval(a, b, N, M, Nt=96, Nphi=64):
    Is, Iz = index_sets(N, M)
    th = 2 * np.pi * np.arange(Nt)[:, None] / Nt * np.ones((1, Nphi))
    ph = np.pi / 4 + np.pi * np.arange(Nphi)[None, :] / Nphi * np.ones((Nt, 1))
    ps = 2 * ph - np.pi / 2
    R = np.zeros_like(th); z = np.zeros_like(th)
    Rt = np.zeros_like(th); Rp = np.zeros_like(th); zt = np.zeros_like(th); zp = np.zeros_like(th)
    for (k, m), c in zip(Is, a):
        ang = k * th + m * ps
        R += c * np.cos(ang); Rt -= k * c * np.sin(ang); Rp -= 2 * m * c * np.sin(ang)
    for (k, m), c in zip(Iz, b):
        ang = k * th + m * ps
        z += c * np.sin(ang); zt += k * c * np.cos(ang); zp += 2 * m * c * np.cos(ang)
    return th, ph, R, z, Rt, Rp, zt, zp   # Rp, zp are d/dphi


def elps_twist(a, b, N, M, iota, Nt=96, Nphi=64):
    th, ph, R, z, Rt, Rphi, zt, zphi = grid_eval(a, b, N, M, Nt, Nphi)
    omega = iota / 2
    K1 = 2 * np.pi * np.array([Rt * np.cos(ph), Rt * np.sin(ph), zt])                  # d/d vartheta1
    K2 = np.pi * np.array([Rphi * np.cos(ph) - R * np.sin(ph), Rphi * np.sin(ph) + R * np.cos(ph), zphi])
    X, Y, Z = R * np.cos(ph), R * np.sin(ph), z
    Bv = field_cart(X, Y, Z)
    bphi = (X * Bv[1] - Y * Bv[0]) / (X ** 2 + Y ** 2)
    flowdir = (omega / np.pi) * K1 + K2 / np.pi
    inv = np.abs(Bv - bphi * flowdir).max()
    kt = np.fft.fftfreq(Nt, 1 / Nt)[:, None]; kp = np.fft.fftfreq(Nphi, 1 / Nphi)[None, :]

    def D(F, a1, b1):
        return np.real(np.fft.ifft2(np.fft.fft2(F) * (2j * np.pi * kt) ** a1 * (2j * np.pi * kp) ** b1))
    cc = 1 / np.mean(1 / bphi)
    rhsu = 1 - cc / bphi
    sym = (2j * np.pi * kt) * omega / np.pi + (2j * np.pi * kp) / np.pi
    sym[0, 0] = 1
    U = np.fft.fft2(rhsu) / sym; U[0, 0] = 0
    u = np.real(np.fft.ifft2(U))
    u1 = D(u, 1, 0); u2 = D(u, 0, 1)
    v = np.array([omega / np.pi, 1 / np.pi])
    detP = 1 - (v[0] * u1 + v[1] * u2)
    n = np.cross(K1, K2, axis=0); n2 = (n ** 2).sum(0)
    DB = jac_cart(X, Y, Z)
    S = DB + DB.transpose(1, 0, 2, 3)
    Sn = np.einsum('ijab,jab->iab', S, n)
    G = np.array([[(K1 * K1).sum(0), (K1 * K2).sum(0)], [(K2 * K1).sum(0), (K2 * K2).sum(0)]])
    DKtSn = np.array([(K1 * Sn).sum(0), (K2 * Sn).sum(0)])
    Gi = np.linalg.inv(G.transpose(2, 3, 0, 1)).transpose(2, 3, 0, 1)
    A = -np.einsum('ijab,jab->iab', Gi, DKtSn) / n2
    DPsi = np.array([[1 - v[0] * u1, -v[0] * u2], [-v[1] * u1, 1 - v[1] * u2]])
    Ahat = detP * np.einsum('ijab,jab->iab', DPsi, A)
    Aavg = (Ahat * detP).mean(axis=(1, 2))
    ws = cc * v
    T = Aavg[0] * ws[1] - Aavg[1] * ws[0]
    return T, T / np.hypot(*ws), inv


def flux(a, b, N, M, Nt=512, nq=24):
    """Toroidal flux through phi = pi/4 enclosed by the torus: Phi = oint G dz,
    G(R,z) = int_1^R (B^phi R) dR' ... with B . e_phi area density w = (1 + eps h_phi)/R."""
    Is, Iz = index_sets(N, M)
    th = 2 * np.pi * np.arange(Nt) / Nt
    R = sum(c * np.cos(k * th) for (k, m), c in zip(Is, a))      # psi = 0 at phi = pi/4
    z = sum(c * np.sin(k * th) for (k, m), c in zip(Iz, b))
    zt = sum(k * c * np.cos(k * th) for (k, m), c in zip(Iz, b))
    xg, wg = np.polynomial.legendre.leggauss(nq)

    def w(Rv, zv):
        sv = Rv * Rv
        sf = ((sv - 1) ** 2 - 4 * zv ** 2) / 4
        sg = -zv * ((sv - 1) * (sv - 5) - 4 * zv ** 2) / 4
        # at phi = pi/4: psi = 0, cos2phi = 0, sin2phi = 1; h_phi = -2 f sin2phi + 2 g cos2phi = -2f
        hphi = -2 * sf / sv
        return (1 + EPS * hphi) / Rv
    G = np.zeros(Nt)
    for i in range(Nt):
        Rq = 1 + (R[i] - 1) * (xg + 1) / 2
        G[i] = (R[i] - 1) / 2 * np.sum(wg * w(Rq, z[i]))
    return np.mean(G * zt) * 2 * np.pi


if __name__ == '__main__':
    from mpmath import sqrt as msqrt
    iota = float((75 + msqrt(5)) / 562)
    d = np.load('/tmp/k2work/torusA_P90_N32_M22.npz')
    N, M, P = int(d['N']), int(d['M']), int(d['P'])
    a = np.array([int(x) for x in d['A']], dtype=float) / 2.0 ** P
    b = np.array([int(x) for x in d['B']], dtype=float) / 2.0 ** P
    T, Trel, inv = elps_twist(a, b, N, M, iota)
    print(f"ELP-S twist T = {T:.4e} (relative T/|omega_s| = {Trel:.3e}); invariance check {inv:.1e}")
    Phi0 = flux(a, b, N, M)
    res = []
    for dl in (-2e-4, 2e-4):
        g = Galerkin(N, M, iota + dl)
        a1, b1 = newton_double(g, a.copy(), b.copy(), verbose=False)
        res.append((iota + dl, flux(a1, b1, N, M), a1[0]))
    dio_dPhi = (res[1][0] - res[0][0]) / (res[1][1] - res[0][1])
    print(f"toroidal flux Phi_A = {Phi0:.6e}; shear d iota/d Phi = {dio_dPhi:.4e}; "
          f"d iota/d(r_eff) with Phi = pi r_eff^2: {dio_dPhi * 2 * np.sqrt(np.pi * Phi0):.4e}")
