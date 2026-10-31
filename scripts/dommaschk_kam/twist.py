"""UNTRUSTED.  Twist of a Dommaschk flow torus (double precision), ported from
scripts/kam_oracle/twist.py (same recipe, notes/theory/kam-route.md §4).

1. ELP-S (JEMS 2025, Def. 6.1) twist constant after the reparametrisation to field-line time:
   angles normalised to [0,1)^2 (theta/2pi, phi/pi; one field period), omega = iota/2.
2. Shear d iota/d Phi, Phi the toroidal flux through the section phi = 0 enclosed by the torus,
   from neighbouring Galerkin tori at iota +- delta.
"""
import numpy as np

from torus import Galerkin, index_sets, newton_double


def field_cart(ev, X, Y, Z):
    R = np.sqrt(X*X + Y*Y)
    ph = np.arctan2(Y, X)
    BR, BP, BZ = ev.B_cyl(R, ph, Z)
    c, s = X/R, Y/R
    return np.array([BR*c - BP*s, BR*s + BP*c, BZ])


def jac_cart(ev, X, Y, Z, d=1e-6):
    cols = []
    for e in np.eye(3):
        Bp = field_cart(ev, X + d*e[0], Y + d*e[1], Z + d*e[2])
        Bm = field_cart(ev, X - d*e[0], Y - d*e[1], Z - d*e[2])
        cols.append((Bp - Bm)/(2*d))
    return np.stack(cols, axis=1)        # [i, j] = dB_i/dx_j


def grid_eval(a, b, N, M, Nt=128, Nphi=96):
    Is, Iz = index_sets(N, M)
    th = 2*np.pi*np.arange(Nt)[:, None]/Nt*np.ones((1, Nphi))
    ph = np.pi*np.arange(Nphi)[None, :]/Nphi*np.ones((Nt, 1))
    ps = 2*ph
    R = np.zeros_like(th); z = np.zeros_like(th)
    Rt = np.zeros_like(th); Rp = np.zeros_like(th); zt = np.zeros_like(th); zp = np.zeros_like(th)
    for (k, m), c in zip(Is, a):
        ang = k*th + m*ps
        R += c*np.cos(ang); Rt -= k*c*np.sin(ang); Rp -= 2*m*c*np.sin(ang)
    for (k, m), c in zip(Iz, b):
        ang = k*th + m*ps
        z += c*np.sin(ang); zt += k*c*np.cos(ang); zp += 2*m*c*np.cos(ang)
    return th, ph, R, z, Rt, Rp, zt, zp      # Rp, zp are d/dphi


def elps_twist(ev, a, b, N, M, iota, Nt=128, Nphi=96):
    th, ph, R, z, Rt, Rphi, zt, zphi = grid_eval(a, b, N, M, Nt, Nphi)
    omega = iota/2
    K1 = 2*np.pi*np.array([Rt*np.cos(ph), Rt*np.sin(ph), zt])
    K2 = np.pi*np.array([Rphi*np.cos(ph) - R*np.sin(ph), Rphi*np.sin(ph) + R*np.cos(ph), zphi])
    X, Y, Z = R*np.cos(ph), R*np.sin(ph), z
    Bv = field_cart(ev, X, Y, Z)
    bphi = (X*Bv[1] - Y*Bv[0])/(X**2 + Y**2)
    flowdir = (omega/np.pi)*K1 + K2/np.pi
    inv = float(np.abs(Bv - bphi*flowdir).max())
    kt = np.fft.fftfreq(Nt, 1/Nt)[:, None]; kp = np.fft.fftfreq(Nphi, 1/Nphi)[None, :]

    def Dd(F, a1, b1):
        return np.real(np.fft.ifft2(np.fft.fft2(F)*(2j*np.pi*kt)**a1*(2j*np.pi*kp)**b1))
    cc = 1/np.mean(1/bphi)
    rhsu = 1 - cc/bphi
    sym = (2j*np.pi*kt)*omega/np.pi + (2j*np.pi*kp)/np.pi
    sym[0, 0] = 1
    U = np.fft.fft2(rhsu)/sym; U[0, 0] = 0
    u = np.real(np.fft.ifft2(U))
    u1 = Dd(u, 1, 0); u2 = Dd(u, 0, 1)
    v = np.array([omega/np.pi, 1/np.pi])
    detP = 1 - (v[0]*u1 + v[1]*u2)
    n = np.cross(K1, K2, axis=0); n2 = (n**2).sum(0)
    DB = jac_cart(ev, X, Y, Z)
    S = DB + DB.transpose(1, 0, 2, 3)
    Sn = np.einsum('ijab,jab->iab', S, n)
    G = np.array([[(K1*K1).sum(0), (K1*K2).sum(0)], [(K2*K1).sum(0), (K2*K2).sum(0)]])
    DKtSn = np.array([(K1*Sn).sum(0), (K2*Sn).sum(0)])
    Gi = np.linalg.inv(G.transpose(2, 3, 0, 1)).transpose(2, 3, 0, 1)
    A = -np.einsum('ijab,jab->iab', Gi, DKtSn)/n2
    DPsi = np.array([[1 - v[0]*u1, -v[0]*u2], [-v[1]*u1, 1 - v[1]*u2]])
    Ahat = detP*np.einsum('ijab,jab->iab', DPsi, A)
    Aavg = (Ahat*detP).mean(axis=(1, 2))
    ws = cc*v
    T = Aavg[0]*ws[1] - Aavg[1]*ws[0]
    return float(T), float(T/np.hypot(*ws)), inv, [float(x) for x in ws]


def flux(ev, a, b, N, M, Nt=512, nq=24):
    """Toroidal flux through phi = 0 enclosed by the torus: Phi = oint G dz with
    G(R, z) = int_1^R B_phi(R', 0, z) dR' (Stokes; B_phi = (1 + d_phi V)/R)."""
    Is, Iz = index_sets(N, M)
    th = 2*np.pi*np.arange(Nt)/Nt
    R = sum(c*np.cos(k*th) for (k, m), c in zip(Is, a))         # psi = 0
    zt = sum(k*c*np.cos(k*th) for (k, m), c in zip(Iz, b))
    z = sum(c*np.sin(k*th) for (k, m), c in zip(Iz, b))
    xg, wg = np.polynomial.legendre.leggauss(nq)
    Rq = 1 + (R[:, None] - 1)*(xg[None, :] + 1)/2
    _, BP, _ = ev.B_cyl(Rq, 0.0, z[:, None] + 0*Rq)
    G = (R - 1)/2*(wg[None, :]*BP).sum(1)
    return float(np.mean(G*zt)*2*np.pi)


def shear(ev, a, b, N, M, iota, delta=2e-4):
    Phi0 = flux(ev, a, b, N, M)
    res = []
    for dl in (-delta, delta):
        g = Galerkin(ev, N, M, iota + dl)
        a1, b1, h = newton_double(g, a.copy(), b.copy(), log=lambda s: None)
        res.append((iota + dl, flux(ev, a1, b1, N, M), h[-1]))
    d = (res[1][0] - res[0][0])/(res[1][1] - res[0][1])
    B0 = float(np.mean(ev.B_cyl(np.array([a[0]]), 0.0, np.array([0.0]))[1]))
    r_eff = np.sqrt(abs(Phi0)/(np.pi*B0))
    return dict(flux=Phi0, diota_dflux=float(d), r_eff=float(r_eff),
                diota_dreff=float(d*2*np.pi*B0*r_eff*np.sign(Phi0)),
                neighbour_newton=[float(r[2]) for r in res], delta=delta)
