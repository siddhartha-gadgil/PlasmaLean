"""UNTRUSTED numerics.  Flow-form invariant torus of the Dommaschk certification target.

Ansatz (stellarator symmetric about the line phi = 0, z = 0), theta in radians, psi = 2 phi:

    R(theta, phi) = sum_{(k,m) in Is} a_km cos(k theta + m psi),
    z(theta, phi) = sum_{(k,m) in Iz} b_km sin(k theta + m psi),
    Is = {(0,m): 0 <= m <= M} u {(k,m): 1 <= k <= N, |m| <= M},   Iz = Is \\ {(0,0)}.

Equation (dfield.py): RR = D (d_phi R + iota d_theta R) - 2 R Ps = 0,
                      RZ = D (d_phi z + iota d_theta z) - s Pz = 0,     d_phi = 2 d_psi,
with iota fixed (negative for this field).  RR is a sine series and RZ a cosine series, so the
Galerkin projection onto Iz resp. Is is a square system, as in scripts/kam_oracle/flow_torus.py.

Double precision: residual and Jacobian by FFT on an Nt x Np grid (the Jacobian of "multiply by w,
project" is a Toeplitz+Hankel matrix in the Fourier coefficients of w, so no dense collocation
matrices are formed).  Multiprecision: the same residual with gmpy2 mpfr numbers in numpy object
arrays and separable real DFTs; refinement x <- x - J0^{-1} F_mp(x) with the double Jacobian J0.

Initial guess: axis by Newton on the period map, launch radius by bisection on the Birkhoff
rotation number, weighted-Birkhoff Fourier coefficients of the section curve, flow to a grid.
"""
import math
import time

import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import lu_factor, lu_solve

from dfield import TRIG, trig_values


# ======================================================================= field-line tracing
class Tracer:
    def __init__(self, ev):
        self.ev = ev
        self.C = np.stack([ev.C[k] for k in ('D', 'Ps', 'Pz')])      # (3, 7, I, J) float

    def rhs(self, phi, R, z):
        T = trig_values(2*phi)                                       # (7,)
        c = np.tensordot(T, self.C, axes=([0], [1]))                 # (3, I, J)
        zp = np.stack([z**j for j in range(c.shape[2])])             # (J, L)
        s = R*R
        out = []
        for q in range(3):
            v = c[q] @ zp                                            # (I, L)
            acc = v[-1]
            for i in range(v.shape[0] - 2, -1, -1):
                acc = acc*s + v[i]
            out.append(acc)
        D, Ps, Pz = out
        return 2*R*Ps/D, s*Pz/D

    def flow(self, R0, z0, phis, rtol=1e-13, atol=1e-15):
        R0 = np.atleast_1d(np.asarray(R0, float)); z0 = np.atleast_1d(np.asarray(z0, float))
        n = R0.size

        def f(t, y):
            a, b = self.rhs(t, y[:n], y[n:])
            return np.concatenate([a, b])
        sol = solve_ivp(f, (phis[0], phis[-1]), np.concatenate([R0, z0]), method='DOP853',
                        rtol=rtol, atol=atol, t_eval=phis)
        assert sol.success, sol.message
        return sol.y[:n], sol.y[n:]           # (n, len(phis))


def birkhoff_weights(n):
    t = np.arange(1, n + 1)/(n + 1)
    w = np.exp(-1/(t*(1 - t)))
    return w/w.sum()


def find_axis(tr, R0=0.964, z0=0.0, tol=1e-13):
    R, z = R0, z0
    for _ in range(20):
        d = 1e-7
        Rs = np.array([R, R + d, R]); zs = np.array([z, z, z + d])
        PR, Pz = tr.flow(Rs, zs, np.array([0, np.pi]))
        PR, Pz = PR[:, -1], Pz[:, -1]
        F = np.array([PR[0] - R, Pz[0] - z])
        Mo = np.array([[(PR[1] - PR[0])/d, (PR[2] - PR[0])/d], [(Pz[1] - Pz[0])/d, (Pz[2] - Pz[0])/d]])
        step = np.linalg.solve(Mo - np.eye(2), -F)
        R, z = R + step[0], z + step[1]
        if np.abs(step).max() < tol:
            break
    return R, z, Mo


def section_iota(tr, Ra, za, r, nper):
    """Birkhoff rotation number (iota per toroidal turn, signed) of lines launched at
    (Ra + r, za) on phi = 0, and a convergence estimate."""
    r = np.atleast_1d(r)
    PR, Pz = tr.flow(Ra + r, za + 0*r, np.pi*np.arange(nper + 1))
    th = np.unwrap(np.arctan2(Pz - za, PR - Ra), axis=1)
    d = np.diff(th, axis=1)
    io = (d*birkhoff_weights(nper)).sum(1)/np.pi
    h = nper//2
    io1 = (d[:, :h]*birkhoff_weights(h)).sum(1)/np.pi
    io2 = (d[:, h:2*h]*birkhoff_weights(h)).sum(1)/np.pi
    return io, np.abs(io1 - io2), PR, Pz


def find_launch(tr, Ra, za, iota_target, lo=0.005, hi=0.075, nper=200, rounds=3):
    """Launch radius with signed rotation number iota_target (|iota| decreasing in r)."""
    for _ in range(rounds):
        rs = np.linspace(lo, hi, 9)
        io, _, _, _ = section_iota(tr, Ra, za, rs, nper)
        a = np.abs(io)
        i = int(np.searchsorted(-a, -abs(iota_target)))       # a decreasing
        i = min(max(i, 1), 8)
        lo, hi = rs[i - 1], rs[i]
    io, err, _, _ = section_iota(tr, Ra, za, np.array([lo, hi]), nper)
    # final secant
    r = lo + (abs(iota_target) - abs(io[0]))*(hi - lo)/(abs(io[1]) - abs(io[0]))
    return float(r)


def initial_torus(tr, Ra, za, r, nper=1000, Nf=40, Nt=64, Np=48):
    """Grid values of the flow torus K(theta, phi) = flow_{0->phi}(k(theta - iota phi)) from the
    section conjugacy k (weighted Birkhoff).  Returns R, z (Nt, Np) on theta_i = 2 pi i/Nt,
    psi_j = 2 pi j/Np (phi_j = pi j/Np), and the traced iota."""
    io, err, PR, Pz = section_iota(tr, Ra, za, np.array([r]), nper)
    io, PR, Pz = float(io[0]), PR[0], Pz[0]
    om = io/2*2*np.pi                         # theta advance per period (radians)
    w = birkhoff_weights(nper + 1)
    k = np.arange(-Nf, Nf + 1)
    E = np.exp(-1j*np.outer(om*np.arange(nper + 1), k))
    cR = (w[:, None]*E*PR[:, None]).sum(0)
    cz = (w[:, None]*E*Pz[:, None]).sum(0)
    th = 2*np.pi*np.arange(Nt)/Nt
    ph = np.pi*np.arange(Np)/Np
    TT = th[:, None] - io*ph[None, :]
    Ek = np.exp(1j*TT[..., None]*k)
    R0 = np.real(Ek @ cR).ravel(); z0 = np.real(Ek @ cz).ravel()
    PRg, Pzg = tr.flow(R0, z0, np.concatenate([ph, [np.pi]]))
    col = np.tile(np.arange(Np), Nt)
    Rg = PRg[np.arange(R0.size), col].reshape(Nt, Np)
    zg = Pzg[np.arange(R0.size), col].reshape(Nt, Np)
    tail = float(np.abs(cR[:5]).max() + np.abs(cz[:5]).max())
    return Rg, zg, io, float(err[0]), tail


# ======================================================================= Galerkin (double)
def index_sets(N, M):
    Is = [(0, m) for m in range(M + 1)] + [(k, m) for k in range(1, N + 1) for m in range(-M, M + 1)]
    return np.array(Is), np.array(Is[1:])


def from_grid(Rg, zg, N, M):
    """Ansatz coefficients from grid values (FFT, symmetric parts)."""
    Nt, Np = Rg.shape
    FR = np.fft.fft2(Rg)/Rg.size
    FZ = np.fft.fft2(zg)/zg.size
    Is, Iz = index_sets(N, M)
    a = np.array([(1 if (k, m) == (0, 0) else 2)*FR[k % Nt, m % Np].real for k, m in Is])
    b = np.array([-2*FZ[k % Nt, m % Np].imag for k, m in Iz])
    return a, b


def resize(a, b, N0, M0, N, M):
    Is0, Iz0 = index_sets(N0, M0)
    Is, Iz = index_sets(N, M)
    da = {tuple(i): c for i, c in zip(Is0, a)}; db = {tuple(i): c for i, c in zip(Iz0, b)}
    return (np.array([da.get(tuple(i), 0.0) for i in Is]), np.array([db.get(tuple(i), 0.0) for i in Iz]))


class Galerkin:
    def __init__(self, ev, N, M, iota, Nt=None, Np=None, fac=3):
        self.ev, self.N, self.M, self.iota = ev, N, M, iota
        self.Nt = Nt or (fac*N + 8 + (fac*N) % 2)
        self.Np = Np or (fac*M + 8 + (fac*M) % 2)
        self.Is, self.Iz = index_sets(N, M)
        self.th = 2*np.pi*np.arange(self.Nt)/self.Nt
        self.ps = 2*np.pi*np.arange(self.Np)/self.Np
        T = trig_values(self.ps)[:, None, :]            # (7, 1, Np)
        self.cf = ev.coeff_fields(T)
        self.kf = np.fft.fftfreq(self.Nt, 1/self.Nt)[:, None]
        self.mf = np.fft.fftfreq(self.Np, 1/self.Np)[None, :]
        self.lam_s = 2*self.Is[:, 1] + iota*self.Is[:, 0]
        self.lam_z = 2*self.Iz[:, 1] + iota*self.Iz[:, 0]

    # ---- synthesis
    def _H(self, I, c, kind):
        H = np.zeros((self.Nt, self.Np), complex)
        k, m = I[:, 0], I[:, 1]
        if kind == 'c':
            np.add.at(H, (k % self.Nt, m % self.Np), c/2)
            np.add.at(H, (-k % self.Nt, -m % self.Np), c/2)
        else:
            np.add.at(H, (k % self.Nt, m % self.Np), c/2j)
            np.add.at(H, (-k % self.Nt, -m % self.Np), -c/2j)
        return H

    def fields(self, a, b):
        Ng = self.Nt*self.Np
        HR = self._H(self.Is, a, 'c'); HZ = self._H(self.Iz, b, 's')
        f = lambda H: np.real(np.fft.ifft2(H))*Ng
        R, z = f(HR), f(HZ)
        Rth, Rps = f(1j*self.kf*HR), f(1j*self.mf*HR)
        zth, zps = f(1j*self.kf*HZ), f(1j*self.mf*HZ)
        return R, z, Rth, Rps, zth, zps

    def residual_grid(self, a, b):
        R, z, Rth, Rps, zth, zps = self.fields(a, b)
        D, Ps, Pz = self.ev.DPP(R*R, z, cf=self.cf)
        RR = D*(2*Rps + self.iota*Rth) - 2*R*Ps
        RZ = D*(2*zps + self.iota*zth) - R*R*Pz
        return RR, RZ, D

    def proj(self, RR, RZ):
        Ng = self.Nt*self.Np
        fr = np.fft.fft2(RR)/Ng; fz = np.fft.fft2(RZ)/Ng
        Fs = -2*fr[self.Iz[:, 0] % self.Nt, self.Iz[:, 1] % self.Np].imag
        Fc = 2*fz[self.Is[:, 0] % self.Nt, self.Is[:, 1] % self.Np].real
        Fc[0] *= 0.5
        return np.concatenate([Fs, Fc])

    def F(self, a, b):
        RR, RZ, _ = self.residual_grid(a, b)
        return self.proj(RR, RZ)

    # ---- Jacobian
    def _block(self, wh, rows, cols, rk, ck):
        Nt, Np = self.Nt, self.Np
        out = np.empty((len(rows), len(cols)))
        for s0 in range(0, len(rows), 512):
            r = rows[s0:s0 + 512]
            Dl = wh[(r[:, None, 0] - cols[None, :, 0]) % Nt, (r[:, None, 1] - cols[None, :, 1]) % Np]
            Sg = wh[(r[:, None, 0] + cols[None, :, 0]) % Nt, (r[:, None, 1] + cols[None, :, 1]) % Np]
            if rk == 's' and ck == 'c':
                v = -(Dl + Sg).imag
            elif rk == 's':
                v = (Dl - Sg).real
            elif ck == 'c':
                v = (Dl + Sg).real
            else:
                v = (Dl - Sg).imag
            if rk == 'c' and s0 == 0:
                v[0] *= 0.5                     # row (0,0) of the cosine projection
            out[s0:s0 + 512] = v
        return out

    def J(self, a, b):
        R, z, Rth, Rps, zth, zps = self.fields(a, b)
        s = R*R
        h = 1e-30
        D, Ps, Pz = self.ev.DPP(s, z, cf=self.cf)
        Dc, Psc, Pzc = self.ev.DPP((R + 1j*h)**2, z, cf=self.cf)
        D_R, Ps_R, Pz_R = Dc.imag/h, Psc.imag/h, Pzc.imag/h
        Dc, Psc, Pzc = self.ev.DPP(s + 0j, z + 1j*h, cf=self.cf)
        D_z, Ps_z, Pz_z = Dc.imag/h, Psc.imag/h, Pzc.imag/h
        LR = 2*Rps + self.iota*Rth
        LZ = 2*zps + self.iota*zth
        Ng = self.Nt*self.Np
        ff = lambda w: np.fft.fft2(w)/Ng
        w1 = ff(D)
        w2 = ff(D_R*LR - 2*Ps - 2*R*Ps_R)
        w3 = ff(D_z*LR - 2*R*Ps_z)
        w4 = ff(D_R*LZ - 2*R*Pz - s*Pz_R)
        w5 = ff(D_z*LZ - s*Pz_z)
        Is, Iz = self.Is, self.Iz
        na = len(Is)
        Jm = np.empty((2*na - 1, 2*na - 1), order="F")   # Fortran order: LU in place; peak ~ 2 n^2 doubles
        Jm[:na - 1, :na] = self._block(w2, Iz, Is, 's', 'c')
        Jm[:na - 1, :na] -= self._block(w1, Iz, Is, 's', 's')*self.lam_s[None, :]
        Jm[:na - 1, na:] = self._block(w3, Iz, Iz, 's', 's')
        Jm[na - 1:, :na] = self._block(w4, Is, Is, 'c', 'c')
        Jm[na - 1:, na:] = self._block(w1, Is, Iz, 'c', 'c')*self.lam_z[None, :]
        Jm[na - 1:, na:] += self._block(w5, Is, Iz, 'c', 's')
        return Jm


def newton_double(g, a, b, steps=12, tol=1e-14, log=print):
    na = len(a)
    hist = []
    for it in range(steps):
        Fv = g.F(a, b)
        e = float(np.abs(Fv).max())
        hist.append(e)
        log(f"  double Newton {it}: |F|_inf = {e:.3e}")
        if e < tol or (it >= 3 and e > 0.5*hist[-2]):
            break
        d = lu_solve(lu_factor(g.J(a, b), overwrite_a=True, check_finite=False), -Fv)
        lim = min(1.0, 0.02/max(np.abs(d).max(), 1e-300))       # trust region on coefficients
        a, b = a + lim*d[:na], b + lim*d[na:]
    return a, b, hist


# ======================================================================= multiprecision
class MPNum:
    """gmpy2 mpfr backend for object arrays (fast); constants from strings/Fractions."""

    def __init__(self, dps):
        import gmpy2
        self.g = gmpy2
        self.bits = int(dps*3.33) + 24
        gmpy2.get_context().precision = self.bits
        self.pi = gmpy2.const_pi()

    def mpf(self, x):
        from fractions import Fraction
        if isinstance(x, Fraction):
            return self.g.mpfr(self.g.mpq(x.numerator, x.denominator))
        return self.g.mpfr(x)

    def cos(self, x):
        return self.g.cos(x)

    def sin(self, x):
        return self.g.sin(x)


def obj(arr, num):
    out = np.empty(np.shape(arr), dtype=object)
    flat = out.reshape(-1)
    for i, v in enumerate(np.ravel(arr)):
        flat[i] = num.mpf(v) if not isinstance(v, float) else num.mpf(float(v))
    return out


class GalerkinMP:
    """Residual of the Galerkin system in multiprecision on the grid of a double Galerkin object
    (or on an Nt x Np grid of choice, for off-grid error estimates)."""

    def __init__(self, evmp, num, N, M, iota_mp, Nt, Np):
        self.ev, self.num, self.N, self.M, self.iota = evmp, num, N, M, iota_mp
        self.Nt, self.Np = Nt, Np
        self.Is, self.Iz = index_sets(N, M)
        two_pi = 2*num.pi
        th = [two_pi*i/Nt for i in range(Nt)]
        ps = [two_pi*j/Np for j in range(Np)]
        mk = np.empty((len(TRIG), 1, Np), dtype=object)
        for t, (kd, n) in enumerate(TRIG):
            f = num.cos if kd == 'c' else num.sin
            for j in range(Np):
                mk[t, 0, j] = f(n*ps[j])
        self.cf = evmp.coeff_fields(mk)
        ks = np.arange(N + 1); ms = np.arange(-M, M + 1)
        self.ks, self.ms = ks, ms
        self.Ct = np.array([[num.cos(k*x) for k in ks] for x in th], dtype=object)   # (Nt, N+1)
        self.St = np.array([[num.sin(k*x) for k in ks] for x in th], dtype=object)
        self.Cp = np.array([[num.cos(m*x) for m in ms] for x in ps], dtype=object)   # (Np, 2M+1)
        self.Sp = np.array([[num.sin(m*x) for m in ms] for x in ps], dtype=object)

    def _full(self, I, c):
        A = np.empty((self.N + 1, 2*self.M + 1), dtype=object)
        A[...] = self.num.mpf(0)
        for (k, m), v in zip(I, c):
            A[k, m + self.M] = v
        return A

    def fields(self, a, b):
        A = self._full(self.Is, a); B = self._full(self.Iz, b)
        kk = self.ks[:, None]; mm = self.ms[None, :]
        Ct, St, CpT, SpT = self.Ct, self.St, self.Cp.T, self.Sp.T
        # cos(k t + m p) = cos kt cos mp - sin kt sin mp ; sin(k t + m p) = sin kt cos mp + cos kt sin mp
        def cosser(X):
            return Ct.dot(X.dot(CpT)) - St.dot(X.dot(SpT))

        def sinser(X):
            return St.dot(X.dot(CpT)) + Ct.dot(X.dot(SpT))
        R = cosser(A); z = sinser(B)
        Rth = -sinser(A*kk); Rps = -sinser(A*mm)
        zth = cosser(B*kk); zps = cosser(B*mm)
        return R, z, Rth, Rps, zth, zps

    def residual_grid(self, a, b):
        R, z, Rth, Rps, zth, zps = self.fields(a, b)
        s = R*R
        D, Ps, Pz = self.ev.DPP(s, z, cf=self.cf)
        RR = D*(2*Rps + self.iota*Rth) - 2*R*Ps
        RZ = D*(2*zps + self.iota*zth) - s*Pz
        return RR, RZ, D

    def proj(self, RR, RZ):
        Ng = self.Nt*self.Np
        Ct, St, Cp, Sp = self.Ct, self.St, self.Cp, self.Sp
        Fs_full = St.T.dot(RR).dot(Cp) + Ct.T.dot(RR).dot(Sp)      # sum f sin(k t + m p)
        Fc_full = Ct.T.dot(RZ).dot(Cp) - St.T.dot(RZ).dot(Sp)      # sum f cos(k t + m p)
        Fs = [2*Fs_full[k, m + self.M]/Ng for k, m in self.Iz]
        Fc = [(1 if (k, m) == (0, 0) else 2)*Fc_full[k, m + self.M]/Ng for k, m in self.Is]
        return np.array(Fs + Fc, dtype=object)

    def F(self, a, b):
        RR, RZ, _ = self.residual_grid(a, b)
        return self.proj(RR, RZ)


def refine_mp(gd, gmp, a, b, steps=6, tol=None, log=print):
    """x <- x - J0^{-1} F_mp(x); a, b object arrays (mpfr).  Returns a, b, history."""
    na = len(a)
    lu = lu_factor(gd.J(np.array([float(x) for x in a]), np.array([float(x) for x in b])),
                   overwrite_a=True, check_finite=False)
    hist = []
    for it in range(steps + 1):
        t0 = time.time()
        Fv = gmp.F(a, b)
        Ff = np.array([float(x) for x in Fv])
        e = float(np.abs(Ff).max())
        hist.append(e)
        log(f"  mp refine {it}: |F_galerkin|_inf = {e:.3e} ({time.time() - t0:.1f}s)")
        if it == steps or (tol is not None and e < tol) or (it >= 2 and e > 0.1*hist[-2]):
            break
        d = lu_solve(lu, -Ff)
        a = a + obj(d[:na], gmp.num)
        b = b + obj(d[na:], gmp.num)
    return a, b, hist


# ======================================================================= diagnostics
def decay(a, b, N, M):
    Is, Iz = index_sets(N, M)
    byk = np.zeros(N + 1); bym = np.zeros(M + 1)
    for (k, m), c in list(zip(Is, a)) + list(zip(Iz, b)):
        byk[k] = max(byk[k], abs(c)); bym[abs(m)] = max(bym[abs(m)], abs(c))

    def rate(v, lo, hi):
        x = np.arange(len(v)); sel = (x >= lo) & (x <= hi) & (v > 0)
        if sel.sum() < 3:
            return float('nan')
        return float(-np.polyfit(x[sel], np.log(v[sel]), 1)[0])
    rk = rate(byk, 2, max(N - 2, 3)); rm = rate(bym, 2, max(M - 2, 3))
    return dict(max_by_k=byk.tolist(), max_by_m=bym.tolist(), rate_theta=rk, rate_psi=rm,
                strip_theta_turns=rk/(2*math.pi), strip_phi_turns=rm/(2*math.pi),
                tail_theta=float(byk[-1]), tail_psi=float(bym[-1]))


def mp_spectrum(num, F, Kmax=None, Mmax=None):
    """Fourier amplitudes of a real grid function F (object array, Nt x Np, mpfr) by a separable
    multiprecision DFT: returns float array A[k, m + Mmax] = sqrt(c_km^2 + s_km^2) for the half-plane
    0 <= k <= Kmax, |m| <= Mmax (k = 0: m >= 0), F = sum (c cos + s sin)(k theta + m psi).
    (A double FFT of the mp values cannot resolve the 20+ decades of the residual spectrum.)"""
    Nt, Np = F.shape
    Kmax = Kmax or Nt//2 - 1
    Mmax = Mmax or Np//2 - 1
    two_pi = 2*num.pi
    th = [two_pi*i/Nt for i in range(Nt)]
    ps = [two_pi*j/Np for j in range(Np)]
    ks = range(Kmax + 1); ms = range(-Mmax, Mmax + 1)
    Ct = np.array([[num.cos(k*x) for k in ks] for x in th], dtype=object)
    St = np.array([[num.sin(k*x) for k in ks] for x in th], dtype=object)
    Cp = np.array([[num.cos(m*x) for m in ms] for x in ps], dtype=object)
    Sp = np.array([[num.sin(m*x) for m in ms] for x in ps], dtype=object)
    CtF, StF = Ct.T.dot(F), St.T.dot(F)
    C = CtF.dot(Cp) - StF.dot(Sp)
    S = StF.dot(Cp) + CtF.dot(Sp)
    Ng = Nt*Np
    A = np.zeros((Kmax + 1, 2*Mmax + 1))
    for k in range(Kmax + 1):
        for j, m in enumerate(ms):
            if k == 0 and m < 0:
                continue
            f = 1 if (k == 0 and m == 0) else 2
            A[k, j] = float(f*num.g.sqrt(C[k, j]**2 + S[k, j]**2)/Ng)
    return A


def strip_norms_coeffs(AR, AZ, gamma_list, rhos=(0.0, 0.005, 0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.075, 0.1)):
    """Weighted l1 norms ||E||_rho = sum |e_km| e^{2 pi rho (|k| + |m|)} (half-plane real amplitudes;
    equals the two-sided complex l1 norm; angles in turns theta/2pi, phi/pi) and FHL ratios
    max/(gamma^4 rho^4) for each gamma in gamma_list.  Also the weighted mass in the outermost
    5 k- and m-columns (truncation indicator for the DFT grid)."""
    K, Mw = AR.shape
    Mmax = (Mw - 1)//2
    kk = np.arange(K)[:, None]; mm = np.abs(np.arange(-Mmax, Mmax + 1))[None, :]
    edge = (kk >= K - 5) | (mm >= Mmax - 4)
    out = []
    for rho in rhos:
        w = np.exp(2*np.pi*rho*(kk + mm))
        eR, eZ = float((AR*w).sum()), float((AZ*w).sum())
        frac = float(((AR + AZ)*w*edge).sum()/max(((AR + AZ)*w).sum(), 1e-300))
        out.append(dict(rho=rho, ER=eR, EZ=eZ, edge_fraction=frac,
                        ratios=[(max(eR, eZ)/(g**4*rho**4) if rho > 0 else None) for g in gamma_list]))
    return out


def fft_spectrum(F, Kmax=None, Mmax=None):
    """Double-precision counterpart of mp_spectrum (noise floor ~1e-16 max|F|)."""
    Nt, Np = F.shape
    Kmax = Kmax or Nt//2 - 1
    Mmax = Mmax or Np//2 - 1
    f = np.fft.fft2(F)/F.size
    A = np.zeros((Kmax + 1, 2*Mmax + 1))
    for k in range(Kmax + 1):
        for j, m in enumerate(range(-Mmax, Mmax + 1)):
            if k == 0 and m < 0:
                continue
            A[k, j] = (1 if (k == 0 and m == 0) else 2)*abs(f[k % Nt, m % Np])
    return A
