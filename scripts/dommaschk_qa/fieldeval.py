"""UNTRUSTED numerics (Q-16, N-31).  Fast batched evaluation of Dommaschk vacuum fields and the
quantities the optimiser needs: magnetic axis, rotational transform, Boozer spectrum of |B|.

Field (basis.py):  B = grad Phi,  Phi = phi + sum_k a_k V_k, cylindrical (R, phi, z), R0 = B0R0 = 1.
Many coefficient vectors ("configurations") are integrated at once: points have shape (nconf, nl)
and a configuration's field is F(x) @ W[:, :, conf], where F are the monomials R^p (ln R)^q z^j
trig(m phi) and W = A @ a (exact basis tables A, see `Tables`).  Batching over configurations is
what makes the finite-difference Jacobian cheap (one integration for all columns).

Boozer angles (exact for a vacuum field B = grad Phi with Phi - phi single-valued, N-30 section 2):
    phi_B = Phi,   theta_B = theta_s + iota (Phi - phi),   G = 1,
    Jacobian d(theta_B, phi_B)/d(theta_s, phi) = |B|^2 / B^phi.
Along the field line launched at theta_s = 0, theta_s = iota*phi, hence theta_B = iota*Phi.  The
Boozer coefficients of |B|,
    c_mn = < |B| e^{-i(m theta_B - n NFP phi_B)} >_Boozer = < |B| Jac e^{-i(m iota - n NFP) Phi} >_line,
are weighted Birkhoff averages along ONE long field line (the line average equals the (theta_s, phi)
torus average for an irrational torus; Das-Saiki-Sander-Yorke weights, spectrally accurate).  The
same convention as scripts/c2_diagnostics/boozer.py: modes (m, n) with n in units of NFP.
"""
import os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'c2_diagnostics'))
from nemov import nemov_sums, eps_eff_from          # noqa: E402,F401  (re-exported for diagnostics)

COMP = ('BR', 'BP', 'BZ', 'V')   # physical components of grad V, and V itself


def birkhoff_weights(n):
    """Same weights as scripts/c2_diagnostics/tori.birkhoff_weights (copied: importing tori.py
    builds the rational-field sympy model of Q-19 at import time)."""
    t = (np.arange(n) + 0.5)/n
    w = np.exp(-1.0/(t*(1 - t)))
    return w/w.sum()


class Tables:
    """Exact basis -> monomial tables.  A[c] has shape (nf, nbasis): component c of grad V_k (or V_k)
    is sum_f F_f A[c][f, k].  base[c] (nf,) is the contribution of grad phi (B_phi = 1/R)."""

    def __init__(self, b, nfp):
        self.nfp = nfp
        self.nb = len(b)
        trig = [('cos', 0)]
        feats = {}

        def feat(p, q, j, tr):
            if tr not in trig:
                trig.append(tr)
            key = (p, q, j, trig.index(tr))
            if key not in feats:
                feats[key] = len(feats)
            return feats[key]

        entries = []   # (comp, feature, basis, value)
        for k, bk in enumerate(b):
            m, tr = bk['m'], bk['trig']
            T = ('cos', 0) if m == 0 else (tr, m)
            dT = None if m == 0 else (('sin', m), -m) if tr == 'cos' else (('cos', m), m)
            for c, p, q, j in bk['terms']:
                c = float(c)
                entries.append((3, feat(p, q, j, T), k, c))
                if p:
                    entries.append((0, feat(p - 1, q, j, T), k, c*p))
                if q:
                    entries.append((0, feat(p - 1, q - 1, j, T), k, c*q))
                if dT is not None:
                    entries.append((1, feat(p - 1, q, j, dT[0]), k, c*dT[1]))
                if j:
                    entries.append((2, feat(p, q, j - 1, T), k, c*j))
        f_base = feat(-1, 0, 0, ('cos', 0))
        nf = len(feats)
        self.A = np.zeros((4, nf, self.nb))
        for comp, f, k, v in entries:
            self.A[comp, f, k] += v
        self.base = np.zeros((4, nf))
        self.base[1, f_base] = 1.0
        keys = sorted(feats, key=feats.get)
        self.trig = trig
        self.P = sorted({k[0] for k in keys}); self.Q = sorted({k[1] for k in keys})
        self.J = sorted({k[2] for k in keys})
        self.pidx = np.array([self.P.index(k[0]) for k in keys])
        self.qidx = np.array([self.Q.index(k[1]) for k in keys])
        self.jidx = np.array([self.J.index(k[2]) for k in keys])
        self.tidx = np.array([k[3] for k in keys])
        self.nf = nf

    def weights(self, X):
        """X (nconf, nb) -> W (4, nf, nconf)."""
        return self.base[:, :, None] + np.einsum('cfk,nk->cfn', self.A, X)

    def trig_vals(self, phi):
        return np.array([1.0 if m == 0 else (np.cos(m*phi) if t == 'cos' else np.sin(m*phi))
                         for t, m in self.trig])

    def eval(self, W, R, phi, z, comps=(0, 1, 2)):
        """Components at points R, z (nconf, nl), common scalar phi.  Returns (len(comps), nconf, nl)."""
        with np.errstate(all='ignore'):
            lR = np.log(R)
        Rp = np.stack([R**p if p else np.ones_like(R) for p in self.P])
        Lq = np.stack([lR**q if q else np.ones_like(R) for q in self.Q])
        Zj = np.stack([z**j if j else np.ones_like(R) for j in self.J])
        F = Rp[self.pidx]*Lq[self.qidx]*Zj[self.jidx]
        F *= self.trig_vals(phi)[self.tidx][:, None, None]
        return np.einsum('cfn,fnl->cnl', W[list(comps)], F)


def line_rhs(tab, W, phi, R, z):
    BR, BP, BZ = tab.eval(W, R, phi, z)
    return R*BR/BP, R*BZ/BP


def _rk4_step(tab, W, phi, R, z, h):
    a1, b1 = line_rhs(tab, W, phi, R, z)
    a2, b2 = line_rhs(tab, W, phi + h/2, R + h/2*a1, z + h/2*b1)
    a3, b3 = line_rhs(tab, W, phi + h/2, R + h/2*a2, z + h/2*b2)
    a4, b4 = line_rhs(tab, W, phi + h, R + h*a3, z + h*b3)
    return R + h/6*(a1 + 2*a2 + 2*a3 + a4), z + h/6*(b1 + 2*b2 + 2*b3 + b4)


def _sane(R, z):
    bad = ~np.isfinite(R) | ~np.isfinite(z) | (R < 0.3) | (R > 3.0) | (np.abs(z) > 1.5)
    R = np.where(bad, 1.0, R); z = np.where(bad, 0.0, z)
    return R, z, bad


def period_map(tab, W, R, z, ns, nper=1):
    """Field-line map over nper field periods (2 pi/NFP each), ns RK4 steps per period."""
    h = 2*np.pi/tab.nfp/ns
    lost = np.zeros(R.shape, bool)
    for i in range(nper*ns):
        R, z = _rk4_step(tab, W, i*h, R, z, h)
        R, z, bad = _sane(R, z); lost |= bad
    return R, z, lost


def find_axis(tab, W, R0, z0, ns, tol=1e-12, maxit=12, fd=1e-6):
    """Fixed points of the period map (one per configuration) by Newton with a finite-difference
    Jacobian.  R0, z0: (nconf,) initial guesses.  Returns R, z, ok (nconf,), monodromy (nconf,2,2)."""
    R = np.array(R0, float); z = np.array(z0, float)
    ok = np.zeros(R.shape, bool); M = np.zeros(R.shape + (2, 2))
    for _ in range(maxit):
        Rs = np.stack([R, R + fd, R], 1); zs = np.stack([z, z, z + fd], 1)
        PR, Pz, lost = period_map(tab, W, Rs, zs, ns)
        M[:, 0, 0] = (PR[:, 1] - PR[:, 0])/fd; M[:, 1, 0] = (Pz[:, 1] - Pz[:, 0])/fd
        M[:, 0, 1] = (PR[:, 2] - PR[:, 0])/fd; M[:, 1, 1] = (Pz[:, 2] - Pz[:, 0])/fd
        F = np.stack([PR[:, 0] - R, Pz[:, 0] - z], 1)
        Jm = M - np.eye(2)
        det = Jm[:, 0, 0]*Jm[:, 1, 1] - Jm[:, 0, 1]*Jm[:, 1, 0]
        det = np.where(np.abs(det) < 1e-14, 1e-14, det)
        dR = -(Jm[:, 1, 1]*F[:, 0] - Jm[:, 0, 1]*F[:, 1])/det
        dz = -(-Jm[:, 1, 0]*F[:, 0] + Jm[:, 0, 0]*F[:, 1])/det
        step = np.sqrt(dR**2 + dz**2)
        lim = np.minimum(1.0, 0.05/np.maximum(step, 1e-300))    # damped (trust radius 0.05)
        R = R + lim*dR; z = z + lim*dz
        ok = (step < tol) & ~lost.any(1)
        if ok.all():
            break
    ok &= np.isfinite(R) & (np.abs(M[:, 0, 0] + M[:, 1, 1]) < 2)   # elliptic axis (surfaces around it)
    return R, z, ok, M


def axis_curve(tab, W, Ra, za, ns, nsamp=None):
    """Samples of the axis over one field period: phi (n,), R, z (nconf, n)."""
    h = 2*np.pi/tab.nfp/ns
    Rs, zs = [Ra.copy()], [za.copy()]
    R, z = Ra[:, None].copy(), za[:, None].copy()
    for i in range(ns - 1):
        R, z = _rk4_step(tab, W, i*h, R, z, h)
        Rs.append(R[:, 0].copy()); zs.append(z[:, 0].copy())
    return h*np.arange(ns), np.array(Rs).T, np.array(zs).T


def trace_surfaces(tab, W, R0, z0, ns, nper, half=False):
    """Trace lines from (R0, z0) (nconf, nl) at phi = 0 over nper periods.  Returns
    sec (nper+1, 2, nconf, nl) section points at phi = k 2pi/NFP, and per-step samples
    Bm, Jac, Phi (nsteps, nconf, nl) at the start of every step (Phi includes phi), lost (nconf, nl).
    half=True also returns the sections at phi = (k + 1/2) 2pi/NFP (needs ns even)."""
    h = 2*np.pi/tab.nfp/ns
    R, z = np.array(R0, float), np.array(z0, float)
    nsteps = nper*ns
    sec = np.empty((nper + 1, 2) + R.shape); sec[0, 0], sec[0, 1] = R, z
    Bm = np.empty((nsteps,) + R.shape); Jac = np.empty_like(Bm); Phi = np.empty_like(Bm)
    lost = np.zeros(R.shape, bool)
    sech = np.empty((nper, 2) + R.shape)
    for i in range(nsteps):
        phi = i*h
        BR, BP, BZ, V = tab.eval(W, R, phi, z, comps=(0, 1, 2, 3))
        B2 = BR**2 + BP**2 + BZ**2
        Bm[i] = np.sqrt(B2); Jac[i] = B2*R/BP; Phi[i] = phi + V
        a1, b1 = R*BR/BP, R*BZ/BP
        a2, b2 = line_rhs(tab, W, phi + h/2, R + h/2*a1, z + h/2*b1)
        a3, b3 = line_rhs(tab, W, phi + h/2, R + h/2*a2, z + h/2*b2)
        a4, b4 = line_rhs(tab, W, phi + h, R + h*a3, z + h*b3)
        R = R + h/6*(a1 + 2*a2 + 2*a3 + a4); z = z + h/6*(b1 + 2*b2 + 2*b3 + b4)
        R, z, bad = _sane(R, z); lost |= bad
        if (i + 1) % ns == 0:
            sec[(i + 1)//ns, 0], sec[(i + 1)//ns, 1] = R, z
        if half and (i + 1) % ns == ns//2:
            sech[i//ns, 0], sech[i//ns, 1] = R, z
    if half:
        return sec, Bm, Jac, Phi, lost, sech
    return sec, Bm, Jac, Phi, lost


def iota_from_sections(sec, Ra, za, nfp):
    """Rotation number about the axis point (Ra, za) (nconf,) on phi = 0.  iota per toroidal angle.
    Returns iota, |iota(first half) - iota(second half)| (convergence estimate), both (nconf, nl)."""
    th = np.unwrap(np.arctan2(sec[:, 1] - za[None, :, None], sec[:, 0] - Ra[None, :, None]), axis=0)
    d = np.diff(th, axis=0)
    n = d.shape[0]; per = 2*np.pi/nfp
    full = np.einsum('t,t...->...', birkhoff_weights(n), d)/per
    hlf = n//2
    a = np.einsum('t,t...->...', birkhoff_weights(hlf), d[:hlf])/per
    b = np.einsum('t,t...->...', birkhoff_weights(hlf), d[hlf:2*hlf])/per
    return full, np.abs(a - b)


def boozer_coeffs(Bm, Jac, Phi, iota, nfp, mmax, nmax):
    """c[m, n + nmax] (complex) for 0 <= m <= mmax, -nmax <= n <= nmax, per line: shape
    (nconf, nl, mmax+1, 2 nmax+1).  Also the Birkhoff mean of Jac (should be 1)."""
    T = Bm.shape[0]
    w = birkhoff_weights(T)[:, None, None]
    f = (w*Bm*Jac)
    E1 = np.exp(-1j*iota[None]*Phi)                     # e^{-i theta_B}
    F1 = np.exp(1j*nfp*Phi)                              # e^{+i NFP phi_B}
    Em = [f.astype(complex)]
    for _ in range(mmax):
        Em.append(Em[-1]*E1)
    Fn = [np.ones_like(E1)]
    for _ in range(nmax):
        Fn.append(Fn[-1]*F1)
    Fn = [np.conj(x) for x in Fn[:0:-1]] + Fn            # n = -nmax..nmax
    Em = np.stack(Em, -1); Fn = np.stack(Fn, -1)          # (T, nconf, nl, M) (T, nconf, nl, N)
    c = np.einsum('tkam,tkan->kamn', Em, Fn)
    jm = np.einsum('t,t...->...', w[:, 0, 0], Jac)
    return c, jm


def qa_bad_modes(c, nmax):
    """Complex Boozer coefficients incompatible with quasi-axisymmetry (n != 0), normalised by c_00
    and in the cos-amplitude convention A_mn = 2|c_mn|.  m = 0 uses n > 0 only (n < 0 conjugate).
    Returns (nconf, nl, nbad) complex."""
    mm = c.shape[-2]
    sel = []
    for m in range(mm):
        for n in range(-nmax, nmax + 1):
            if n == 0 or (m == 0 and n < 0):
                continue
            sel.append((m, n + nmax))
    mi = np.array([s[0] for s in sel]); ni = np.array([s[1] for s in sel])
    return 2*c[..., mi, ni]/np.real(c[..., 0, nmax])[..., None]


def amplitudes_dict(c, nmax):
    """One line's coefficient array (M+1, 2N+1) -> {(m, n): c} as in c2_diagnostics/boozer.spectrum."""
    out = {}
    for m in range(c.shape[0]):
        for n in range(-nmax, nmax + 1):
            if m == 0 and n < 0:
                continue
            out[(m, n)] = c[m, n + nmax]
    return out
