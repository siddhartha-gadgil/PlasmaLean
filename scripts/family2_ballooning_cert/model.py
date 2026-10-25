"""UNTRUSTED certificate model and convex search for family-2 ballooning (one flux surface).

NOT part of the trusted base.  The certificate (`LandremanFamily2Ballooning.family2_stable_of_cert`)
is a C^1 function Phi(x, s) on surface x R with, at every point x and every s,

    D(x, s) := Q(x, s) - DPhi(x, s)(B, d) - Phi^2 / P(x, s) >= 0,
    P = 1/g2 + s^2 g2/B2,   Q = q0 + s q1.

Ansatz (all pieces smooth on the torus):

    Phi = (c0 - Jpar(x)) s + sum_j f_j(theta, zeta) r_j(s),

* `Jpar = (curl B . B)/|B|^2` with the identity B . grad Jpar = -q1, so the secular terms cancel
  exactly and q1 never has to be evaluated (proved numerically in `geom.check_identity`);
* (theta, zeta): zeta the toroidal angle (all data have period pi in zeta), theta the tip-clustering
  poloidal angle  tan(chi - phi(zeta)) = eps_m tan(theta),  where chi = phi(zeta) is the ridge of
  |grad psi| (the "tips" of the flat cross-section, LandremanFamily2Rotated); uniform theta
  resolution is resolution ~eps_m near the tips;
* f_j: tensor periodic cubic B-splines in (theta, zeta) (NT x NZ coefficients each);
* r_j(s): 1 and, for each width sigma in `sig`, rho = 1/(1+u^2), nu = u/(1+u^2) with the SCALED
  variable u = s/(sigma w(x)), w = |B|/|grad psi|^2 (the natural width: 2e-5 in the flats, 0.06
  at the tips), and the same with absolute widths `sigabs` (u = s/sigma); rational in s, so the
  defect times a positive denominator is a polynomial in s (Polya-checkable).

With this ansatz D is concave in the unknowns (c0, coefficients), so maximising the margin m in

    D(x, s) >= m * omega(x)      on samples (x, s), plus the tail limit s -> +-infinity

is a second-order-cone programme (solved with Clarabel, sparse; each cone is written in the
balanced form y >= x^2, y = (L - m omega)/omega, x = Phi/sqrt(omega P)).  `tail_lp` solves the
s -> infinity problem alone (an LP in f0 for fixed c0, HiGHS); `c0_tail_opt` gives the
flux-surface-average optimum of c0.  Driver: `search.py`.
"""
import numpy as np
import scipy.sparse as sp
import geom

LAM = 200.0


def phiz(k, z):
    """Ridge angle phi(zeta): sin phi = cosh nu sinh nu / R, cos phi = T / R."""
    nu = 0.125 * np.sin(2 * z)
    ch, sh = np.cosh(nu), np.sinh(nu)
    return np.arctan2(ch * sh, np.sqrt(ch * ch - k * k))


def phiz_d(k, z, h=1e-6):
    return (phiz(k, z + h) - phiz(k, z - h)) / (2 * h)


def theta_of_chip(chip, epsm):
    return np.arctan2(np.sin(chip), epsm * np.cos(chip))


def chip_of_theta(th, epsm):
    return np.arctan2(epsm * np.sin(th), np.cos(th))


def bspl(x, n):
    """Periodic cubic B-splines on [0, 1) with n cells: (indices, values, d/dx) lists of 4."""
    t = np.mod(x, 1.0) * n
    i = np.floor(t).astype(int)
    f = t - i
    B = [(1 - f) ** 3 / 6, (3 * f ** 3 - 6 * f ** 2 + 4) / 6, (-3 * f ** 3 + 3 * f ** 2 + 3 * f + 1) / 6,
         f ** 3 / 6]
    dB = [-(1 - f) ** 2 / 2, (9 * f ** 2 - 12 * f) / 6, (-9 * f ** 2 + 6 * f + 3) / 6, f ** 2 / 2]
    idx = [np.mod(i - 3 + j, n) for j in range(4)]
    return idx, B, [d * n for d in dB]


class Model:
    """Geometry at sample points (theta, zeta) of one surface and the certificate basis."""

    def __init__(s, k, epsm, NT, NZ, sig, lam=LAM, scaled=True, sigabs=()):
        s.k, s.epsm, s.NT, s.NZ, s.sig, s.lam = k, epsm, NT, NZ, list(sig), lam
        s.scaled = scaled
        s.sigabs = list(sigabs)
        s.nf = 1 + 2 * len(s.sig) + 2 * len(s.sigabs)
        s.nb = NT * NZ

    def points(s, th, ze):
        """Geometry and basis matrices at the points (theta, zeta) (1-D arrays)."""
        k, epsm = s.k, s.epsm
        chip = chip_of_theta(th, epsm)
        chi = chip + phiz(k, ze)
        D = geom.surface_data(k, chi, ze, s.lam)
        dth = 1 / (epsm * np.cos(chip) ** 2 + np.sin(chip) ** 2 / epsm)
        D['thdot'] = dth * (D['chidot'] - phiz_d(k, ze) * D['zetadot'])
        D['th'], D['ze'], D['chi'] = th, ze, chi
        n = len(th)
        it, Bt, dBt = bspl(th / (2 * np.pi), s.NT)
        iz, Bz, dBz = bspl(ze / np.pi, s.NZ)
        rows, cols, v, dv = [], [], [], []
        for a in range(4):
            for b in range(4):
                rows.append(np.arange(n))
                cols.append(it[a] * s.NZ + iz[b])
                v.append(Bt[a] * Bz[b])
                dv.append(dBt[a] / (2 * np.pi) * Bz[b] * D['thdot'] + Bt[a] * dBz[b] / np.pi * D['zetadot'])
        rows, cols = np.concatenate(rows), np.concatenate(cols)
        D['X'] = sp.csr_matrix((np.concatenate(v), (rows, cols)), shape=(n, s.nb))
        D['DX'] = sp.csr_matrix((np.concatenate(dv), (rows, cols)), shape=(n, s.nb))
        D['omega'] = np.abs(D['q0']) + np.abs(D['d']) * 0.5 + 0.25 * D['B2'] / D['g2']
        return D

    def sfun(s, D, sv, idx=slice(None)):
        """r_j and their derivatives along the flow (x, s)' = (B, d), lists of arrays.
        scaled: u = s/(sigma w(x)), w = |B|/|grad psi|^2, du/dt = d/(sigma w) - u B.grad log w;
        otherwise u = s/sigma, du/dt = d/sigma."""
        d = D['d'][idx]
        out = [(np.ones_like(sv), np.zeros_like(sv))]
        for sg in s.sig:
            if s.scaled:
                w = np.sqrt(D['B2'][idx]) / D['g2'][idx]
                u = sv / (sg * w)
                udot = d / (sg * w) - u * D['lwdot'][idx]
            else:
                u = sv / sg
                udot = d / sg
            den = 1 + u * u
            out.append((1 / den, -2 * u / den ** 2 * udot))
            out.append((u / den, (1 - u * u) / den ** 2 * udot))
        for sg in s.sigabs:
            u = sv / sg
            udot = d / sg
            den = 1 + u * u
            out.append((1 / den, -2 * u / den ** 2 * udot))
            out.append((u / den, (1 - u * u) / den ** 2 * udot))
        return out

    # ---- evaluation of a given certificate -------------------------------------------------
    def defect(s, D, c0, C, sv):
        """Normalised defect D(x, s)/omega(x) at the points of D, for an array sv of s (shape
        (n,) or (n, m)).  C has shape (nf, nb)."""
        sv = np.asarray(sv, float)
        if sv.ndim == 1:
            sv = sv[:, None]
        f = np.array([D['X'] @ C[j] for j in range(s.nf)])        # (nf, n)
        df = np.array([D['DX'] @ C[j] for j in range(s.nf)])
        out = np.empty(sv.shape)
        a = c0 - D['Jpar']
        for col in range(sv.shape[1]):
            ss = sv[:, col]
            R = s.sfun(D, ss)
            F = sum(R[j][0] * f[j] for j in range(s.nf))
            DF = sum(R[j][0] * df[j] + R[j][1] * f[j] for j in range(s.nf))
            P = 1 / D['g2'] + ss * ss * D['g2'] / D['B2']
            Phi = a * ss + F
            out[:, col] = (D['q0'] - D['d'] * a - DF - Phi * Phi / P) / D['omega']
        return out

    def tail_defect(s, D, c0, C):
        a = c0 - D['Jpar']
        df0 = D['DX'] @ C[0]
        return (D['q0'] - D['d'] * a - df0 - a * a * D['B2'] / D['g2']) / D['omega']

    # ---- SOCP assembly ----------------------------------------------------------------------
    def rows(s, D, idx, sv):
        """SOC triples for points idx with s-values sv (same length).  Unknowns
        v = [c0, m, C_0 (nb), ..., C_{nf-1} (nb)].  Returns (A, b) with s = b - A v in SOC(3)^n."""
        n = len(idx)
        X, DX = D['X'][idx], D['DX'][idx]
        d, J, q0, g2, B2, om = (D[key][idx] for key in ('d', 'Jpar', 'q0', 'g2', 'B2', 'omega'))
        R = s.sfun(D, sv, idx)
        # Phi = c0 s - J s + sum_j r_j X C_j ;  L = q0 + d J - d c0 - sum_j (r_j DX + d r_j' X) C_j
        PhiC = sp.hstack([sp.diags(R[j][0]) @ X for j in range(s.nf)])
        LC = sp.hstack([-(sp.diags(R[j][0]) @ DX + sp.diags(R[j][1]) @ X) for j in range(s.nf)])
        P = 1 / g2 + sv * sv * g2 / B2
        z = sp.csr_matrix((n, 1))
        rowPhi = sp.hstack([sp.csr_matrix(sv[:, None]), z, PhiC]).tocsr()
        constPhi = -J * sv
        rowL = sp.hstack([sp.csr_matrix(-d[:, None]), sp.csr_matrix(-om[:, None]), LC]).tocsr()
        constL = q0 + d * J
        return s._triples(rowPhi, constPhi, rowL, constL, P, om)

    def tail_rows(s, D, idx):
        n = len(idx)
        DX = D['DX'][idx]
        d, J, q0, g2, B2, om = (D[key][idx] for key in ('d', 'Jpar', 'q0', 'g2', 'B2', 'omega'))
        r = np.sqrt(B2 / g2)
        z = sp.csr_matrix((n, s.nb))
        rowPhi = sp.hstack([sp.csr_matrix(r[:, None]), sp.csr_matrix((n, 1))] + [z] * s.nf).tocsr()
        constPhi = -J * r
        rowL = sp.hstack([sp.csr_matrix(-d[:, None]), sp.csr_matrix(-om[:, None]), -DX] +
                         [z] * (s.nf - 1)).tocsr()
        constL = q0 + d * J
        return s._triples(rowPhi, constPhi, rowL, constL, np.ones(n), om)

    @staticmethod
    def _triples(rowPhi, constPhi, rowL, constL, P, om):
        """(L - m om) P >= Phi^2 as the balanced rotated cone y >= x^2 with y = (L - m om)/om,
        x = Phi/sqrt(om P): SOC (y + 1, 2 x, y - 1).  (Keeps all entries O(1).)"""
        sc = sp.diags(1 / om)
        sx = sp.diags(1 / np.sqrt(om * P))
        # rows of s = b - A v
        A0 = -(sc @ rowL)
        A1 = -2 * (sx @ rowPhi)
        b0 = constL / om + 1
        b1 = 2 * constPhi / np.sqrt(om * P)
        b2 = constL / om - 1
        n = len(P)
        A = sp.vstack([A0, A1, A0]).tocsr()
        perm = np.arange(3 * n).reshape(3, n).T.ravel()
        A = A[perm]
        b = np.stack([b0, b1, b2], axis=1).ravel()
        return A, b


def solve(model, blocks, reg=1e-8, verbose=False, cbound=None, fixed=None, max_iter=400):
    """blocks: list of (A, b) SOC-triple blocks.  Maximise m - reg |C|^2 over
    v = [c0, m, C].  `fixed`: dict {index: value} of unknowns held fixed (substituted out).
    Returns (c0, m, C, status)."""
    import clarabel
    A = sp.vstack([blk[0] for blk in blocks]).tocsc()
    b = np.concatenate([blk[1] for blk in blocks])
    nv = 2 + model.nf * model.nb
    full = np.zeros(nv)
    free = np.ones(nv, bool)
    if fixed:
        fi = np.array(sorted(fixed))
        fv = np.array([fixed[i] for i in fi])
        full[fi] = fv
        free[fi] = False
        b = b - A[:, fi] @ fv
        A = A[:, np.where(free)[0]]
    nfree = int(free.sum())
    cones = [clarabel.SecondOrderConeT(3)] * (len(b) // 3)
    mpos = int(free[:2].sum()) - 1          # position of m among the free unknowns
    if cbound is not None:
        I = sp.eye(nfree, format='csc')
        keep = np.array([i for i in range(nfree) if i != mpos and not (free[0] and i == 0)])
        I = I[keep]
        A = sp.vstack([A, I, -I]).tocsc()
        b = np.concatenate([b, np.full(2 * len(keep), cbound)])
        cones = cones + [clarabel.NonnegativeConeT(2 * len(keep))]
    diag = np.full(nfree, reg)
    diag[mpos] = 0.0
    if free[0]:
        diag[0] = reg
    Pm = sp.diags(diag).tocsc()
    q = np.zeros(nfree)
    q[mpos] = -1.0
    st = clarabel.DefaultSettings()
    st.verbose = verbose
    st.max_iter = max_iter
    solver = clarabel.DefaultSolver(Pm, q, A, b, cones, st)
    sol = solver.solve()
    full[free] = np.array(sol.x)
    return full[0], full[1], full[2:].reshape(model.nf, model.nb), str(sol.status)


def tail_lp(model, D, c0, om=1e-4, bound=1.0):
    """Tail (s -> +-infinity) problem with c0 fixed: maximise m subject to
    B.grad f0 <= Qhat - m om at the points of D (an LP, HiGHS).  Returns (f0, m)."""
    from scipy.optimize import linprog
    n = len(D['d'])
    a = c0 - D['Jpar']
    Qh = D['q0'] - D['d'] * a - a * a * D['B2'] / D['g2']
    A = sp.hstack([D['DX'], sp.csr_matrix(np.full((n, 1), om))]).tocsr()
    r = linprog(np.r_[np.zeros(model.nb), -1.0], A_ub=A, b_ub=Qh,
                bounds=[(-bound, bound)] * model.nb + [(None, None)], method='highs')
    return r.x[:-1], -r.fun * 1.0


def c0_tail_opt(k, lam=LAM, nchi=4000, nz=32):
    """Flux-surface-average optimum of c0 for the tail (Mercier-type) condition."""
    chi = 2 * np.pi * (np.arange(nchi) + .5) / nchi
    z = np.pi * (np.arange(nz) + .5) / nz
    C, Z = np.meshgrid(chi, z, indexing='ij')
    C, Z = C.ravel(), Z.ravel()
    D = geom.surface_data(k, C, Z, lam)
    s1, c1, s2, c2 = np.sin(C), np.cos(C), np.sin(2 * Z), np.cos(2 * Z)
    Y, X = k * s1, k * c1
    cc = np.sqrt(1 - Y * Y)
    nu = 0.125 * s2
    ch, sh = np.cosh(nu), np.sinh(nu)
    T = np.sqrt(ch * ch - k * k)
    sA = (cc * ch * X + Y * sh * T) / (ch * ch - Y * Y)
    sig = 4 + np.arcsin(sA)
    h = np.sqrt(4 * sig * sig + 1 / 16)
    w = (h + 0.25 * c2) / 2 / (lam * h * T * cc)
    w /= w.sum()
    av = lambda f: float((w * f).sum())
    r = D['B2'] / D['g2']
    J = D['Jpar']
    A2 = av(r)
    A1 = -av(D['d']) + 2 * av(J * r)
    A0 = av(D['q0']) + av(D['d'] * J) - av(J * J * r)
    return A1 / (2 * A2), A0 + A1 ** 2 / (4 * A2)
