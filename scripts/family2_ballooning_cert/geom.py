"""UNTRUSTED vectorised geometry of Landreman family 2 (eps = 1/4, S = 4) for the ballooning
certificate search.  NOT part of the trusted base.

Mirrors exactly the Lean definitions `LandremanFamily2.field`, `psi` and the surface
parametrisation `LandremanFamily2Surface.surfPt`; derivatives are exact forward-mode AD on numpy
arrays (no finite differences), so DB, grad psi, the curvature kappa, the local shear d
(`BallooningSurface.shearRate`) and the drives q0, q1 (`BallooningSurface.eikQ`, mu = -1/lam^2)
are evaluated to rounding accuracy.

Main entry point: `surface_data(k, chi, zeta, lam)` -> dict of arrays (see its docstring).
"""
import numpy as np

EPS, S = 0.25, 4.0


class V:
    """Vectorised forward-mode dual number: value `v` (shape N) and gradient `g` (shape N x 3)."""
    __slots__ = ('v', 'g')

    def __init__(s, v, g):
        s.v = v
        s.g = g

    @staticmethod
    def lift(a):
        return a if isinstance(a, V) else None

    def __add__(a, b):
        return V(a.v + b.v, a.g + b.g) if isinstance(b, V) else V(a.v + b, a.g)
    __radd__ = __add__

    def __sub__(a, b):
        return V(a.v - b.v, a.g - b.g) if isinstance(b, V) else V(a.v - b, a.g)

    def __rsub__(a, b):
        return V(b - a.v, -a.g)

    def __neg__(a):
        return V(-a.v, -a.g)

    def __mul__(a, b):
        if isinstance(b, V):
            return V(a.v * b.v, a.g * b.v[:, None] + b.g * a.v[:, None])
        return V(a.v * b, a.g * b)
    __rmul__ = __mul__

    def __truediv__(a, b):
        if isinstance(b, V):
            return V(a.v / b.v, (a.g * b.v[:, None] - b.g * a.v[:, None]) / (b.v * b.v)[:, None])
        return V(a.v / b, a.g / b)

    def __rtruediv__(a, b):
        return V(b / a.v, -a.g * (b / (a.v * a.v))[:, None])


def _f(fn, dfn):
    def h(a):
        if isinstance(a, V):
            return V(fn(a.v), a.g * dfn(a.v)[:, None])
        return fn(a)
    return h


sqrt = _f(np.sqrt, lambda v: 0.5 / np.sqrt(v))
sin = _f(np.sin, np.cos)
cos = _f(np.cos, lambda v: -np.sin(v))
sinh = _f(np.sinh, np.cosh)
cosh = _f(np.cosh, np.sinh)


def field_psi(x, lam):
    """`LandremanFamily2.field` and `psi` (eps = 1/4, S = 4) on duals or arrays."""
    x0, x1, x2 = x
    r2 = x0 * x0 + x1 * x1
    Zr = r2 * r2 + EPS * (x0 * x0 - x1 * x1)
    Zi = 2 * EPS * x0 * x1
    Mo = sqrt(Zr * Zr + Zi * Zi)
    sg = sqrt((Mo + Zr) / 2)
    nu = EPS * x0 * x1 / sg
    Mq = sg * sg + nu * nu
    cz, sz = cos(lam * x2), sin(lam * x2)
    cs, ss, ch, sh = cos(sg - S), sin(sg - S), cosh(nu), sinh(nu)
    uR = cz * cs * ch - sz * ss * sh
    uI = -(sz * cs * ch + cz * ss * sh)
    vR = cz * ss * ch + sz * cs * sh
    al = sg * x0 + nu * x1
    be = sg * x1 - nu * x0
    B = [-(uR * be + uI * al) / (2 * Mq), (uR * al - uI * be) / (2 * Mq), -vR / lam]
    return B, (sz * sz + vR * vR) / 2, vR, sz, sg


def surfpt(k, chi, zeta, lam):
    """`LandremanFamily2Surface.surfPt` (eps = 1/4, S = 4), vectorised."""
    s1, c1, s2 = np.sin(chi), np.cos(chi), np.sin(2 * zeta)
    Y, X = k * s1, k * c1
    cc = np.sqrt(1 - Y * Y)
    nu = EPS / 2 * s2
    ch, sh = np.cosh(nu), np.sinh(nu)
    T = np.sqrt(ch * ch - k * k)
    T0 = ch * ch - Y * Y
    sA = (cc * ch * X + Y * sh * T) / T0
    sig = S + np.arcsin(sA)
    h = np.sqrt(4 * sig * sig + EPS * EPS)
    return np.array([np.sqrt((h - EPS) / 2) * np.cos(zeta),
                     np.sqrt((h + EPS) / 2) * np.sin(zeta), -np.arcsin(Y) / lam])


def evalall(x, lam):
    """B (3,N), DB (N,3,3) with DB[n,i,j] = dB_i/dx_j, psi, grad psi (N,3), and the gradients of
    the angle carriers vR, sin(lam z), sg at the points x (3,N)."""
    N = x.shape[1]
    xs = [V(x[i], np.tile(np.eye(3)[i], (N, 1))) for i in range(3)]
    B, psi, vR, sz, sg = field_psi(xs, lam)
    Bv = np.array([b.v for b in B])
    DB = np.stack([b.g for b in B], axis=1)
    return Bv, DB, psi, vR, sz, sg


def chi_zeta_of(x, lam):
    """Inverse angles (`chiOf`, `zetaOf`) and their gradients, by AD."""
    N = x.shape[1]
    xs = [V(x[i], np.tile(np.eye(3)[i], (N, 1))) for i in range(3)]
    _, _, vR, sz, sg = field_psi(xs, lam)
    # chi = arg(vR - i sz): grad chi = (vR grad(-sz) - (-sz) grad vR)/(vR^2 + sz^2)
    r2 = vR.v ** 2 + sz.v ** 2
    gchi = (vR.v[:, None] * (-sz.g) + sz.v[:, None] * vR.g) / r2[:, None]
    chi = np.arctan2(-sz.v, vR.v)
    h = sqrt(4 * sg * sg + EPS * EPS)
    a = sqrt((h - EPS) / 2)
    b = sqrt((h + EPS) / 2)
    p = xs[0] / a
    q = xs[1] / b
    rr = p.v ** 2 + q.v ** 2
    gzeta = (p.v[:, None] * q.g - q.v[:, None] * p.g) / rr[:, None]
    zeta = np.arctan2(q.v, p.v)
    return chi, gchi, zeta, gzeta


def surface_data(k, chi, zeta, lam=200.0):
    """Pointwise ballooning data on the surface psi = k^2/2 at angles (chi, zeta) (arrays).

    Returns a dict with (all arrays of shape N):
      x (3,N)  the point surfPt
      B2, g2   |B|^2, |grad psi|^2
      d        local shear `shearRate (DB) B (grad psi)`
      q0, q1   drive Q = q0 + s q1 (eikQ with mu = -1/lam^2)
      Jpar     (curl B . B)/|B|^2   (B . grad Jpar = -q1, checked by `check_identity`)
      chidot, zetadot   B . grad chi, B . grad zeta
      lwdot    B . grad log w, w = |B|/|grad psi|^2 (the natural secular width)
    """
    chi = np.asarray(chi, float).ravel()
    zeta = np.asarray(zeta, float).ravel()
    x = surfpt(k, chi, zeta, lam)
    B, DB, psi, _, _, _ = evalall(x, lam)
    N = x.shape[1]
    xs = [V(x[i], np.tile(np.eye(3)[i], (N, 1))) for i in range(3)]
    _, psiD, _, _, _ = field_psi(xs, lam)
    g = psiD.g.T                       # (3, N)
    B2 = (B * B).sum(0)
    g2 = (g * g).sum(0)
    DBB = np.einsum('nij,jn->in', DB, B)
    kap = (DBB - (B * DBB).sum(0) / B2 * B) / B2
    Bxg = np.cross(B.T, g.T).T
    k0 = Bxg / g2
    Mg = np.einsum('nij,jn->in', DB, g)
    Mk0 = np.einsum('nij,jn->in', DB, k0)
    d = ((k0 * Mg).sum(0) + (Mk0 * g).sum(0)) / g2
    q0 = (2 / lam ** 2) * (g * kap).sum(0) / g2
    q1 = (2 / lam ** 2) * (Bxg * kap).sum(0) / B2
    curl = np.array([DB[:, 2, 1] - DB[:, 1, 2], DB[:, 0, 2] - DB[:, 2, 0],
                     DB[:, 1, 0] - DB[:, 0, 1]])
    Jpar = (curl * B).sum(0) / B2
    # B . grad log w,  w = |B|/|grad psi|^2:  B.grad B2 = 2 <B, DB B>,  B.grad g2 = -2 <DB g, g>
    lwdot = (B * DBB).sum(0) / B2 + 2 * (Mg * g).sum(0) / g2
    _, gchi, _, gzeta = chi_zeta_of(x, lam)
    chidot = (gchi * B.T).sum(1)
    zetadot = (gzeta * B.T).sum(1)
    return dict(x=x, B2=B2, g2=g2, d=d, q0=q0, q1=q1, Jpar=Jpar, chidot=chidot,
                zetadot=zetadot, psi=psi, lwdot=lwdot)


def closed_chidot_zetadot(k, chi, zeta):
    """Paper (3.21), (3.23): B . grad chi = sqrt(1 - Y^2), B . grad zeta = T/(2G)."""
    s1, c1, s2, c2 = np.sin(chi), np.cos(chi), np.sin(2 * zeta), np.cos(2 * zeta)
    Y, X = k * s1, k * c1
    cc = np.sqrt(1 - Y * Y)
    nu = EPS / 2 * s2
    ch, sh = np.cosh(nu), np.sinh(nu)
    T = np.sqrt(ch * ch - k * k)
    sA = (cc * ch * X + Y * sh * T) / (ch * ch - Y * Y)
    sig = S + np.arcsin(sA)
    h = np.sqrt(4 * sig * sig + EPS * EPS)
    G = (h + EPS * c2) / 2
    return cc, T / (2 * G)


def check_identity(k, lam=200.0, n=7, h=1e-5):
    """Finite-difference check of B . grad Jpar = -q1 and of the closed forms of chidot, zetadot."""
    rng = np.random.default_rng(1)
    chi = rng.uniform(-np.pi, np.pi, n)
    zeta = rng.uniform(-np.pi, np.pi, n)
    D = surface_data(k, chi, zeta, lam)
    x = D['x']
    B, _, _, _, _, _ = evalall(x, lam)
    def jpar(y):
        Bv, DB, _, _, _, _ = evalall(y, lam)
        curl = np.array([DB[:, 2, 1] - DB[:, 1, 2], DB[:, 0, 2] - DB[:, 2, 0],
                         DB[:, 1, 0] - DB[:, 0, 1]])
        return (curl * Bv).sum(0) / (Bv * Bv).sum(0)
    BgJ = (jpar(x + h * B) - jpar(x - h * B)) / (2 * h)
    cd, zd = closed_chidot_zetadot(k, chi, zeta)
    return dict(BgJ_plus_q1=np.max(np.abs(BgJ + D['q1'])), q1max=np.max(np.abs(D['q1'])),
                chidot_err=np.max(np.abs(cd - D['chidot'])), zetadot_err=np.max(np.abs(zd - D['zetadot'])))


if __name__ == '__main__':
    for k in (0.7, 0.9):
        print(k, check_identity(k))
