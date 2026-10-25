#!/usr/bin/env python3
"""UNTRUSTED numerical study of ideal-ballooning stability of Landreman's family 2.

NOT part of the trusted base. Nothing printed here is used by Lean as a hypothesis.

Equilibrium: Landreman family 2 (arXiv:2609.26742 v2, Sec. 3), eps = 1/4, S = 4, lam = 200,
exactly the Lean definitions `LandremanFamily2.field`, `psi`, `pressureGrad` (mu0 = 1, so
mu0 grad p = -grad psi / lam^2); flux surfaces psi = k^2/2, the Mercier band k in [0.7, 0.9]
(`LandremanFamily2MercierDerived.family2_mercier_stable_derived`).

Ballooning reduction (the SUPPLIED interface `BallooningReduction`): along a field line
X' = B(X) (line element l = 1), with a covering-space eikonal gradient k (k' = -(DB)^T k,
k . B = 0, i.e. k = grad S along the line for some S with B . grad S = 0),
    P = |k|^2 / |B|^2,   Q = -2 (B x k . mu0 grad p)(B x k . kappa) / |B|^4,
    kappa = (DB B - (b . DB B) b)/|B|^2,
and the line is stable iff int (P xi'^2 + Q xi^2) >= 0 for every compactly supported xi.
All derivatives are computed exactly by forward-mode automatic differentiation of the field
formula (no finite differences in P, Q).  Every transported k with k . B = 0 is (up to scale)
k0 - sigma grad psi with k0 = B x grad psi / |grad psi|^2 and sigma' = d (the local shear),
see PlasmaLean/Theory/Stability/BallooningSurface.lean; the eikonal family theta_k is the
choice of the starting direction of k in the plane orthogonal to B.

Stability test: Jacobi/Sturm.  The energy is nonnegative on [-T, T] iff the solution of
(P xi')' = Q xi with xi(-T) = 0 has no zero in (-T, T); in Pruefer form
theta' = cos^2 theta / P - Q sin^2 theta, zeros of xi are crossings of multiples of pi
(always upwards).  We integrate the field line, the transported eikonal and theta jointly
(DOP853, rtol 1e-9) and report theta(T)/pi (< 1: no zero, stable on [-T, T]).

Modes:
  scan  k [T] [gammas]   grid of starting points (chi0, zeta0) x eikonal angles a
  gamma k chi zeta a [T] critical pressure multiplier gamma_c (Q -> gamma Q) by bisection
  affine k               Jacobi test of the affine (Mercier-type) certificate class
  tail  [k]              flux-surface averages of the large-sigma (Mercier-type) tail problem:
                         gamma_c of the averaged condition, and the affine-certificate test
Requires numpy and scipy (e.g. a venv); runtime: a scan of one surface ~ 10-20 min.

Findings (lam = 200; run 2026-10-25, `scan k 60 1,2`, `gamma`, `tail`):
* every one of the 16 x 8 x 3 = 384 (line, theta_k) samples on each of k = 0.70, 0.75, 0.80,
  0.85, 0.90 has no Jacobi zero on [-60, 60] at gamma = 1 and gamma = 2 (worst theta(T)/pi
  = 0.9992, 0.9994, 0.9990, 0.9995, 0.9991 at gamma = 1): numerically ballooning STABLE on the band;
* finite-T critical multipliers (T = 100, bisection): gamma_c ~ 4.68, 4.62 (k = 0.7, two lines),
  7.7 (k = 0.8), 14.8 (k = 0.9);
* the binding constraint is the large-sigma (Mercier-type) tail, reached only for T -> infinity:
  its averaged condition gives gamma_c(tail) = 2.36, 3.13, 4.26, 6.07, 9.39 for
  k = 0.70 ... 0.90, and is marginal at k ~ 0.54 (gamma_c(tail) = 0.83, 0.97, 1.13 at
  k = 0.50, 0.53, 0.56), reproducing the Mercier threshold k_c ~ 0.53 of
  scripts/landreman_family2_map.py; finite-sigma ballooning is much more stable;
* the affine certificate F = a sigma + b (a = -J_par + const, the only Riccati certificates
  linear in sigma; b a function on the torus) is INFEASIBLE: its auxiliary 1-D problem
  (int xi'^2/|grad psi|^2 + Qhat xi^2) has a Jacobi zero every half poloidal turn.  A rigorous
  certificate needs a genuinely sigma-dependent flux resolving the O(1/lam) tip structure of
  |grad psi| on the 2-torus, which is not attempted here.
"""
import math
import sys

import numpy as np
from scipy.integrate import solve_ivp

EPS, S, LAM = 0.25, 4.0, 200.0
GAM = [1.0]


class D:
    """Forward-mode dual number with a 3-vector gradient."""
    __slots__ = ('v', 'g')

    def __init__(s, v, g):
        s.v = v
        s.g = g

    def __add__(a, b):
        return D(a.v + b.v, a.g + b.g) if isinstance(b, D) else D(a.v + b, a.g)
    __radd__ = __add__

    def __sub__(a, b):
        return D(a.v - b.v, a.g - b.g) if isinstance(b, D) else D(a.v - b, a.g)

    def __rsub__(a, b):
        return D(b - a.v, -a.g)

    def __neg__(a):
        return D(-a.v, -a.g)

    def __mul__(a, b):
        return D(a.v * b.v, a.g * b.v + a.v * b.g) if isinstance(b, D) else D(a.v * b, a.g * b)
    __rmul__ = __mul__

    def __truediv__(a, b):
        if isinstance(b, D):
            return D(a.v / b.v, (a.g * b.v - a.v * b.g) / (b.v * b.v))
        return D(a.v / b, a.g / b)


def _f1(fn, dfn):
    return lambda a: D(fn(a.v), dfn(a.v) * a.g) if isinstance(a, D) else fn(a)


sqrt = _f1(math.sqrt, lambda v: 0.5 / math.sqrt(v))
sin = _f1(math.sin, math.cos)
cos = _f1(math.cos, lambda v: -math.sin(v))
sinh = _f1(math.sinh, math.cosh)
cosh = _f1(math.cosh, math.sinh)


def field_psi(x):
    """`LandremanFamily2.field` and `psi` (real form), on duals or floats."""
    x0, x1, x2 = x
    r2 = x0 * x0 + x1 * x1
    Zr = r2 * r2 + EPS * (x0 * x0 - x1 * x1)
    Zi = 2 * EPS * x0 * x1
    Mo = sqrt(Zr * Zr + Zi * Zi)
    sg = sqrt((Mo + Zr) / 2)
    nu = EPS * x0 * x1 / sg
    Mq = sg * sg + nu * nu
    cz, sz = cos(LAM * x2), sin(LAM * x2)
    cs, ss, ch, sh = cos(sg - S), sin(sg - S), cosh(nu), sinh(nu)
    uR = cz * cs * ch - sz * ss * sh
    uI = -(sz * cs * ch + cz * ss * sh)
    vR = cz * ss * ch + sz * cs * sh
    al = sg * x0 + nu * x1
    be = sg * x1 - nu * x0
    B = [-(uR * be + uI * al) / (2 * Mq), (uR * al - uI * be) / (2 * Mq), -vR / LAM]
    return B, (sz * sz + vR * vR) / 2


def evalall(x):
    """B, DB (DB[i, j] = dB_i/dx_j), psi, grad psi at x (exact AD)."""
    xs = [D(x[i], np.eye(3)[i]) for i in range(3)]
    B, psi = field_psi(xs)
    return np.array([b.v for b in B]), np.array([b.g for b in B]), psi.v, psi.g


def surfpt(k, chi, zeta):
    """`LandremanFamily2Surface.surfPt` (eps = 1/4, S = 4)."""
    s1, c1, s2 = math.sin(chi), math.cos(chi), math.sin(2 * zeta)
    Y, X = k * s1, k * c1
    cc = math.sqrt(1 - Y * Y)
    nu = EPS / 2 * s2
    ch, sh = math.cosh(nu), math.sinh(nu)
    T = math.sqrt(ch * ch - k * k)
    T0 = ch * ch - Y * Y
    sA = (cc * ch * X + Y * sh * T) / T0
    sig = S + math.asin(sA)
    h = math.sqrt(4 * sig * sig + EPS * EPS)
    return np.array([math.sqrt((h - EPS) / 2) * math.cos(zeta),
                     math.sqrt((h + EPS) / 2) * math.sin(zeta), -math.asin(Y) / LAM])


def coeffs(B, DB, g, k):
    """P, Q of the supplied reduction (l = 1, mu0 grad p = -g/lam^2)."""
    B2 = B @ B
    DBB = DB @ B
    kap = (DBB - (B @ DBB) / B2 * B) / B2
    Bk = np.cross(B, k)
    return (k @ k) / B2, -2 * (Bk @ (-g / LAM ** 2)) * (Bk @ kap) / B2 ** 2


def rhs_line(t, y):
    B, DB, _, _ = evalall(y[0:3])
    return np.concatenate([B, -DB.T @ y[3:6]])


def rhs_joint(t, y):
    B, DB, _, g = evalall(y[0:3])
    k = y[3:6]
    P, Q = coeffs(B, DB, g, k)
    th = y[6]
    return np.concatenate([B, -DB.T @ k, [math.cos(th) ** 2 / P - GAM[0] * Q * math.sin(th) ** 2]])


def kinit(x, a):
    """Eikonal direction at x: angle a in the plane orthogonal to B (a = 0: k ~ B x grad psi)."""
    B, _, _, g = evalall(x)
    u1 = np.cross(B, g)
    return math.cos(a) * u1 / np.linalg.norm(u1) + math.sin(a) * g / np.linalg.norm(g)


def jacobi(x0, a, T, rtol=1e-9):
    """theta(T)/pi for the line through x0 (at t = 0) with eikonal angle a."""
    y0 = np.concatenate([x0, kinit(x0, a)])
    b = solve_ivp(rhs_line, (0, -T), y0, rtol=rtol, atol=1e-13, method='DOP853')
    s = solve_ivp(rhs_joint, (-T, T), np.concatenate([b.y[:, -1], [0.0]]), rtol=rtol,
                  atol=1e-12, method='DOP853')
    return s.y[6, -1] / math.pi


def scan(k, T=60.0, gammas=(1.0,), nchi=16, nzeta=8, angles=(0.0, 1.2, -1.2)):
    worst = {g: 0.0 for g in gammas}
    for i in range(nchi):
        for j in range(nzeta):
            x = surfpt(k, 2 * math.pi * i / nchi, math.pi * j / nzeta)
            for a in angles:
                r = []
                for g in gammas:
                    GAM[0] = g
                    r.append(jacobi(x, a, T))
                    worst[g] = max(worst[g], r[-1])
                print(k, i, j, a, ' '.join('%.4f' % v for v in r), flush=True)
    GAM[0] = 1.0
    print('k=%g T=%g worst theta(T)/pi:' % (k, T), worst, '(< 1 everywhere: stable)')


def gamma_c(k, chi, zeta, a, T=100.0, lo=1.0, hi=20.0, it=10):
    x = surfpt(k, chi, zeta)
    for _ in range(it):
        mid = math.sqrt(lo * hi)
        GAM[0] = mid
        if jacobi(x, a, T) < 1:
            lo = mid
        else:
            hi = mid
    GAM[0] = 1.0
    return lo, hi


def local(x):
    """Pointwise data on the surface: Jacobian weight, q0, q1, d, J_par, B^2/|g|^2, |g|^2."""
    B, DB, _, g = evalall(x)
    B2, g2 = B @ B, g @ g
    DBB = DB @ B
    kap = (DBB - (B @ DBB) / B2 * B) / B2
    k0 = np.cross(B, g) / g2
    Mg = DB @ g
    d = (k0 @ Mg + (DB @ k0) @ g) / g2
    curl = np.array([DB[2, 1] - DB[1, 2], DB[0, 2] - DB[2, 0], DB[1, 0] - DB[0, 1]])
    q0 = (2 / LAM ** 2) * (kap @ g) / g2
    q1 = (2 / LAM ** 2) * (np.cross(B, g) @ kap) / B2
    return q0, q1, d, (curl @ B) / B2, B2 / g2, g2


def jac_weight(k, chi, zeta):
    """dS/|grad psi| = JacR dchi dzeta (paper (3.18), derived in LandremanFamily2Coarea)."""
    s1, c1, s2, c2 = math.sin(chi), math.cos(chi), math.sin(2 * zeta), math.cos(2 * zeta)
    Y, X = k * s1, k * c1
    cc = math.sqrt(1 - Y * Y)
    nu = EPS / 2 * s2
    ch, sh = math.cosh(nu), math.sinh(nu)
    T = math.sqrt(ch * ch - k * k)
    sA = (cc * ch * X + Y * sh * T) / (ch * ch - Y * Y)
    sig = S + math.asin(sA)
    h = math.sqrt(4 * sig * sig + EPS * EPS)
    return (h + EPS * c2) / 2 / (LAM * h * T * cc)


def tail(k, nchi=1000, nzeta=16):
    """Large-sigma tail.  With F = a sigma + b, a = c - J_par (exact antiderivative of q1:
    B . grad J_par = -q1), the Riccati inequality for all sigma is pointwise equivalent to
        Qhat := q0 - d a - a^2 B^2/|g|^2 >= B . grad b + b^2 |g|^2.
    Its flux-surface average (b periodic) needs <q0 - d a - a^2 B^2/|g|^2> > 0, optimised
    over c: this is the Mercier-type tail condition; gamma scales q0, q1 (hence J_par - <J_par>)."""
    rows = []
    for i in range(nchi):
        chi = 2 * math.pi * (i + 0.5) / nchi
        for j in range(nzeta):
            zeta = math.pi * (j + 0.5) / nzeta
            rows.append((jac_weight(k, chi, zeta),) + local(surfpt(k, chi, zeta)))
    R = np.array(rows)
    w = R[:, 0] / R[:, 0].sum()
    av = lambda f: float((w * f).sum())
    q0, d, a1, r = R[:, 1], R[:, 3], -R[:, 4], R[:, 5]
    a1 = a1 - av(a1)

    def margin(g):
        A2 = av(r)
        A1 = av(d) + 2 * g * av(a1 * r)
        A0 = g * av(q0) - g * av(d * a1) - g * g * av(a1 * a1 * r)
        return A0 + A1 * A1 / (4 * A2), -A1 / (2 * A2)
    lo, hi = 0.0, 100.0
    for _ in range(50):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if margin(mid)[0] > 0 else (lo, mid)
    m1, c1 = margin(1.0)
    print('k=%g: <d> = %.4g, <q0> = %.4g, tail margin(gamma=1) = %.4g (c = %.4g), '
          'gamma_c(tail) = %.3f' % (k, av(d), av(q0), m1, c1, lo))
    return lo


def affine(k, c, T=40.0, chi=0.3, zeta=0.2):
    """Jacobi test of the auxiliary problem of the affine certificate F = a sigma + b,
    a = lam - J_par + c: energy int xi'^2/|g|^2 + Qhat xi^2, Qhat = q0 - d a - a^2 B^2/|g|^2
    (b' + |g|^2 b^2 <= Qhat).  Returns the number of Jacobi zeros on [-T, T] (0 iff feasible
    along this line).  d uses only DB (shearRate of BallooningSurface)."""
    def rhs(t, y):
        B, _, _, _ = evalall(y[0:3])
        q0, _, d, jpar, r, g2 = local(y[0:3])
        a = LAM - jpar + c
        Qh = q0 - d * a - a * a * r
        th = y[3]
        return np.concatenate([B, [math.cos(th) ** 2 * g2 - Qh * math.sin(th) ** 2]])
    x0 = surfpt(k, chi, zeta)
    b = solve_ivp(lambda t, y: evalall(y)[0], (0, -T), x0, rtol=1e-10, atol=1e-13,
                  method='DOP853')
    s = solve_ivp(rhs, (-T, T), np.concatenate([b.y[:, -1], [0.0]]), rtol=1e-8, atol=1e-11,
                  method='DOP853', max_step=0.01)
    return int(s.y[3, -1] / math.pi)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'tail'
    if mode == 'scan':
        k = float(sys.argv[2])
        T = float(sys.argv[3]) if len(sys.argv) > 3 else 60.0
        gs = tuple(float(v) for v in sys.argv[4].split(',')) if len(sys.argv) > 4 else (1.0,)
        scan(k, T, gs)
    elif mode == 'gamma':
        k, chi, zeta, a = (float(v) for v in sys.argv[2:6])
        T = float(sys.argv[6]) if len(sys.argv) > 6 else 100.0
        print('gamma_c in', gamma_c(k, chi, zeta, a, T))
    elif mode == 'affine':
        k = float(sys.argv[2])
        for c in (-0.6, -1.2, -2.0):
            print('k=%g c=%g: Jacobi zeros of the affine auxiliary problem on [-40, 40]: %d'
                  % (k, c, affine(k, c)))
    else:
        for k in ([float(sys.argv[2])] if len(sys.argv) > 2 else [0.7, 0.75, 0.8, 0.85, 0.9]):
            tail(k)
