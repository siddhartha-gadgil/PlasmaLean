#!/usr/bin/env python3
"""Untrusted numerical map of the Mercier index of Landreman's family 2 (arXiv:2609.26742 v2, §3).

Pure Python (no numpy).  For parameters (eps, S, lam) and flux surfaces psi = k^2/2 this computes
the inputs of the general Mercier index of Landreman & Jorge (2020) eq. (3.1)
(`PlasmaLean.Stability.MercierGeneral.mercierIndex`, mu0 = 1, toroidal-flux label psi_t) from the
closed forms proved in Lean:

* one-dimensional labels (PlasmaLean/Design/LandremanFamily2Labels.lean):
      F1 = int dt / (h(S - asin(k sin t / c)) c),  c = sqrt(1 - k^2 + k^2 sin^2 t),
      Z  = int dt / sqrt(cosh^2(eps sin t / 2) - k^2),   E = int dt / sqrt(1 - k^2 sin^2 t),
  and their analytic k-derivatives; psi_t' = F1/(4 pi lam), iota = Z/F1, V'(psi_t) = 2 pi Z E/F1,
  I' = lam + 2E/(lam F1), mu0 p' = -4 pi/(lam F1);
* surface integrals int f dS/|grad psi_t|^3 = int int f Jac/(psi_t'^3 |grad psi|^2) with the closed
  forms of |B|^2, B.Xi, |Xi|^2, |grad psi|^2 (PlasmaLean/Design/LandremanFamily2Surface.lean), in the
  ridge-aligned poloidal angle of PlasmaLean/Design/LandremanFamily2Rotated.lean, the sharp
  1/|grad psi|^2 ridge being integrated with the exact Lorentzian kernel (midpoint product rule).

The index (2pi)^6 D = (sG 2pi^2 iota' - int B.Xi)^2 + (mu0 p' V'' - int |Xi|^2) int B^2 is
reported for both signs sG = +-1, together with R = min_sG X^2/((|well| + int|Xi|^2) int B^2)
(R > 1 iff D > 0 when the well term is a hill).

Findings (eps = 1/4, S = 4; untrusted):
* every surface has a magnetic hill (V'' > 0, mu0 p' < 0); stability comes from shear;
* (2pi)^6 D grows like lam^2 (shear) minus a term growing like lam (hill x int B^2), so Mercier
  stability holds for k > k_c(lam): k_c ~ 0.91, 0.82, 0.68, 0.53, 0.36 for lam = 30, 50, 100, 200,
  500, and there is no stable surface for lam <= 15 (on-axis beta ~ 5-6% at lam = 15, beta ~ 1/lam^2);
* scanning eps in {0.1,..,2} and S in {2, 4, 8} at fixed lam, eps = 1/4, S = 4 is near-optimal.

The certificate PlasmaLean/Design/LandremanFamily2MercierStable.lean proves stability for
lam = 200, k in [7/10, 9/10]; its 34 k-cells were proposed by `#eval` of the Lean checker
`LandremanFamily2Quad.cellCheck` itself (bisection over k with grids (8,8,4), (12,12,6)).

Run:  python3 scripts/landreman_family2_map.py [eps S] (default 0.25 4)
Nothing printed here is trusted by Lean.
"""
import math
import sys

EPS = float(sys.argv[1]) if len(sys.argv) > 2 else 0.25
S = float(sys.argv[2]) if len(sys.argv) > 2 else 4.0


def hh(s):
    return math.sqrt(4 * s * s + EPS * EPS)


def one_d(k, n=2000):
    """F1, F1', Z, Z', E, E' by the midpoint rule over t in [-pi, pi]."""
    acc = [0.0] * 6
    sk = math.sqrt(1 - k * k)
    for i in range(n):
        y = math.sin(-math.pi + 2 * math.pi * (i + 0.5) / n)
        c2 = 1 - k * k + k * k * y * y
        c = math.sqrt(c2)
        sig = S - math.asin(k * y / c)
        h2 = 4 * sig * sig + EPS * EPS
        h = math.sqrt(h2)
        acc[0] += 1 / (h * c)
        acc[1] += (4 * sig * y / (h2 * sk) + k * (1 - y * y)) / (h * c * c2)
        tz = math.cosh(EPS * y / 2) ** 2 - k * k
        acc[2] += 1 / math.sqrt(tz)
        acc[3] += k / tz ** 1.5
        te = 1 - k * k * y * y
        acc[4] += 1 / math.sqrt(te)
        acc[5] += k * y * y / te ** 1.5
    return [a * 2 * math.pi / n for a in acc]


def ridge(k, s2):
    nu = EPS / 2 * s2
    ch, sh = math.cosh(nu), math.sinh(nu)
    T = math.sqrt(ch * ch - k * k)
    rho = ch * sh / T
    u = 1 + rho * rho
    s = rho * math.sqrt(2 / (u + math.sqrt(u * u - 4 * k * k * rho * rho)))
    return nu, ch, sh, T, s, math.sqrt(1 - s * s), math.sqrt(1 - k * k * s * s)


def core(k, lam, dI, z, sp, cp, c2, mode):
    nu, ch, sh, T, s, c, C = z
    s1 = sp * c + cp * s
    c1 = cp * c - sp * s
    Y, X = k * s1, k * c1
    cc = math.sqrt(1 - Y * Y)
    T0 = ch * ch - Y * Y
    sA = (cc * ch * X + Y * sh * T) / T0
    base = c * c * cc + s * s * C
    if mode == 0:
        g = T / c * (base + cp * s * c * k * k * (s * sp / (1 + cp) - c) * (s + s1) / (cc + C))
        fg = sp * g
    elif mode == 1:
        g = T / c * (base + cp * s * c * k * k * (s - s1) * (s * sp / (1 - cp) + c) / (cc + C))
        fg = sp * g
    else:
        g = fg = s1 * cc * T - c1 * ch * sh
    uI = k * fg / T0
    sig = S + math.asin(sA)
    h = math.sqrt(4 * sig * sig + EPS * EPS)
    m, G, q = (h - EPS * c2) / 2, (h + EPS * c2) / 2, sig * sig + nu * nu
    r = m * m / q
    T2, uI2 = T * T, uI * uI
    Bsq = (T2 + uI2) * (m / q) / 4 + X * X / lam ** 2
    gX2 = (q / m) * (T2 * (1 + r) ** 2 + uI2 * (1 - r) ** 2)
    BD = (T2 * (1 + r) - uI2 * (1 - r)) / (2 * lam)
    J = G / (lam * h * T * cc)
    H = (Bsq * J, (dI * Bsq + BD) * J, (dI * (dI * Bsq + 2 * BD) + gX2 / lam ** 2) * J)
    a2 = X * X * gX2
    P = lam ** 2 * T2 * k * k / T0 ** 2
    return H, a2, P, g, a2 + P * fg * fg


def kern(a, b, al, ga):
    sr = math.sqrt(ga / al)
    return (math.atan(b * sr) - math.atan(a * sr)) / math.sqrt(al * ga)


def two_d(k, lam, dI, ntip=24, nside=24, nz=24):
    """int int H_j / gp2 dchi dzeta, j = B^2, B.Xi, |Xi|^2 (four arcs in each angle)."""
    acc = [0.0, 0.0, 0.0]
    for arc2 in range(4):
        for jz in range(nz):
            v = -1 + 2 * (jz + 0.5) / nz
            sv, cv, wv = v / math.sqrt(1 + v * v), 1 / math.sqrt(1 + v * v), 1 / (1 + v * v)
            s2, c2 = [(sv, cv), (-sv, -cv), (cv, sv), (-cv, -sv)][arc2]
            z = ridge(k, s2)
            for arc in range(4):
                n = ntip if arc < 2 else nside
                for i in range(n):
                    a, b = -1 + 2 * i / n, -1 + 2 * (i + 1) / n
                    t = (a + b) / 2
                    st, ct = t / math.sqrt(1 + t * t), 1 / math.sqrt(1 + t * t)
                    if arc < 2:
                        sp, cp = (st, ct) if arc == 0 else (-st, -ct)
                        H, a2, P, g, _ = core(k, lam, dI, z, sp, cp, c2, arc)
                        K = kern(a, b, a2, a2 + P * g * g)
                        val = [x * K for x in H]
                    else:
                        sp, cp = (ct, st) if arc == 2 else (-ct, -st)
                        H, _, _, _, gp2 = core(k, lam, dI, z, sp, cp, c2, 2)
                        val = [x / gp2 * (b - a) / (1 + t * t) for x in H]
                    for q in range(3):
                        acc[q] += val[q] * wv * (2 / nz)
    return acc


def mercier(k, lam):
    F1, F1d, Z, Zd, E, Ed = one_d(k)
    tp = F1 / (4 * math.pi * lam)
    iotap = (Zd * F1 - Z * F1d) / F1 ** 2 / (k * tp)
    Vpp = 2 * math.pi * (Zd * E * F1 + Z * Ed * F1 - Z * E * F1d) / F1 ** 2 / (k * tp)
    muP = -4 * math.pi / (lam * F1)
    dI = -2 * E / (lam * F1)
    IB, IX, IZ = two_d(k, lam, dI)
    B2, BXi, Xi2 = IB / tp ** 3, IX / tp ** 3, IZ / tp ** 3
    sh = 2 * math.pi ** 2 * iotap
    well = muP * Vpp
    D = {sG: (sG * sh - BXi) ** 2 + (well - Xi2) * B2 for sG in (1, -1)}
    R = min((sh - BXi) ** 2, (sh + BXi) ** 2) / ((abs(well) + Xi2) * B2)
    return dict(iota=Z / F1, iotap=iotap, Vpp=Vpp, muP=muP, well=well, B2=B2, BXi=BXi,
                Xi2=Xi2, Dp=D[1], Dm=D[-1], R=R)


def k_crit(lam, lo=0.05, hi=0.97):
    """Smallest k with R > 1 on [k, hi] (bisection; assumes one sign change)."""
    if mercier(hi, lam)['R'] <= 1:
        return None
    if mercier(lo, lam)['R'] > 1:
        return lo
    for _ in range(14):
        mid = (lo + hi) / 2
        if mercier(mid, lam)['R'] > 1:
            hi = mid
        else:
            lo = mid
    return hi


if __name__ == '__main__':
    print(f'eps={EPS} S={S}')
    ks = [0.5, 0.6, 0.7, 0.8, 0.9]
    print('R = min_sG X^2/((|well|+int|Xi|^2) int B^2)  (stable iff R > 1) at k =', ks)
    for lam in [15, 30, 50, 100, 200, 300]:
        print('lam=%4d ' % lam + ' '.join('%7.3f' % mercier(k, lam)['R'] for k in ks))
    for lam in [30, 50, 100, 200]:
        kc = k_crit(lam)
        print('lam=%4d  k_c ~ %s' % (lam, 'none' if kc is None else '%.3f' % kc))
    r = mercier(0.8, 200)
    print('lam=200, k=0.8:', {key: '%.6g' % val for key, val in r.items()})
