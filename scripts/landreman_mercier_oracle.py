#!/usr/bin/env python3
"""Untrusted numerical oracle: Mercier index of Landreman's family 2 (arXiv:2609.26742 v2, §3).

Pure Python (no numpy).  Computes, on surfaces psi = k^2/2 of the sheared family
(eps, S, lam), the inputs of the general Mercier index of Landreman & Jorge (2020) eq. (3.1)
(`PlasmaLean.Stability.MercierGeneral.mercierIndex`), with mu0 = 1 and the toroidal-flux label
psi_t = Phi_t / (2 pi), and prints D_Merc for both signs s_G = +-1 (s_psi = +1).

Two independent routes are used and cross-checked:

* 2-D: surface integrals over the paper's coordinates (chi, zeta), eq. (3.12)-(3.19), with the
  Jacobian (3.18) (checked against finite differences of the embedding), B from (3.2),
  J = curl B and grad psi by central differences.  Then
      dV/dpsi    = int int Jac dchi dzeta,
      dPhi_t/dpsi = (1/2pi) int int (B.grad zeta) Jac,     B.grad zeta = T/(2G)  (3.23),
      dPsi_p/dpsi = (1/2pi) int int (B.grad chi) Jac,      B.grad chi = sqrt(1-Y^2) (3.21),
      dI_tor/dpsi = (1/2pi) int int (J.grad zeta) Jac,
  iota = dPsi_p/dPhi_t, I = I_tor/(2pi), and int f dS/|grad psi_t|^3 =
  int int f Jac / (psi_t'^3 |grad psi|^2).
* 1-D (exact reductions, derived by hand from (3.18) and the zeta -> pi/2 - zeta symmetry):
      Phi_t'(psi) = F1/(2 lam),  F1 = int dchi / (h(S + asin(k cos chi / c)) c),  c = sqrt(1-k^2 sin^2 chi)
      iota = Z/F1,               Z  = int dzeta / sqrt(cosh^2 nu - k^2),  nu = (eps/2) sin 2 zeta
      dV/dpsi_t = 2 pi E iota,   E  = int dchi / c = 4 K(k)
      I' = dI/dpsi_t = lam + 2E/(lam F1).
  In particular V'(psi_t) = 2 pi E(k) iota(psi_t), so positive shear forces a magnetic hill.

Run:  python3 scripts/landreman_mercier_oracle.py [lam] [N]
Nothing printed here is trusted by Lean; see PlasmaLean/Design/LandremanMercier.lean.
"""
import cmath
import math
import sys

EPS = 0.25
S = 4.0
LAM = float(sys.argv[1]) if len(sys.argv) > 1 else 15.0
NGRID = int(sys.argv[2]) if len(sys.argv) > 2 else 48
H = 1e-5


def field(x, y, z):
    w = complex(x, y)
    wb = w.conjugate()
    K = wb * cmath.sqrt(1 + EPS / wb ** 2)
    Xi = w * K + math.pi / 2 - S
    e = cmath.exp(-1j * LAM * z)
    h = 1j * e * cmath.sin(Xi) / (2 * K)
    return (h.real, h.imag, (e * cmath.cos(Xi)).real / LAM)


def psi(x, y, z):
    w = complex(x, y)
    wb = w.conjugate()
    K = wb * cmath.sqrt(1 + EPS / wb ** 2)
    Xi = w * K + math.pi / 2 - S
    e = cmath.exp(-1j * LAM * z)
    return 0.5 * (math.sin(LAM * z) ** 2 + ((e * cmath.cos(Xi)).real) ** 2)


def grad(f, p):
    g = []
    for i in range(3):
        a = list(p)
        b = list(p)
        a[i] += H
        b[i] -= H
        g.append((f(*a) - f(*b)) / (2 * H))
    return g


def curl(p):
    d = [[0.0] * 3 for _ in range(3)]
    for j in range(3):
        a = list(p)
        b = list(p)
        a[j] += H
        b[j] -= H
        Ba = field(*a)
        Bb = field(*b)
        for i in range(3):
            d[i][j] = (Ba[i] - Bb[i]) / (2 * H)
    return (d[2][1] - d[1][2], d[0][2] - d[2][0], d[1][0] - d[0][1])


def hh(s):
    return math.sqrt(4 * s * s + EPS * EPS)


def ac(s):
    return math.sqrt((hh(s) - EPS) / 2)


def bc(s):
    return math.sqrt((hh(s) + EPS) / 2)


def embed(k, chi, zeta):
    X = -k * math.cos(chi)
    Y = k * math.sin(chi)
    nu = EPS / 2 * math.sin(2 * zeta)
    sig = (S + math.atan(math.tanh(nu) * Y / math.sqrt(1 - Y * Y))
           - math.asin(X / math.sqrt(math.cosh(nu) ** 2 - Y * Y)))
    return sig, (ac(sig) * math.cos(zeta), bc(sig) * math.sin(zeta), -math.asin(Y) / LAM), Y, nu


def dot(a, b):
    return sum(i * j for i, j in zip(a, b))


def surface(k, full):
    n = NGRID
    d = (2 * math.pi / n) ** 2
    out = dict(Vp=0.0, Ftp=0.0, Ppp=0.0, Itp=0.0, B2=0.0, JB=0.0, J2=0.0)
    for i in range(n):
        chi = 2 * math.pi * (i + 0.5) / n
        for j in range(n):
            zeta = 2 * math.pi * (j + 0.37) / n
            sig, p, Y, nu = embed(k, chi, zeta)
            G = (hh(sig) + EPS * math.cos(2 * zeta)) / 2
            T = math.sqrt(math.cosh(nu) ** 2 - k * k)
            jac = G / (LAM * hh(sig) * T * math.sqrt(1 - Y * Y))
            out['Vp'] += jac * d
            out['Ftp'] += d / (4 * math.pi * LAM * hh(sig) * math.sqrt(1 - Y * Y))
            out['Ppp'] += d * G / (2 * math.pi * LAM * hh(sig) * T)
            if full:
                gz = (-ac(sig) * math.sin(zeta) / G, bc(sig) * math.cos(zeta) / G, 0.0)
                B = field(*p)
                J = curl(p)
                gp = grad(psi, p)
                out['Itp'] += d * dot(J, gz) * jac / (2 * math.pi)
                wgt = jac / dot(gp, gp) * d
                out['B2'] += dot(B, B) * wgt
                out['JB'] += dot(J, B) * wgt
                out['J2'] += dot(J, J) * wgt
    return out


def trap(f, n=2000):
    return sum(f(2 * math.pi * (i + 0.5) / n) for i in range(n)) * 2 * math.pi / n


def reduced(k):
    """1-D reductions: (psi_t', iota, V'(psi_t), I')."""
    Z = trap(lambda z: 1 / math.sqrt(math.cosh(EPS / 2 * math.sin(2 * z)) ** 2 - k * k))
    E = trap(lambda c: 1 / math.sqrt(1 - k * k * math.sin(c) ** 2))

    def f1(c):
        ct = math.sqrt(1 - k * k * math.sin(c) ** 2)
        return 1 / (hh(S + math.asin(k * math.cos(c) / ct)) * ct)
    F1 = trap(f1)
    return F1 / (4 * math.pi * LAM), Z / F1, 2 * math.pi * E * Z / F1, LAM + 2 * E / (LAM * F1)


def mercier(k):
    ps = k * k / 2
    dp = 1e-4 * ps
    m = reduced(math.sqrt(2 * (ps - dp)))
    c0 = reduced(k)
    p = reduced(math.sqrt(2 * (ps + dp)))
    tp, iota, _, Ip = c0
    iotap = (p[1] - m[1]) / (2 * dp) / tp
    Vpp = (p[2] - m[2]) / (2 * dp) / tp
    muP = -(1 / LAM ** 2) / tp
    r = surface(k, True)
    # cross-check of the reductions against the 2-D route
    assert abs(r['Ftp'] / (2 * math.pi) - tp) < 1e-6 * tp
    assert abs(r['Ppp'] / r['Ftp'] - iota) < 1e-6 * iota
    assert abs(r['Itp'] / (2 * math.pi) / tp - Ip) < 1e-4 * Ip
    cc = 1 / tp ** 3
    B2 = r['B2'] * cc
    BXi = (r['JB'] - Ip * r['B2']) * cc
    Xi2 = (r['J2'] - 2 * Ip * r['JB'] + Ip ** 2 * r['B2']) * cc
    well = muP * Vpp
    D = {}
    for sG in (1, -1):
        X = sG * 2 * math.pi ** 2 * iotap - BXi
        D[sG] = (X ** 2 + (well - Xi2) * B2) / (2 * math.pi) ** 6
    return dict(k=k, iota=iota, iotap=iotap, Vpp=Vpp, muP=muP, well=well, Xi2=Xi2, B2=B2,
                BXi=BXi, Ip=Ip, Dp=D[1], Dm=D[-1])


if __name__ == '__main__':
    print(f'eps={EPS} S={S} lam={LAM} N={NGRID}')
    for k in [0.05, 0.1, 0.3, 0.5, 0.7, 0.9]:
        r = mercier(k)
        print('k=%.2f iota=%.4f iota\'=%.2f V\'\'=%.1f muP\'=%.5f well=%.1f int|Xi|^2=%.2f '
              'intB^2=%.6g intB.Xi=%.2f I\'=%.5f D(sG=+1)=%.6g D(sG=-1)=%.6g' % (
                  r['k'], r['iota'], r['iotap'], r['Vpp'], r['muP'], r['well'], r['Xi2'],
                  r['B2'], r['BXi'], r['Ip'], r['Dp'], r['Dm']))
