"""UNTRUSTED.  The rational stellarator field `field (1/4)` in the variables used by the K2 certificate.

Variables: s = R^2 (squared distance from the z-axis), z, toroidal angle phi.  We use the shifted
angle  psi = 2*phi - pi/2  (so phi' = phi - pi/4 is the stellarator-symmetric plane), in which
    cos 2phi = -sin psi,   sin 2phi = cos psi.

With eps = 1/4 and h = f cos 2phi + g sin 2phi, f = ((s-1)^2 - 4z^2)/(4s), g = -z((s-1)(s-5) - 4z^2)/(4s),
the field-line equations dR/dphi = R^2 eps h_R/(1+eps h_phi), dz/dphi = R^2 eps h_z/(1+eps h_phi) become,
after multiplying by the polynomial  D = s (1 + eps h_phi),

    D * ds/dphi = 4 eps s Ps,      D * dz/dphi = eps s Pz,

    D  = s + eps * ( -2 sf sin2phi... ) written below in psi,
    Ps = s^2 h_s,   Pz = s h_z   (polynomials in s, z, cos psi, sin psi).

All quantities are polynomials in (s, z, cos psi, sin psi).  This module gives them in numpy form
(for the oracle) and as integer polynomial formulas (mirrored exactly in the Lean file
PlasmaLean/Design/KamTorusA.lean).
"""
import numpy as np

EPS = 0.25


def parts(s, z):
    """sf = s f, sg = s g, s^2 f_s, s^2 g_s, s f_z, s g_z  (all polynomials)."""
    sf = ((s - 1) ** 2 - 4 * z ** 2) / 4
    sg = -z * ((s - 1) * (s - 5) - 4 * z ** 2) / 4
    s2fs = (s ** 2 - 1 + 4 * z ** 2) / 4
    s2gs = -z * (s ** 2 - 5 + 4 * z ** 2) / 4
    sfz = -2 * z
    sgz = -((s - 1) * (s - 5) - 12 * z ** 2) / 4
    return sf, sg, s2fs, s2gs, sfz, sgz


def DPP(s, z, c, sn):
    """D, Ps, Pz at (s, z) with c = cos psi, sn = sin psi (cos2phi = -sn, sin2phi = c)."""
    sf, sg, s2fs, s2gs, sfz, sgz = parts(s, z)
    c2, s2 = -sn, c
    # h_phi = -2 f sin2phi + 2 g cos2phi
    D = s + EPS * (-2 * sf * s2 + 2 * sg * c2)
    Ps = s2fs * c2 + s2gs * s2
    Pz = sfz * c2 + sgz * s2
    return D, Ps, Pz


def rhs_phi(phi, R, z):
    """dR/dphi, dz/dphi (for tracing; R not s)."""
    s = R * R
    psi = 2 * phi - np.pi / 2
    D, Ps, Pz = DPP(s, z, np.cos(psi), np.sin(psi))
    ds = 4 * EPS * s * Ps / D
    dz = EPS * s * Pz / D
    return ds / (2 * R), dz
