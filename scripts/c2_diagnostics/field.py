"""UNTRUSTED numerics (Q-19).  The rational stellarator vacuum field `RationalStellarator.field (1/4)`.

Cylindrical (R, phi, z), R0 = B0 = 1.  Scalar potential Phi = phi + eps*h,
    h = f cos 2phi + g sin 2phi,
    f = ((R^2-1)^2 - 4z^2)/(4R^2),  g = -z((R^2-1)(R^2-5) - 4z^2)/(4R^2),
exactly as in PlasmaLean/Design/RationalStellarator.lean (h = H/4, field = toroidal + (eps/4) gradH)
and notes/theory/first-stellarator-rung.md section 0.  B = grad Phi (vacuum, exact).

Boozer facts used downstream (vacuum, no enclosed toroidal current):
  * covariant B = G grad phi_B with G = 1, so phi_B = Phi = phi + eps*h exactly;
  * theta_B = theta_s + iota*eps*h, theta_s the straight-field-line angle with toroidal angle phi;
  * Jacobian d(theta_B,phi_B)/d(theta_s,phi) = 1 + eps dh/dphi|_line = |B|^2 / B^phi.
Functions return arrays in the orthonormal basis (e_R, e_phi, e_z).
"""
import numpy as np
import sympy as sp

EPS = 0.25
NFP = 2

R, ph, z = sp.symbols('R phi z', real=True)
f = ((R**2 - 1)**2 - 4*z**2) / (4*R**2)
g = -z*((R**2 - 1)*(R**2 - 5) - 4*z**2) / (4*R**2)
h = f*sp.cos(2*ph) + g*sp.sin(2*ph)
e = sp.Rational(1, 4)
BR = e*sp.diff(h, R)
BP = (1 + e*sp.diff(h, ph))/R          # physical toroidal component
BZ = e*sp.diff(h, z)
Bm = sp.sqrt(BR**2 + BP**2 + BZ**2)
dBm = [sp.diff(Bm, R), sp.diff(Bm, ph)/R, sp.diff(Bm, z)]
# field-line ODE in phi:  dR/dphi = R BR/BP,  dz/dphi = R BZ/BP
FR = R*BR/BP
FZ = R*BZ/BP
J2 = [[sp.diff(FR, R), sp.diff(FR, z)], [sp.diff(FZ, R), sp.diff(FZ, z)]]

_args = (R, ph, z)
h_f = sp.lambdify(_args, h, 'numpy', cse=True)
B_f = sp.lambdify(_args, [BR, BP, BZ], 'numpy', cse=True)
Bm_f = sp.lambdify(_args, Bm, 'numpy', cse=True)
dBm_f = sp.lambdify(_args, dBm, 'numpy', cse=True)
J_f = sp.lambdify(_args, [J2[0][0], J2[0][1], J2[1][0], J2[1][1]], 'numpy', cse=True)


def F_f(Rr, phi, zz):
    """dR/dphi, dz/dphi in polynomial form (s = R^2), as in scripts/kam_oracle/field.py."""
    s = Rr*Rr
    c2, s2 = np.cos(2*phi), np.sin(2*phi)
    sf = ((s - 1)**2 - 4*zz**2)/4
    sg = -zz*((s - 1)*(s - 5) - 4*zz**2)/4
    s2fs = (s**2 - 1 + 4*zz**2)/4
    s2gs = -zz*(s**2 - 5 + 4*zz**2)/4
    sfz = -2*zz
    sgz = -((s - 1)*(s - 5) - 12*zz**2)/4
    D = s + EPS*(-2*sf*s2 + 2*sg*c2)
    Ps = s2fs*c2 + s2gs*s2
    Pz = sfz*c2 + sgz*s2
    return [2*EPS*s*Ps/(D*Rr), EPS*s*Pz/D]


def rhs(phi, y):
    """Field line (R, z) plus tangent vector (dR, dz) of the 2-D phi-flow."""
    Rr, zz = y[0], y[1]
    fr, fz = F_f(Rr, phi, zz)
    a, b, c, d = J_f(Rr, phi, zz)
    out = [fr, fz]
    for k in range(2, len(y), 2):
        out += [a*y[k] + b*y[k+1], c*y[k] + d*y[k+1]]
    return np.array(out)


def rhs_plain(phi, y):
    fr, fz = F_f(y[0], phi, y[1])
    return np.array([fr, fz])


if __name__ == '__main__':
    # sanity: axis is a field line, |B| = 1 on it, vacuum (div, curl) by sympy
    print('axis F =', F_f(1.0, 0.3, 0.0), '|B| =', Bm_f(1.0, 0.3, 0.0))
    divB = sp.simplify(sp.diff(R*BR, R)/R + sp.diff(BP, ph)/R + sp.diff(BZ, z))
    print('div B =', divB)
    Fs = sp.lambdify(_args, [FR, FZ], 'numpy')
    import numpy.random as nr
    p = nr.uniform(0.7, 1.3, 20), nr.uniform(0, 6, 20), nr.uniform(-.3, .3, 20)
    print('poly F vs sympy F:', np.abs(np.array(F_f(*p)) - np.array(Fs(*p))).max())
