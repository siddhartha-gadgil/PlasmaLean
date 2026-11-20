"""Independent check (N-42) of the Laurent form of the Dommaschk QA candidate claimed in
sources/fusion_complex_geometry_and_stability.pdf, section 3.1. Built from the project's own
candidate.json and basis terms; does not use any script from the source bundle."""
import json, sys
from fractions import Fraction
import sympy as sp

cand = json.load(open(sys.argv[1]))
u, v, z = sp.symbols('u v z')
nonzero = [(b, Fraction(a)) for b, a in zip(cand['basis'], cand['coefficients']) if Fraction(a) != 0]
print('nonzero Dommaschk coefficients:', len(nonzero))
# collect c * R^p (ln R)^q z^j * trig(m phi)
logterms = {}
F = 0
for b, a in nonzero:
    m = b['m']
    for c, p, q, j in b['terms']:
        c = Fraction(c) * a
        if q:
            logterms[(b['trig'], m, p, q, j)] = logterms.get((b['trig'], m, p, q, j), 0) + c
            continue
        assert (p + m) % 2 == 0
        e1, e2 = (p + m) // 2, (p - m) // 2
        if b['trig'] == 'cos':
            t = (u**e1 * v**e2 + u**e2 * v**e1) / 2
        else:
            t = (u**e1 * v**e2 - u**e2 * v**e1) / (2 * sp.I)
        F += sp.Rational(c.numerator, c.denominator) * t * z**j
nzlog = {k: c for k, c in logterms.items() if c != 0}
print('log terms surviving collection:', len(nzlog))
F = sp.expand(F)
P = sp.Poly(F * (u * v)**12, u, v, z)  # clear negative powers
print('nonzero Laurent monomials:', len(P.terms()))
lap = sp.expand(4 * sp.diff(F, u, v) + sp.diff(F, z, 2))
print('Delta_q F == 0:', lap == 0)
Fstar = sp.expand(sp.conjugate(F.subs({u: sp.Symbol('V'), v: sp.Symbol('U')}, simultaneous=True)).subs({sp.conjugate(sp.Symbol('V')): v, sp.conjugate(sp.Symbol('U')): u, sp.conjugate(z): z}))
print('F* == F:', sp.expand(Fstar - F) == 0)
print('F(-u,-v,z) == F:', sp.expand(F.subs({u: -u, v: -v}, simultaneous=True) - F) == 0)
print('F(v,u,-z) == -F:', sp.expand(F.subs({u: v, v: u, z: -z}, simultaneous=True) + F) == 0)
coeff = sp.expand(F * u**6).subs({u: 0}) if False else None
c6 = sp.Poly(sp.expand(F * u**12 * v**12), u, v, z).coeff_monomial(u**6 * v**12)
print('coefficient of u^-6:', c6)
