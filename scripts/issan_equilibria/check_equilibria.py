#!/usr/bin/env python3
"""Independent check of the closed-form equilibria of Issan, José, Landreman, Citrin, Tracey,
"Non-axisymmetric MHD equilibria with an arbitrary number of field periods", arXiv:2611.07672
(sources/Non-AxisymmetricMHD.pdf). Untrusted numerics (note N-43): nothing here is a proof.

The coordinate map (3), auxiliary functions (5)-(6), field (7) and flux/pressure (8) are typed
from the paper. Derivatives are exact (sympy); residuals are evaluated with 40-digit arithmetic
at random points. Checks, for each family k in {1, 0, -1}, several N and both signs s:

  A  Cartesian equations (1): div B = 0, (curl B) x B = grad p, B . grad psi = 0,
     computed with the inverse Jacobian matrix, not with the paper's reduced equations (24)-(26).
  B  Jacobian formula (9) against the determinant.
  C  Axis condition: d/d rho H(rho_a, 0) = 0 with C2(rho_a) from (6).
  D  Family 1 with rho_a = rho_0: C2 = 0 and the covariant form (19)-(20),
     B = H grad zeta + grad Phi (so the poloidal circulation of B vanishes).
  E  Interchange instability identities of Section 4.3: xi0 x B = grad chi,
     Q(xi1) = -g B, div xi1 = g, (xi0 + eps xi1) . grad p = -g.
  F  Axis radius formula (16).

usage: check_equilibria.py [--points K] [--seed S]
"""
import argparse, random, sys
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
rho, zeta, eta = sp.symbols('rho zeta eta', real=True)
q = (rho, zeta, eta)


def build(N, k, rho0, rhoa, s):
    """Return a dict of sympy expressions for family k, N field periods."""
    m1, m2, m3 = 1 + (k - 1) * N, 1 + k * N, 1 + (k + 1) * N
    assert m1 != 0 and m3 != 0
    C1 = sp.sign(m1) * rho0 / m1**2 * (rho / rho0)**m1
    C3 = rho0 / m3**2 * (rho0 / rho)**m3
    C5 = 2 * rho0 / (N * sp.sqrt(abs(m1) * m3)) * (rho0 / rho)**N
    Dp = m1 * (m1 + m2) * C1 + m3 * (m3 + m2) * C3
    Dm = m1 * (m1 + m2) * C1 - m3 * (m3 + m2) * C3
    at = lambda e: e.subs(rho, rhoa)
    rad = (at(m1 * C1 + m3 * C3) * at(m1**2 * C1 - m3**2 * C3) * at(Dm)) / (m2**3 * at(Dp))
    C2a = s * sp.sqrt(rad)
    C2 = C2a * (rhoa / rho)**N * at(Dm) / Dm
    C4 = N**2 * C5 / Dp
    x = C1 * sp.cos(m1 * zeta) + C2 * sp.cos(m2 * zeta) - eta * C4 * sp.sin(m2 * zeta) \
        - C3 * sp.cos(m3 * zeta)
    y = C1 * sp.sin(m1 * zeta) + C2 * sp.sin(m2 * zeta) + eta * C4 * sp.cos(m2 * zeta) \
        - C3 * sp.sin(m3 * zeta)
    z = eta + C5 * sp.sin(N * zeta)
    H = (m1 * C1 + m3 * C3)**2 + m2**2 * (C2**2 + eta**2 * C4**2)
    psi = (H - H.subs({rho: rhoa, eta: 0})) / 2
    return dict(N=N, k=k, m=(m1, m2, m3), C=(C1, C2, C3, C4, C5), Dp=Dp, Dm=Dm, rad=rad,
                X=sp.Matrix([x, y, z]), H=H, psi=psi)


class Chart:
    """Numerical evaluation of Cartesian differential operators through the chart."""

    def __init__(self, X):
        self.X = X
        self.Jm = X.jacobian(q)            # d x_i / d q_a
        self.det = self.Jm.det()
        self.fJ = sp.lambdify(q, self.Jm, 'mpmath')

    def Ji(self, pt):                       # d q_a / d x_i
        return mp.matrix(self.fJ(*pt)) ** -1

    def grad(self, f):
        df = sp.lambdify(q, [sp.diff(f, a) for a in q], 'mpmath')
        def g(pt):
            Ji = self.Ji(pt); d = df(*pt)
            return [sum(d[a] * Ji[a, i] for a in range(3)) for i in range(3)]
        return g

    def dvec(self, V):                      # matrix of d V_i / d x_j at a point
        dV = sp.lambdify(q, sp.Matrix(3, 3, lambda i, a: sp.diff(V[i], q[a])), 'mpmath')
        def g(pt):
            return mp.matrix(dV(*pt)) * self.Ji(pt)
        return g

    def div(self, V):
        g = self.dvec(V)
        return lambda pt: sum(g(pt)[i, i] for i in range(3))

    def curl(self, V):
        g = self.dvec(V)
        def c(pt):
            D = g(pt)
            return [D[2, 1] - D[1, 2], D[0, 2] - D[2, 0], D[1, 0] - D[0, 1]]
        return c


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def norm(v):
    return mp.sqrt(sum(abs(c)**2 for c in v))


def rel(a, b):
    """Relative size of a - b."""
    d = norm([u - v for u, v in zip(a, b)])
    return d / max(norm(a), norm(b), mp.mpf(1) / 10**20)


def cases():
    r0 = sp.Integer(1)
    out = []
    for N in (1, 2, 3, 4, 5):
        out.append(('F1', N, 1, r0, sp.Rational(11, 10), 1))      # rho_a > rho_0
        out.append(('F1', N, 1, r0, sp.Rational(11, 10), -1))
        out.append(('F1 rho_a=rho_0', N, 1, r0, r0, 1))
    for N in (2, 3, 4, 5):
        out.append(('F2 small rho_a', N, 0, r0, sp.Rational(3, 4), 1))
    out += [('F2 iota=N', 3, 0, r0, sp.Rational(112, 100), 1),
            ('F2 iota=N', 4, 0, r0, sp.Rational(106, 100), -1),
            ('F2 iota=N', 5, 0, r0, sp.Rational(104, 100), 1)]
    out += [('F3', 3, -1, r0, sp.Rational(97, 100), 1),
            ('F3', 4, -1, r0, sp.Rational(89, 100), -1),
            ('F3', 5, -1, r0, sp.Rational(88, 100), 1)]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--points', type=int, default=4)
    ap.add_argument('--seed', type=int, default=20261116)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    tol = mp.mpf(10) ** -25
    worst = {}
    ok = True

    def record(name, val):
        nonlocal ok
        worst[name] = max(worst.get(name, mp.mpf(0)), val)
        if not val < tol:
            ok = False

    for label, N, k, rho0, rhoa, s in cases():
        E = build(N, k, rho0, rhoa, s)
        radv = sp.N(E['rad'], 30)
        if radv < 0:
            print(f'{label} N={N}: radicand of C2(rho_a) negative ({radv}); case skipped')
            ok = False
            continue
        ch = Chart(E['X'])
        B = sp.diff(E['X'], zeta)                     # eq. (7): B = d x / d zeta
        psi, H = E['psi'], E['H']
        p = -2 * psi                                  # p = p0 - 2 psi; p0 drops out of grad p
        C1, C2, C3, C4, C5 = E['C']
        m1, m2, m3 = E['m']
        fB = sp.lambdify(q, list(B), 'mpmath')
        divB, curlB, gradp, gradpsi = ch.div(B), ch.curl(B), ch.grad(p), ch.grad(psi)
        fdet = sp.lambdify(q, ch.det, 'mpmath')
        # eq. (9)
        det9 = E['Dm'] / (rho * E['Dp']) * ((m1 * C1 + m3 * C3)**2 - m2**2 * eta**2 * C4**2) \
            - E['Dp'] / (rho * E['Dm']) * m2**2 * C2**2
        fdet9 = sp.lambdify(q, det9, 'mpmath')
        # C: axis condition
        dH = sp.N(sp.diff(H, rho).subs({rho: rhoa, eta: 0}), 40)
        scale = sp.N(abs(H.subs({rho: rhoa, eta: 0})), 40)
        record('C axis: dH/drho(rho_a,0)', abs(mp.mpf(str(dH))) / mp.mpf(str(scale)))
        # E: stability trial displacements; delta is any constant, take a symbol value
        delta = sp.Rational(1, 50)
        chi = (delta - psi)**3 * eta
        Xr, Xe = sp.diff(E['X'], rho), sp.diff(E['X'], eta)
        xi0 = (sp.diff(chi, eta) * Xr - sp.diff(chi, rho) * Xe) / ch.det
        xi1 = chi * (sp.diff(p, eta) * Xr - sp.diff(p, rho) * Xe) / ch.det
        g = 2 * (delta - psi)**3 / ch.det * sp.diff(psi, rho)
        fxi0 = sp.lambdify(q, list(xi0), 'mpmath')
        fxi1 = sp.lambdify(q, list(xi1), 'mpmath')
        fg = sp.lambdify(q, g, 'mpmath')
        gradchi = ch.grad(chi)
        Q1 = ch.curl(sp.Matrix(cross(list(xi1), list(B))))
        divxi1 = ch.div(xi1)
        for _ in range(args.points):
            pt = (mp.mpf(str(sp.N(rhoa, 30))) * (1 + mp.mpf(rng.uniform(-0.02, 0.02))),
                  mp.mpf(rng.uniform(0, 6.283)), mp.mpf(rng.uniform(-0.02, 0.02)))
            Bv = fB(*pt)
            Jv = curlB(pt)
            gp = gradp(pt)
            record('A div B / |B|', abs(divB(pt)) / norm(Bv))
            record('A |J x B - grad p| (relative)', rel(cross(Jv, Bv), gp))
            record('A B.grad psi / (|B||grad psi|)',
                   abs(sum(a * b for a, b in zip(Bv, gradpsi(pt)))) / (norm(Bv) * norm(gradpsi(pt))))
            record('B Jacobian (9) (relative)', abs(fdet(*pt) - fdet9(*pt)) / abs(fdet(*pt)))
            x0, x1, gv = fxi0(*pt), fxi1(*pt), fg(*pt)
            record('E xi0 x B = grad chi', rel(cross(x0, Bv), gradchi(pt)))
            record('E Q(xi1) = -g B', rel(Q1(pt), [-gv * b for b in Bv]))
            record('E div xi1 = g', abs(divxi1(pt) - gv) / max(abs(gv), mp.mpf(10)**-20))
            record('E xi0.grad p = -g, xi1.grad p = 0',
                   (abs(sum(a * b for a, b in zip(x0, gp)) + gv)
                    + abs(sum(a * b for a, b in zip(x1, gp)))) / max(abs(gv), mp.mpf(10)**-20))
        # F: axis radius (16)
        Xa = E['X'].subs({rho: rhoa, eta: 0})
        R2 = Xa[0]**2 + Xa[1]**2
        a = lambda e: e.subs(rho, rhoa)
        R2f = a(C1)**2 + a(C2)**2 + a(C3)**2 + 2 * a(C2) * (a(C1) - a(C3)) * sp.cos(N * zeta) \
            - 2 * a(C1) * a(C3) * sp.cos(2 * N * zeta)
        f = sp.lambdify(zeta, R2 - R2f, 'mpmath')
        record('F axis radius (16)', max(abs(f(mp.mpf(rng.uniform(0, 6.283)))) for _ in range(4)))
        # D: family 1 with rho_a = rho_0
        if k == 1 and rhoa == rho0:
            c2 = sp.N(sp.Abs(C2.subs(rho, sp.Rational(21, 20))), 30)
            record('D C2 = 0 for rho_a = rho_0', mp.mpf(str(c2)))
            Phi = sp.Rational(2 * (N + 1), N) * (C1 + (2 * N + 1) * C3) * eta * C4 * sp.cos(N * zeta)
            # covariant components of B = H grad zeta + grad Phi are g_{rho zeta}, g_{zeta zeta},
            # g_{eta zeta}
            cov = [sp.diff(E['X'], aa).dot(B) for aa in q]
            tgt = [sp.diff(Phi, rho), H + sp.diff(Phi, zeta), sp.diff(Phi, eta)]
            f = sp.lambdify(q, [u - v for u, v in zip(cov, tgt)], 'mpmath')
            for _ in range(args.points):
                pt = (mp.mpf(1) + mp.mpf(rng.uniform(-0.03, 0.03)), mp.mpf(rng.uniform(0, 6.283)),
                      mp.mpf(rng.uniform(-0.03, 0.03)))
                record('D B = H grad zeta + grad Phi (19)-(20)', norm(f(*pt)))
        print(f'checked {label:16s} N={N} k={k:2d} s={s:2d} rho_a={rhoa}', flush=True)

    print('\nworst residuals (tolerance 1e-25):')
    for name, val in worst.items():
        print(f'  {name:45s} {mp.nstr(val, 3)}')
    print('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
