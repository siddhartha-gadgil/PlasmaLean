#!/usr/bin/env python3
"""Rotational transform and on-axis field strength of the equilibria of arXiv:2611.07672
(untrusted numerics for note N-43; see check_equilibria.py for the formulas).

Every field line is the closed curve zeta -> x(rho, zeta, eta). Its number of poloidal turns
around the magnetic axis per toroidal turn is the Gauss linking number of the line with the axis
(the axis winds once around the z-axis). The script evaluates the Gauss integral by the
midpoint rule and reports the nearest integer, to be compared with the paper's iota = 0 or
iota = -s N. It also reports the relative variation of |B| along the axis.

The sign of the linking number depends on the orientation convention; with the one used here
the paper's iota = -s N appears as +s N.

usage: check_iota.py [--n 12000]
"""
import argparse
import numpy as np
import sympy as sp
from check_equilibria import build, rho, zeta, eta


def curve(E, r, e, n):
    Xc = E['X'].subs({rho: r, eta: e}).evalf(20)      # numerical coefficients, exact in zeta
    f = sp.lambdify(zeta, list(Xc), 'numpy')
    t = (np.arange(n) + 0.5) * 2 * np.pi / n
    P = np.array([np.broadcast_to(c, t.shape) for c in f(t)]).T
    df = sp.lambdify(zeta, list(sp.diff(Xc, zeta)), 'numpy')
    D = np.array([np.broadcast_to(c, t.shape) for c in df(t)]).T
    return P, D


def linking(P1, D1, P2, D2, chunk=500):
    n1, n2 = len(P1), len(P2)
    total = 0.0
    for a in range(0, n1, chunk):
        R = P1[a:a + chunk, None, :] - P2[None, :, :]
        cr = np.cross(D1[a:a + chunk, None, :], D2[None, :, :])
        total += (np.einsum('ijk,ijk->ij', R, cr) / np.linalg.norm(R, axis=2) ** 3).sum()
    return total * (2 * np.pi / n1) * (2 * np.pi / n2) / (4 * np.pi)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=12000)
    args = ap.parse_args()
    one = sp.Integer(1)
    cases = [('F1 rho_a=rho_0', N, 1, one, 1, 0) for N in (1, 2, 3, 4, 5)]
    cases += [('F1 rho_a>rho_0', N, 1, sp.Rational(11, 10), s, 0) for N in (1, 3) for s in (1, -1)]
    cases += [('F2 small rho_a', N, 0, sp.Rational(3, 4), 1, 0) for N in (2, 3, 4, 5)]
    cases += [('F2 large rho_a', 3, 0, sp.Rational(112, 100), 1, 3),
              ('F2 large rho_a', 3, 0, sp.Rational(112, 100), -1, -3),
              ('F2 large rho_a', 5, 0, sp.Rational(104, 100), 1, 5)]
    cases += [('F3', 3, -1, sp.Rational(97, 100), 1, 3), ('F3', 3, -1, sp.Rational(97, 100), -1, -3),
              ('F3', 4, -1, sp.Rational(89, 100), 1, 4), ('F3', 5, -1, sp.Rational(88, 100), 1, 5)]
    ok = True
    print(f'{"case":16s} {"N":>2s} {"s":>2s} {"rho_a":>7s} {"linking":>9s} {"s N|0":>6s}'
          f' {"|B| axis variation":>20s}')
    for label, N, k, rhoa, s, expect in cases:
        E = build(N, k, one, rhoa, s)
        ra = float(rhoa)
        Pa, Da = curve(E, ra, 0.0, args.n)
        Pl, Dl = curve(E, ra, 4e-3, args.n + 7)   # a field line displaced from the axis in eta
        lk = linking(Pl, Dl, Pa, Da)
        Bn = np.linalg.norm(Da, axis=1)
        var = (Bn.max() - Bn.min()) / Bn.mean()
        good = abs(lk - expect) < 0.05
        ok &= good
        print(f'{label:16s} {N:2d} {s:2d} {ra:7.3f} {lk:9.4f} {expect:6d} {var:20.3e}'
              f' {"" if good else "MISMATCH"}')
    print('ALL IOTA CHECKS PASSED' if ok else 'SOME IOTA CHECK FAILED')
    raise SystemExit(0 if ok else 1)


if __name__ == '__main__':
    main()
