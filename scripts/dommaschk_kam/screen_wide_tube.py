"""UNTRUSTED float screen: how wide a tube can one field-line trace of the QA2R well carry?

In the frame of the variational matrix M along the reference line y through the birth
(phase 0, label u), a nearby line is x = y + M v and

    dv/dphi = M^-1 (F(y + M v) - F(y) - J(y) M v),   Jacobian  A(phi, v) = M^-1 (J(y + M v) - J(y)) M.

For |v| <= rho the extreme eigenvalues of the symmetric part of A bound the growth of the
distance between two lines in both directions. The label (section point at phi = 0) then has
Lipschitz constant at most  |M^-1(phi)| exp(int_0^phi -mu_min).  The screen samples A on the
ball and reports, per rho: the largest |mu|, the two integrals over the half well, the
resulting label Lipschitz constant and the largest physical tube radius |M| rho.
Nothing here is a proof; a certificate must enclose A on the whole ball.
"""
import argparse
import json

import numpy as np
from scipy.integrate import solve_ivp

import bounce_mirror_pilot as pilot

LEVEL = 5300546391395933 / 5000000000000000


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", type=float, default=0.474)
    parser.add_argument("--radii", type=float, nargs="+", default=[1e-5, 1e-4, 3e-4, 1e-3, 3e-3])
    parser.add_argument("--steps", type=int, default=332, help="slabs of 1/64 radian per direction")
    parser.add_argument("--output")
    args = parser.parse_args()
    ev, seeds = pilot.load_inputs()
    c, a = [pilot.seed_cut(*s, np.array([0.0]))[0][:, 0] for s in seeds]

    def line(phi, y):
        B = [float(x) for x in ev.B_cyl(y[0], phi, y[1])]
        return np.array([y[0] * B[0] / B[1], y[0] * B[2] / B[1]])

    def jac(phi, y, d=1e-6):
        return np.column_stack([(line(phi, y + d * e) - line(phi, y - d * e)) / (2 * d)
                                for e in np.eye(2)])

    def rhs(phi, y):
        return np.concatenate([line(phi, y[:2]), (jac(phi, y[:2]) @ y[2:].reshape(2, 2)).ravel()])

    start = np.concatenate([c + args.label * (a - c), np.eye(2).ravel()])
    directions = [np.array([np.cos(t), np.sin(t)]) for t in np.arange(8) * np.pi / 4]
    rows = []
    for rho in args.radii:
        worst = dict(rho=rho, mu_abs_max=0.0, tube=0.0, lipschitz=0.0)
        for sign in (-1, 1):
            end = sign * args.steps / 64
            sol = solve_ivp(rhs, (0, end), start, method="DOP853", rtol=1e-11, atol=1e-13,
                            dense_output=True)
            grid = np.linspace(0, end, 2 * args.steps + 1)
            upper = lower = 0.0
            for i, phi in enumerate(grid):
                y = sol.sol(phi)
                M = y[2:].reshape(2, 2)
                Minv = np.linalg.inv(M)
                J0 = jac(phi, y[:2])
                hi, lo = 0.0, 0.0
                for scale in (0.5, 1.0):
                    for d in directions:
                        A = Minv @ (jac(phi, y[:2] + M @ (scale * rho * d)) - J0) @ M
                        eig = np.linalg.eigvalsh((A + A.T) / 2)
                        hi, lo = max(hi, eig[-1]), min(lo, eig[0])
                if i:
                    step = abs(grid[i] - grid[i - 1])
                    upper += hi * step
                    lower += -lo * step
                worst["mu_abs_max"] = max(worst["mu_abs_max"], hi, -lo)
                worst["tube"] = max(worst["tube"], np.linalg.norm(M, 2) * rho)
                worst["lipschitz"] = max(worst["lipschitz"],
                                         np.linalg.norm(Minv, 2) * np.exp(lower))
            worst["growth_forward" if sign > 0 else "growth_backward"] = float(np.exp(upper))
        rows.append({k: float(v) for k, v in worst.items()})
        print(json.dumps(rows[-1]), flush=True)
    if args.output:
        with open(args.output, "w") as out:
            json.dump(dict(label=args.label, steps=args.steps, rows=rows), out, indent=1)


if __name__ == "__main__":
    main()
