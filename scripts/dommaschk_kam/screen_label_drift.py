"""UNTRUSTED float screen: first-order guiding-centre drift of field-line labels on the QA2R sector.

For births on the original launch line (phase 0, interpolation label u between tori C and A) and
the mirror height h, trace the QA2R field line through the first well, and integrate the vacuum
drift velocity pulled back to the section phi = 0:

    dx/dtau = sqrt(1 - B/h) b  +  eps * G(x),   G = (2h - B) / (2 h B^3)  B x grad|B|,

in units of the major-radius scale R0 and of R0/v (v the particle speed), eps = m v / (q B0 R0).
Labels are the section coordinates (R0, z0) of the field line through the guiding centre.
Reported per half bounce, as coefficients of eps: the largest label excursion inside the well
(banana amplitude) and the net displacement (precession). Nothing here is a proof.
"""
import argparse
import json

import numpy as np
from scipy.integrate import solve_ivp

import bounce_mirror_pilot as pilot

LEVEL = 5300546391395933 / 5000000000000000
TARGET = 6799610938322487 / 5000000000000000


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--labels", type=float, nargs="+", default=[0.470, 0.474, 0.478])
    parser.add_argument("--height", type=float, default=LEVEL)
    parser.add_argument("--output")
    args = parser.parse_args()
    ev, seeds = pilot.load_inputs()
    c, a = [pilot.seed_cut(*s, np.array([0.0]))[0][:, 0] for s in seeds]
    h = args.height

    def bcyl(R, phi, z):
        return np.array([float(x) for x in ev.B_cyl(R, phi, z)])

    def norm(R, phi, z):
        return float(np.linalg.norm(bcyl(R, phi, z)))

    def grad_norm(R, phi, z, d=1e-6):
        return np.array([(norm(R + d, phi, z) - norm(R - d, phi, z)) / (2 * d),
                         (norm(R, phi + d, z) - norm(R, phi - d, z)) / (2 * d * R),
                         (norm(R, phi, z + d) - norm(R, phi, z - d)) / (2 * d)])

    def line(phi, y):
        B = bcyl(y[0], phi, y[1])
        return np.array([y[0] * B[0] / B[1], y[0] * B[2] / B[1]])

    def rhs(phi, y):  # field line and its variational matrix (columns)
        f = line(phi, y[:2])
        d = 1e-6
        jac = np.column_stack([(line(phi, y[:2] + d * e) - line(phi, y[:2] - d * e)) / (2 * d)
                               for e in np.eye(2)])
        return np.concatenate([f, (jac @ y[2:].reshape(2, 2)).ravel()])

    def hit(phi, y):
        return norm(y[0], phi, y[1]) - h
    hit.terminal = True

    rows = []
    for u in args.labels:
        start = np.concatenate([c + u * (a - c), np.eye(2).ravel()])
        legs = [solve_ivp(rhs, (0, s * 8), start, method="DOP853", rtol=1e-11, atol=1e-13,
                          events=hit, dense_output=True) for s in (-1, 1)]
        left, right = legs[0].t_events[0][0], legs[1].t_events[0][0]

        def state(phi):
            return (legs[0] if phi < 0 else legs[1]).sol(phi)

        # phi = mid + half sin(theta) removes the inverse square-root endpoint singularity
        mid, half = (left + right) / 2, (right - left) / 2
        n = 4000
        theta = (np.arange(n) + 0.5) * np.pi / n - np.pi / 2
        action = time = 0.0
        drift = np.zeros(2)
        banana = np.zeros(2)
        for th in theta:
            phi = mid + half * np.sin(th)
            y = state(phi)
            R, z = y[0], y[1]
            B = bcyl(R, phi, z)
            nb = np.linalg.norm(B)
            arc = nb * R / B[1]                       # d(length)/d(phi) along the field line
            weight = half * np.cos(th) * np.pi / n * arc
            gap = max(h - nb, 0.0)
            action += weight * np.sqrt(2 * gap)
            g = (2 * h - nb) / (2 * h * nb ** 3) * np.cross(B, grad_norm(R, phi, z))
            fl = line(phi, y[:2])
            planar = np.array([g[0], g[2]]) - g[1] / R * fl  # remove motion along the field line
            rate = np.linalg.solve(y[2:].reshape(2, 2), planar)
            dt = weight / np.sqrt(max(gap, 1e-300) / h)
            time += dt
            drift += rate * dt
            banana = np.maximum(banana, np.abs(drift))
        rows.append(dict(u=u, birth=list(c + u * (a - c)), well=[left, right], action=action,
                         half_bounce_time=time, banana_per_eps=list(banana),
                         net_per_eps=list(drift)))
        print(json.dumps(rows[-1]), flush=True)
    # Label width of the certified phase window |phi| <= 2^-19 on the middle launch line.
    d = 1e-4
    mid_u = (args.labels[0] + args.labels[-1]) / 2
    cuts = [[pilot.seed_cut(*s, np.array([p]))[0][:, 0] for s in seeds] for p in (-d, d)]
    chart = [cc + mid_u * (aa - cc) for cc, aa in cuts]
    base = c + mid_u * (a - c)
    skew = (chart[1] - chart[0]) / (2 * d) - line(0.0, base)
    window = float(np.linalg.norm(skew)) / 2 ** 19
    field_at_birth = norm(base[0], 0.0, base[1])
    width = float(np.linalg.norm((a - c) * (args.labels[-1] - args.labels[0])))
    slope = (rows[-1]["action"] - rows[0]["action"]) / width
    summary = dict(target=TARGET, height=h, strip_width=width, action_slope_per_length=slope,
                   torus_gap=float(np.linalg.norm(a - c)), phase_window_label=window,
                   field_at_birth=field_at_birth, rows=rows)
    print(json.dumps({k: v for k, v in summary.items() if k != "rows"}))
    if args.output:
        with open(args.output, "w") as out:
            json.dump(summary, out, indent=1)


if __name__ == "__main__":
    main()
