"""Untrusted scoping numbers for the tube label of N-216 (stage 2b and 4).

Along the forward wide trace of label 0.474 this prints, for several chain lengths n: the
extent of the trial tube, the range of |B|, of the gradient of |B| and of the planar field-line
speed on it, the label constant C = exp(sum mu/64) * max ||M^-1||, and the resulting horizon of
the direct drift bound for a given epsilon. Double precision, no validation.

    OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/scope_label.py
"""
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "dommaschk_kam"))
import bounce_mirror_pilot as pilot  # noqa: E402

TRIAL = 362677745884388752412 / 2 ** 80


def main():
    ev, _ = pilot.load_inputs()
    trace = json.loads((HERE / "results/trace_u474_forward.json").read_text())
    mus = [float(x) for x in (HERE.parents[1] / "generated/qa2r_wide/certified_mu.txt").read_text().split()
           if x.replace(".", "").replace("/", "").isdigit() or "/" in x or "." in x][-332:] \
        if False else None
    den, fden = trace["coordinate_denominator"], trace["frame_denominator"]

    def bcyl(R, phi, z):
        return np.array([float(x) for x in ev.B_cyl(R, phi, z)])

    def norm(R, phi, z):
        return float(np.linalg.norm(bcyl(R, phi, z)))

    def grad(R, phi, z, d=1e-6):
        return np.array([(norm(R + d, phi, z) - norm(R - d, phi, z)) / (2 * d),
                         (norm(R, phi + d, z) - norm(R, phi - d, z)) / (2 * d * R),
                         (norm(R, phi, z + d) - norm(R, phi, z - d)) / (2 * d)])

    rows = []
    for slab in trace["slabs"]:
        k = slab["index"]
        cx, cz = [np.array(c, float) / den for c in slab["coefficients"]]
        m0, m1 = [np.array(m, float) / fden for m in (slab["frame_start"], slab["frame_end"])]
        best = dict(k=k, Rmin=9, Rmax=0, zmax=0, Bmin=9, Bmax=0, g=0, gB2=0, speed=0, inv=0, op=0)
        for tau in (-1.0, 0.0, 1.0):
            phi = (k + (tau + 1) / 2) / 64
            y = np.array([np.polyval(cx[::-1], tau), np.polyval(cz[::-1], tau)])
            M = (m0 * (1 - tau) + m1 * (1 + tau)) / 2
            sv = np.linalg.svd(M, compute_uv=False)
            best["inv"], best["op"] = max(best["inv"], 1 / sv[-1]), max(best["op"], sv[0])
            for ang in np.linspace(0, 2 * np.pi, 8, endpoint=False):
                for rad in (0.0, TRIAL):
                    R, z = y + M @ (rad * np.array([np.cos(ang), np.sin(ang)]))
                    B = bcyl(R, phi, z)
                    nb = float(np.linalg.norm(B))
                    g = float(np.linalg.norm(grad(R, phi, z)))
                    best.update(Rmin=min(best["Rmin"], R), Rmax=max(best["Rmax"], R),
                                zmax=max(best["zmax"], abs(z)), Bmin=min(best["Bmin"], nb),
                                Bmax=max(best["Bmax"], nb), g=max(best["g"], g),
                                gB2=max(best["gB2"], g / nb ** 2),
                                speed=max(best["speed"], float(np.hypot(R * B[0] / B[1], R * B[2] / B[1]))))
                    if rad == 0.0:
                        break
        rows.append(best)
    mu = [float(eval(x)) for x in (HERE.parents[1] / "generated/qa2r_wide/certified_mu.txt").read_text().split()[-332:]] \
        if False else None
    out = []
    for n in (64, 110, 166, 220, 332):
        part = rows[:n]
        agg = dict(n=n, angle=n / 64, Rmin=min(r["Rmin"] for r in part), Rmax=max(r["Rmax"] for r in part),
                   zmax=max(r["zmax"] for r in part), Bmin=min(r["Bmin"] for r in part),
                   Bmax=max(r["Bmax"] for r in part), grad=max(r["g"] for r in part),
                   gradB2=max(r["gB2"] for r in part), speed=max(r["speed"] for r in part),
                   inverse=max(r["inv"] for r in part), op=max(r["op"] for r in part))
        out.append(agg)
        print(json.dumps(agg))
    (HERE / "results/scope_label.json").write_text(json.dumps(dict(slabs=rows, lengths=out), indent=1))


if __name__ == "__main__":
    main()
