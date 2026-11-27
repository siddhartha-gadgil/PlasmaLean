"""UNTRUSTED float scan of the QA2R field on the whole spatial envelope, for all angles.

Envelope: 7/8 <= R <= 1, |z| <= 5/64 (`DommaschkSignedTraceDomain.Region`), phi in [0, pi] (the
field has two field periods). Reports the suprema that the certified bounds of
`PlasmaLean/Design/DommaschkRegionFieldBounds.lean` must dominate: the planar field-line speed
R sqrt(B_R^2 + B_z^2) / B_phi, the range of |B| and of B_phi, and the norm of grad |B| (central
differences). Nothing here is a proof.

    cd scripts/dommaschk_kam && ../../.venv-ws/bin/python ../qa2r_wide/scan_region_bounds.py
"""
import argparse
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "dommaschk_kam"))
import bounce_mirror_pilot as pilot  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--nr", type=int, default=81)
    parser.add_argument("--nphi", type=int, default=241)
    parser.add_argument("--nz", type=int, default=81)
    parser.add_argument("--output")
    args = parser.parse_args()
    ev, _ = pilot.load_inputs()

    def field(R, phi, z):
        return [np.asarray(x, dtype=float) for x in ev.B_cyl(R, phi, z)]

    def strength(R, phi, z):
        a, b, c = field(R, phi, z)
        return np.sqrt(a * a + b * b + c * c)

    R, P, Z = np.broadcast_arrays(np.linspace(7 / 8, 1, args.nr)[:, None, None],
                                  np.linspace(0, np.pi, args.nphi)[None, :, None],
                                  np.linspace(-5 / 64, 5 / 64, args.nz)[None, None, :])
    BR, BP, BZ = field(R, P, Z)
    norm = np.sqrt(BR**2 + BP**2 + BZ**2)
    speed = R * np.sqrt(BR**2 + BZ**2) / BP
    d = 1e-5
    grad = np.sqrt(((strength(R + d, P, Z) - strength(R - d, P, Z)) / (2 * d))**2
                   + ((strength(R, P + d, Z) - strength(R, P - d, Z)) / (2 * d * R))**2
                   + ((strength(R, P, Z + d) - strength(R, P, Z - d)) / (2 * d))**2)

    def where(a, k):
        return [float(R.flat[k]), float(P.flat[k]), float(Z.flat[k])]

    over = grad.max(axis=1) > 2  # (R, z) columns where the gradient exceeds 2 at some angle
    result = {
        "grid": [args.nr, args.nphi, args.nz],
        "speed_max": float(speed.max()), "speed_argmax": where(speed, speed.argmax()),
        "strength_min": float(norm.min()), "strength_max": float(norm.max()),
        "toroidal_min": float(BP.min()), "toroidal_max": float(BP.max()),
        "grad_strength_max": float(grad.max()), "grad_argmax": where(grad, grad.argmax()),
        "grad_over_b2_max": float((grad / norm**2).max()),
        "fraction_of_RZ_columns_with_grad_above_2": float(over.mean()),
        "grad_max_by_R": {f"{float(R[i, 0, 0]):.4f}": float(grad[i].max())
                          for i in range(0, args.nr, max(1, (args.nr - 1) // 8))},
        "grad_max_by_abs_z": {f"{float(abs(Z[0, 0, k])):.4f}": float(grad[:, :, k].max())
                              for k in range(0, args.nz, max(1, (args.nz - 1) // 8))},
    }
    text = json.dumps(result, indent=1)
    print(text)
    if args.output:
        Path(args.output).write_text(text + "\n")


if __name__ == "__main__":
    main()
