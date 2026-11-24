"""Sample the two variation inputs in the launch-connected wells at two QA2R radial labels."""

import argparse
import json
from pathlib import Path

import numpy as np

from bounce_radial_variation import HEIGHT, variation_trace
from bounce_screen import FIELD_FILE_SHA, SEEDS, load_inputs


RADII = (0.470, 0.478)
ANGLES = np.array([-2.0 ** -19, 0.0, 2.0 ** -19])


def launch_component(field, height):
    """Include one sample past each first mirror to test the edges of the estimate."""
    center = len(field) // 2
    inside = field < height
    if not inside[center]:
        raise ValueError('launch is outside the well')
    left = np.flatnonzero(~inside[:center])
    right = np.flatnonzero(~inside[center + 1:])
    if not len(left) or not len(right):
        raise ValueError('trace does not bracket both mirrors')
    return slice(left[-1], center + right[0] + 2)


def screen():
    evaluator, seeds = load_inputs()
    rows = []
    for steps, tolerance in ((512, 2e-11), (2048, 2e-12)):
        _, signals = variation_trace(evaluator, seeds, np.asarray(RADII), ANGLES, steps, tolerance)
        for radius, pieces in zip(RADII, signals, strict=True):
            for height in HEIGHT:
                extremes = []
                for piece in pieces:
                    field, weight, dfield, dweight = piece.T
                    interval = launch_component(field, height)
                    ratio = (dweight / weight)[interval]
                    strength = dfield[interval]
                    extremes.append((ratio.min(), ratio.max(), strength.min(), strength.max()))
                extremes = np.asarray(extremes)
                rows.append(dict(steps_per_direction=steps, tolerance=tolerance, radius=radius,
                                 height=float(height), min_log_weight=float(extremes[:, 0].min()),
                                 max_log_weight=float(extremes[:, 1].max()),
                                 min_strength_derivative=float(extremes[:, 2].min()),
                                 max_strength_derivative=float(extremes[:, 3].max())))
    return dict(status='floating-point screen of the launch-connected component',
                field_sha256=FIELD_FILE_SHA, seed_sha256={k: value[1] for k, value in SEEDS.items()},
                angles=ANGLES.tolist(), rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(screen(), indent=2, allow_nan=False) + '\n'
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end='')
