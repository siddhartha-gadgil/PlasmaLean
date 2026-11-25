"""Replay one widened pair of pilot reference tubes covering the whole upper radial bracket."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path

from bounce_frame_witness import DEFAULT_WITNESS, FRAME_SCALE, SCALE, STEP, encode_step
from bounce_mirror_pilot import HEIGHTS, Model, angle_models, evaluate, quotient_range
from bounce_phase_frame import check_frame_step
from bounce_common_section import section_polynomial_data
from bounce_phase_strength import ShiftedStrength
from verify_physical_trace_slabs import digest, save


def interpolate(a, b, u):
    """Round a convex combination of same-scale signed integers to its nearest dyadic tick."""
    if isinstance(a, list):
        return [interpolate(x, y, u) for x, y in zip(a, b, strict=True)]
    return round((1-u)*a + u*b)


def run(seed, part, other, mix, width, stop, data):
    sign = part["direction"]
    radius = SCALE * width
    if radius.denominator != 1:
        raise ValueError("the seed radius must be exactly representable at precision 80")
    radius = int(radius)
    previous = seed
    start = [[FRAME_SCALE, 0], [0, FRAME_SCALE]]
    shifted = ShiftedStrength(data)
    rows = []
    for i, row in enumerate(part["steps"][:stop]):
        other_row = other["steps"][i]
        nominal = [Model(poly) for poly in interpolate(row["coefficients"],other_row["coefficients"],mix)]
        angles = angle_models(sign * (F(i) + F(1, 2)) * STEP, sign * STEP / 2, F(0))
        end = interpolate(row["frame_end"],other_row["frame_end"],mix)
        try:
            step = check_frame_step(data, angles, nominal, previous, radius, start, end, i, sign, STEP, F(0))
        except ArithmeticError as exc:
            return {"direction": sign, "rows": rows, "failed_index": i, "failure": str(exc)}
        seg = step.segment
        tube, harmonic, values = seg.fields(data)
        gaps, (r16, *_) = shifted.calculate(tube, harmonic, values, HEIGHTS[1:])
        lo, hi = quotient_range(gaps[0], r16)
        result = {"index": i, "gap": [str(lo), str(hi)], "position": encode_step(step, end)}
        if lo <= 0 <= hi:
            grads = [[evaluate(p, tube, harmonic)[0] for p in field[1:]] for field in data]
            _, slopes = shifted.geometry(data, harmonic, tube, values, grads, sign, True)
            result["outward_slope"] = list(map(str, slopes))
        rows.append(result)
        previous = [p.endpoint(1) for p in nominal]
        start, radius = end, step.outgoing
    return {"direction": sign, "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed-radius", type=F, default=F(1, 65536))
    parser.add_argument("--tiles", type=int, default=4)
    parser.add_argument("--indices", type=int, nargs="+")
    parser.add_argument("--stop", type=int, default=352)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    indices = list(range(args.tiles)) if args.indices is None else args.indices
    if not (0 < args.seed_radius and 1 <= args.stop <= 391 and args.tiles >= 1
            and indices and all(0 <= i < args.tiles for i in indices)):
        parser.error("expected a positive seed radius and at most 391 ground reference slabs")
    outer = DEFAULT_WITNESS.with_name("bounce_frame_q0_u478.json.gz")
    endpoints = []
    for path in (DEFAULT_WITNESS,outer):
        with gzip.open(path) as stream:
            endpoints.append(json.load(stream))
    inner,outer_packet = endpoints
    data = section_polynomial_data(0)
    result = {"endpoints": [digest(DEFAULT_WITNESS),digest(outer)], "tiles": args.tiles,
              "seed_radius": str(args.seed_radius), "height": str(HEIGHTS[1]), "traces": []}
    for index in indices:
        mix = F(2*index+1,2*args.tiles)
        seed = interpolate(*[[p[0] for p in pkt["seed_center_radius"]] for pkt in endpoints],mix)
        for part, other in zip(inner["traces"],outer_packet["traces"],strict=True):
            trace = run(seed, part, other, mix, args.seed_radius, args.stop, data)
            trace.update(tile=index,seed_center=seed)
            result["traces"].append(trace)
            save(args.output, result)
            uncertain = [r for r in trace["rows"] if "outward_slope" in r]
            above = [r["index"] for r in trace["rows"] if F(r["gap"][0]) > 0]
            print(f'tile {index}, {trace["direction"]:+}: rows {len(trace["rows"])}, '
                  f'first upper slab {above[:1]}, uncertain {[r["index"] for r in uncertain]}, '
                  f'positive outward slopes {all(F(r["outward_slope"][0]) > 0 for r in uncertain)}', flush=True)


if __name__ == "__main__":
    main()
