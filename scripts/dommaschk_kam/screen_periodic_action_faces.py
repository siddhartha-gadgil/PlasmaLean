"""Test the phase-zero upper-height radial strip at its opposite symmetry section."""
import argparse
from fractions import Fraction
from pathlib import Path
import json

from bounce_action_pilot import TARGET, enclose_action
from bounce_common_section import common_section_inputs
from bounce_mirror_pilot import HEIGHTS
from bounce_phase_frame import check_frame, framed_segments
from bounce_phase_strength import ShiftedStrength, check_shifted_strength
from bounce_screen import FIELD_FILE_SHA, SEEDS


def intervals():
    return [(Fraction(i, 1000), Fraction(i + 1, 1000)) for i in range(470, 476)] + [
        (Fraction(476, 1000), Fraction(478, 1000))]


def cover_report(reports):
    if len(reports) != len(intervals()):
        raise ValueError("incomplete opposite-section radial cover")
    for (lower, upper), report in zip(intervals(), reports, strict=True):
        if list(map(Fraction, report["radius"])) != [lower, upper]:
            raise ValueError("changed arc or radial endpoints")
        if (report["section_in_half_pi"] != 1 or Fraction(report["height"]) != HEIGHTS[1]
                or Fraction(report["target"]) != TARGET
                or Fraction(report["phase_half_width"]) != Fraction(1, 2**19)
                or report["field_sha256"] != FIELD_FILE_SHA
                or report["seed_sha256"] != {k: a[1] for k, a in SEEDS.items()}):
            raise ValueError("different physical family or field")
        enclosure = report["enclosure"]
        bound = Fraction(enclosure["action_bounds"][1][0])
        if (bound != Fraction(report["lower_bound"]) or bound - TARGET != Fraction(report["margin"])
                or bound <= TARGET + Fraction(3, 2000) or
                [hit["direction"] for hit in enclosure["crossings"] if hit["success"]] != [-1, 1]):
            raise ValueError("unverified action margin or an unclosed signed first well")
    return {"kind": "external directed interval enclosure", "tiles": reports,
            "minimum_margin": str(min(Fraction(row["margin"]) for row in reports))}


def enclose(lower, upper, phase_width, step, panels):
    if not Fraction(47, 100) <= lower <= upper <= Fraction(239, 500):
        raise ValueError("expected a closed interval in the original phase-zero bracket")
    if phase_width < 0 or step <= 0 or panels < 1:
        raise ValueError("invalid phase width, integration step or panel count")
    check_frame()
    check_shifted_strength()
    inputs, transfer = common_section_inputs(
        phase_width, (upper - lower) / 2, (upper + lower) / 2, 1)
    enclosure = enclose_action(
        inputs, step, panels, Fraction(0), Fraction(49, 8), ShiftedStrength(inputs[0]),
        segment_builder=framed_segments)
    bound = Fraction(enclosure["action_bounds"][1][0])
    return {
        "section_in_half_pi": 1, "phase_half_width": str(phase_width),
        "radius": [str(lower), str(upper)], "height": str(HEIGHTS[1]),
        "target": str(TARGET), "lower_bound": str(bound), "margin": str(bound - TARGET),
        "field_sha256": FIELD_FILE_SHA, "seed_sha256": {k: a[1] for k, a in SEEDS.items()},
        "transfer": transfer, "enclosure": enclosure,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lower", type=Fraction, default=Fraction(47, 100))
    parser.add_argument("--upper", type=Fraction, default=Fraction(47, 100))
    parser.add_argument("--cover", action="store_true",
                        help="recompute all seven consecutive tiles using their original parameters")
    parser.add_argument("--phase-half-width", type=Fraction, default=Fraction(1, 2**19))
    parser.add_argument("--step", type=Fraction, default=Fraction(1, 64))
    parser.add_argument("--panels", type=int, default=24)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.cover:
        report = cover_report([enclose(a, b, Fraction(1, 2**19), Fraction(1,64), 24)
                               for a, b in intervals()])
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(f"verified minimum external lower margin {report['minimum_margin']}")
        return
    report = enclose(args.lower, args.upper, args.phase_half_width, args.step, args.panels)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if Fraction(report["margin"]) <= 0:
        raise SystemExit("strict opposite-face action excess unresolved")
    print(f"verified external lower margin {report['margin']}")


if __name__ == "__main__":
    main()
