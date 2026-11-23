"""Reproduce the integer jet boxes in DommaschkInterfaceArcGeometry.lean.

Use the single-cell, degree-four profile of interface_arc.py. The interval
arithmetic here is exact rational. Each face is rounded out to a 2^-16 grid
and extended by one grid unit to leave slack for composing enclosures.
"""

import argparse
from math import ceil, floor
from pathlib import Path

from interface_arc import END, Interval, jet_enclosure, point, read_jets


JETS = [
    ("radius", "R", 0, 0),
    ("rθ", "R", 1, 0), ("rφ", "R", 0, 1),
    ("zθ", "z", 1, 0), ("zφ", "z", 0, 1),
    ("rθθ", "R", 2, 0), ("rθφ", "R", 1, 1), ("rφφ", "R", 0, 2),
    ("zθθ", "z", 2, 0), ("zθφ", "z", 1, 1), ("zφφ", "z", 0, 2),
]


def definitions():
    jets = read_jets(4)
    boxes = [("leftBox", point(0)), ("rightBox", point(END)), ("arcBox", Interval(0, END))]
    blocks = []
    for name, phi in boxes:
        lines = [f"def {name} : Jet → FIv"]
        for key, profile, a, b in JETS:
            interval = jet_enclosure(jets[profile, a, b], phi)
            lo = floor(interval.lo * 2**16) - 1
            hi = ceil(interval.hi * 2**16) + 1
            lines.append(f"  | .{key} => gridBox ({lo}) ({hi})")
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the Lean file against regeneration")
    args = parser.parse_args()
    data = definitions()
    if args.check:
        lean = Path(__file__).resolve().parents[2] / "PlasmaLean/Design/DommaschkInterfaceArcGeometry.lean"
        if data not in lean.read_text():
            raise SystemExit("Lean jet table differs from regenerated table")
    else:
        print(data)
