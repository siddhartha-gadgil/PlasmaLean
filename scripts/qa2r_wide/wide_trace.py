"""Reference line and frames of the label-0.474 forward trace (N-216 stage 3 pilot).

UNTRUSTED proposal data: a float integration of the candidate field proposes dyadic
polynomial references and dyadic frame matrices for every 1/64 slab, exactly as
``enclosure_pilot.references`` does. Nothing here is a bound; every later certificate
treats these integers as given input. Inputs are repository files only (the candidate and
the two torus seeds read by ``bounce_screen.load_inputs``).

    OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/wide_trace.py
"""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
DEFAULT = RESULTS / "trace_u474_forward.json"


def build(label, count):
    import enclosure_pilot as proto

    rows = []
    for index, nominal, _, start, end, _ in proto.references(float(label), 1, set(range(count))):
        rows.append(dict(index=index, coefficients=[list(map(int, x.a)) for x in nominal],
                         frame_start=[list(map(int, r)) for r in start],
                         frame_end=[list(map(int, r)) for r in end]))
    return dict(format="QA2RWideTrace/v1", label=str(label), direction=1, phase=0, step="1/64",
                order=7, coordinate_denominator=2**80, frame_denominator=2**40, slabs=rows)


def load(path=DEFAULT):
    data = json.loads(Path(path).read_text())
    if data["format"] != "QA2RWideTrace/v1" or [r["index"] for r in data["slabs"]] != list(
            range(len(data["slabs"]))):
        raise ValueError("unexpected trace file")
    for before, after in zip(data["slabs"], data["slabs"][1:]):
        if before["frame_end"] != after["frame_start"]:
            raise ValueError("frames of adjacent slabs do not agree")
    return data


if __name__ == "__main__":
    import sys

    sys.path.insert(0, str(HERE))
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--label", type=F, default=F(474, 1000))
    parser.add_argument("--count", type=int, default=332)
    parser.add_argument("--output", type=Path, default=DEFAULT)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(build(args.label, args.count)))
    print(args.output, len(load(args.output)["slabs"]))
