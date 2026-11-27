"""Backward radii for the tube label on a prefix of the wide-tube forward chain (N-216).

Reads the generated records `generated/qa2r_wide/WideTube/<Group>.lean` and returns, for the
first `count` slabs, natural numbers b_0 > b_1 > ... (units 2^-80) accepted by
`DommaschkTubeCheck.radiiCheck`: b_0 - jump_0 = trial_0 - 1 and
64 b_{k+1} + 2^80 defect_k <= (b_k - jump_k)(64 - max(0, mu_k)).
"""
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ROW = re.compile(r"def row(\d+) : Step :=\s*⟨\[[^\]]*\], \[[^\]]*\],\s*⟨[^⟩]*⟩, ⟨[^⟩]*⟩,\s*"
                 r"(\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+),\s*"
                 r"\(([^)]*)\), \(([^)]*)\), \(([^)]*)\), \(([^)]*)\)⟩")


def records(group="DommaschkWideTubeRows000"):
    text = (ROOT / "generated/qa2r_wide/WideTube" / (group + ".lean")).read_text()
    rows = {}
    for m in ROW.finditer(text):
        k = int(m.group(1))
        jump, incoming, outgoing, trial = (int(m.group(i)) for i in (2, 3, 4, 5))
        det, op, mu, defect = (Fraction(m.group(i)) for i in (9, 10, 11, 12))
        rows[k] = dict(jump=jump, incoming=incoming, outgoing=outgoing, trial=trial, det=det, op=op,
                       mu=mu, defect=defect)
    return [rows[k] for k in range(len(rows))]


def radii(rows, count):
    b = [rows[0]["trial"] - 1 + rows[0]["jump"]]
    for r in rows[:count]:
        g = max(Fraction(0), r["mu"])
        assert r["jump"] <= b[-1] and b[-1] - r["jump"] < r["trial"]
        nxt = ((b[-1] - r["jump"]) * (64 - g) - 2 ** 80 * r["defect"]) / 64
        b.append(nxt.numerator // nxt.denominator)
    return b


if __name__ == "__main__":
    import math
    import sys
    rows = records()
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 224
    b = radii(rows, n)
    part = rows[:n]
    expo = sum(max(Fraction(0), r["mu"]) / 64 for r in part)
    binv = max(r["op"] / r["det"] for r in part)
    print("slabs", n, "b0", b[0] / 2 ** 80, "b_end", b[-1] / 2 ** 80, "sum mu/64", float(expo),
          "max op/det", float(binv), "op0", float(rows[0]["op"]),
          "C", float(rows[0]["op"]) * math.exp(expo) * float(binv))
    # forward radii from a section ball that stays below the backward ones
