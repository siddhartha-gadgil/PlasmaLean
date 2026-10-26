#!/usr/bin/env python3
"""Untrusted generator of the oscillatory-kick cover (Phase 12c).

Builds an adaptive binary subdivision of the index window [0, 120] x [0, 128]
(psi0 in [4.75, 5.8047], Bt in [5.4, 5.5]) whose leaves pass the split checks `legAOk`,
`legBOk` and `finalOk ... Kn 1 Pmin` of `Design/NearAxisQATrappedOscCells`, computed with the
exact mirror `osc_mirror.py`, and writes the Lean files

  PlasmaLean/Design/NearAxisQATrappedOscRowsNN.lean  (kernel checks of the leaves)
  PlasmaLean/Design/NearAxisQATrappedOscCover.lean   (the cover term; written separately)

Usage: python3 -I osc_gen.py OUTDIR Kn Pmin Pmax DlS DhS [leaves_per_file]
"""
import math
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from osc_mirror import (PBI, TBI, theta0_oracle, legs, theta0Ok, add, mul, C, cosSinC, S,
                        finalOk, lit)  # noqa: E402


def box(a, b, c, d):
    P, T = PBI(a, b), TBI(c, d)
    Th0 = theta0_oracle(P, T, 1 << 14)
    dd = legs(P, T, Th0)
    ok = dd["okA"] and dd["okB"] and theta0Ok(P, T, Th0)
    Ct, St = add(dd["Cin"], dd["Cout"]), add(dd["Sin"], dd["Sout"])
    sD = cosSinC(mul(dd["J2"], C(500, 211)))[1]
    if not ok or sD.lo <= 0:
        return None, math.inf, Th0
    Cm, Sm = max(-Ct.lo, Ct.hi), max(-St.lo, St.hi)
    return dd, math.sqrt(Cm * Cm + Sm * Sm) / sD.lo, Th0


def cover(a, b, c, d, Kn, Pmin, leaves, Pmax=72, DlS=3086000000, DhS=4502000000):
    if b - a > 15:
        m = (a + b) // 2
        return ("X", m, cover(a, m, c, d, Kn, Pmin, leaves, Pmax, DlS, DhS), cover(m, b, c, d, Kn, Pmin, leaves, Pmax, DlS, DhS))
    if d - c > 16:
        m = (c + d) // 2
        return ("Y", m, cover(a, b, c, m, Kn, Pmin, leaves, Pmax, DlS, DhS), cover(a, b, m, d, Kn, Pmin, leaves, Pmax, DlS, DhS))
    dd, K, Th0 = box(a, b, c, d)
    if dd is not None and finalOk(dd, Kn, 1, Pmin, Pmax, DlS, DhS):
        leaves.append((a, b, c, d, Th0, dd))
        return ("L", (a, b, c, d))
    if (d - c) >= 8 and (d - c) / 16 >= (b - a) / 15 * 0.5:
        m = (c + d) // 2
        return ("Y", m, cover(a, b, c, m, Kn, Pmin, leaves, Pmax, DlS, DhS), cover(a, b, m, d, Kn, Pmin, leaves, Pmax, DlS, DhS))
    if b - a >= 2:
        m = (a + b) // 2
        return ("X", m, cover(a, m, c, d, Kn, Pmin, leaves, Pmax, DlS, DhS), cover(m, b, c, d, Kn, Pmin, leaves, Pmax, DlS, DhS))
    if d - c >= 2:
        m = (c + d) // 2
        return ("Y", m, cover(a, b, c, m, Kn, Pmin, leaves, Pmax, DlS, DhS), cover(a, b, m, d, Kn, Pmin, leaves, Pmax, DlS, DhS))
    raise RuntimeError(f"cannot certify box {(a, b, c, d)} K={K}")


def term(t, a, b, c, d):
    if t[0] == "L":
        return f"(OscCover.leaf {a} {b} {c} {d} oscLeaf_{a}_{b}_{c}_{d})"
    if t[0] == "X":
        m = t[1]
        return (f"(OscCover.splitP {a} {m} {b} {c} {d}\n  {term(t[2], a, m, c, d)}\n"
                f"  {term(t[3], m, b, c, d)})")
    m = t[1]
    return (f"(OscCover.splitT {a} {b} {c} {m} {d}\n  {term(t[2], a, b, c, m)}\n"
            f"  {term(t[3], a, b, m, d)})")


HEADER = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part {part}

Leaves {first}–{last} of the adaptive cover of the start window used by
`Design/NearAxisQATrappedOscCover` (amplitude target `Kn = {Kn}`, period range
`[{Pmin}, {Pmax}] μs`, precession range `ι₀ Δ ∈ [{DlS}, {DhS}] · 2⁻³²`).
For each index box `[a, b] × [c, d]` (`ψ₀ ∈ PBI a b`, `B_t ∈ TBI c d`) the inner-leg check
`legAOk`, the outer-leg check `legBOk` (with the inner leg's `I(z₁)` enclosure) and the final
check `finalOk` are checked on the oracle enclosures (all computed by the untrusted exact
mirror `scripts/trapped_reanchor/osc_mirror.py`), all three by evaluation certificates
(`fiv_cert`, `Certificates/EvalCert`: one kernel leaf per interval operation; the leg checks are
≈ 4·10⁴ leaves each, so the private `.olean` of this module is ≈ 300 MB).
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Design.NearAxisQATrappedCells
"""


def leaf_lean(a, b, c, d, Th0, dd, Kn, Pmin, Pmax, DlS, DhS):
    P, T = f"(PBI {a} {b})", f"(TBI {c} {d})"
    A = (f"legAOk {P} {T} {lit(Th0)}\n    {lit(dd['Cin'])} {lit(dd['Sin'])}\n    "
         f"{lit(dd['J1'])} {lit(dd['Tin'])}")
    B = (f"legBOk {P} {T} {lit(Th0)}\n    {lit(dd['J1'])} {lit(dd['Cout'])}\n    "
         f"{lit(dd['Sout'])} {lit(dd['J2'])}\n    {lit(dd['Tout'])}")
    Fn = (f"finalOk\n    {lit(dd['Cin'])} {lit(dd['Sin'])}\n    {lit(dd['Cout'])} "
          f"{lit(dd['Sout'])}\n    {lit(dd['J2'])} {lit(dd['Tin'])}\n    {lit(dd['Tout'])} "
          f"{Kn} 1 {Pmin} {Pmax}\n    {DlS} {DhS}")
    n = f"{a}_{b}_{c}_{d}"
    return f"""
set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[{a}, {b}] × [{c}, {d}]`. -/
theorem oscA_{n} : {A} = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[{a}, {b}] × [{c}, {d}]`. -/
theorem oscB_{n} : {B} = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[{a}, {b}] × [{c}, {d}]`. -/
theorem oscF_{n} : {Fn} = true := by
  fiv_cert

/-- The box `[{a}, {b}] × [{c}, {d}]` is a leaf of the cover. -/
theorem oscLeaf_{n} : OscLeaf {Kn} {Pmin} {Pmax} {DlS} {DhS} {a} {b} {c} {d} :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_{n}, oscB_{n}, oscF_{n}⟩
"""


def main():
    out, Kn, Pmin = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    Pmax, DlS, DhS = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    per = int(sys.argv[7]) if len(sys.argv) > 7 else 8
    leaves = []
    tree = cover(0, 120, 0, 128, Kn, Pmin, leaves, Pmax, DlS, DhS)
    print("leaves", len(leaves))
    files = []
    for f0 in range(0, len(leaves), per):
        part = f0 // per + 1
        chunk = leaves[f0:f0 + per]
        name = f"NearAxisQATrappedOscRows{part:02d}"
        body = HEADER.format(part=part, first=f0, last=f0 + len(chunk) - 1, Kn=Kn, Pmin=Pmin,
                             Pmax=Pmax, DlS=DlS, DhS=DhS)
        for (a, b, c, d, Th0, dd) in chunk:
            body += leaf_lean(a, b, c, d, Th0, dd, Kn, Pmin, Pmax, DlS, DhS)
        body += "\nend PlasmaLean.Design.NearAxisQATrappedOsc\n"
        with open(f"{out}/{name}.lean", "w") as fh:
            fh.write(body)
        files.append(name)
    with open(f"{out}/cover_term.txt", "w") as fh:
        fh.write(term(tree, 0, 120, 0, 128))
    with open(f"{out}/files.txt", "w") as fh:
        fh.write("\n".join(files))


if __name__ == "__main__":
    main()
