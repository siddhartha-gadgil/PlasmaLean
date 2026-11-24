"""Kernel-check height-shifted lower action cells on the original q0r478 central 322 pairs."""
import argparse
from fractions import Fraction
from math import isqrt
from pathlib import Path
import subprocess

from screen_secondary_action_archive import ARCHIVE, COUNT, TARGET, archive
from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


PAIRS = 322
PACKAGE = "SecondaryActionHeightCache"
DESIGN_MODULE = "DommaschkSecondaryActionHeight"
SCALE = 1 << 24
MASS_SCALE = 3072 * 2**40


def shift_block(packed, ticks):
    """Decode every original density and propose a fresh downward square-root witness."""
    shifted = mass = 0
    minimum = SCALE
    for index in range(48):
        density = packed % SCALE
        original = (packed >> 24) % SCALE
        gap = max(0, original - ticks)
        speed = isqrt(gap << 14)
        assert speed * speed <= (gap << 14) < (speed + 1) ** 2 and speed < SCALE
        shifted |= (density + (gap << 24) + (speed << 48)) << (72 * index)
        mass += density * speed
        minimum = min(minimum, gap)
        packed >>= 72
    if packed:
        raise ValueError("the source block has trailing digits")
    return shifted, mass, minimum


def source(ticks):
    first, stop = COUNT - PAIRS, COUNT + PAIRS
    original = archive()
    proposals = [shift_block(word, ticks) for word, _ in original[first:stop]]
    units = sum(mass for _, mass, _ in proposals)
    mass = Fraction(units, MASS_SCALE)
    floor = min(gap for _, _, gap in proposals)
    if mass <= TARGET or floor <= 0:
        raise ValueError(f"{ticks} squared-speed ticks leave mass {mass}, "
                         f"excess {mass-TARGET} and minimum digit {floor}")
    name = f"DommaschkQ0R478ShiftedAction{ticks}"
    lines = [
        "module", f"public import PlasmaLean.Design.{DESIGN_MODULE}",
        "/-! # A closed range of mirror heights with a strict second-launch action target -/",
        "@[expose] public section", "noncomputable section",
        f"namespace PlasmaLean.Design.{name}",
        "open Certificates Certificates.MirrorActionQuadrature Certificates.LowerActionHeightShift",
        "open DommaschkActionQ0R478 DommaschkSecondaryActionCore DommaschkSecondaryActionMass",
        "open Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope Set",
        "set_option maxRecDepth 65536", "set_option maxHeartbeats 4000000",
        "set_option linter.style.longLine false", "set_option Elab.async false", "",
    ]
    groups = []
    for index in range(first // 16, (stop - 1) // 16 + 1):
        lo, hi = max(first, 16 * index), min(stop, 16 * (index + 1))
        original_group = f"slabGroup{index}"
        if lo > 16 * index:
            original_group = f"({original_group}.drop {lo-16*index})"
        if hi < 16 * (index + 1):
            original_group = f"({original_group}.take {hi-lo})"
        group = f"shifted{index}"
        groups.append((original_group, group, f"ok{index}"))
        lines.append(f"def {group} : List (Block false) := [")
        lines.append(",\n".join(f"  ⟨{word:#x}, {contribution}, rfl⟩"
                               for word, contribution, _ in proposals[lo-first:hi-first]) + "]")
        lines.append(f"theorem ok{index} : blockTest {ticks} {floor} {original_group} {group}"
                     " = true := by with_unfolding_all rfl")
    old_groups = " ++ ".join(g[0] for g in groups)
    new_groups = " ++ ".join(g[1] for g in groups)
    lines.extend([
        f"def shifted : List (Block false) := {new_groups}",
        f"theorem transferred : blockTest {ticks} {floor} inner shifted = true := by",
        f"  change blockTest {ticks} {floor} ({old_groups}) ({new_groups}) = true",
        *[f"  apply blockTest_append {g[2]}" for g in groups[:-1]],
        f"  exact {groups[-1][2]}",
        "theorem length_shifted : shifted.length = 322 + 322 := by kernel_fact",
        f"theorem sum_shifted : total shifted = {units} := by kernel_fact",
        f"abbrev lowerMass : ℝ := {mass.numerator} / {mass.denominator}",
        f"abbrev heightDrop : ℝ := {ticks} / 134217728",
        "theorem physical_core {w f : ℝ → ℝ} {h : ℝ} (level : height - heightDrop ≤ h)",
        "    (cells : Covers false w f height (-322 / 64) inner) :",
        "    Covers false w f h (-322 / 64) shifted ∧",
        "      (∀ t ∈ Icc (-322 / 64 : ℝ) (322 / 64), f t < h) :=",
        f"  {DESIGN_MODULE}.shifted_cover length_shifted (by norm_num) transferred level cells",
        "theorem first_well {w f : ℝ → ℝ} {h l r : ℝ} (level : height - heightDrop ≤ h)",
        "    (cells : Covers false w f height (-322 / 64) inner)",
        "    (well : LaunchWell f 0 h l r) (hn : ∀ t ∈ Icc l r, 0 ≤ w t)",
        "    (cf : ContinuousOn f (Icc l r)) (cw : ContinuousOn w (Icc l r)) :",
        "    l < -322 / 64 ∧ 322 / 64 < r ∧ target < lowerMass ∧ lowerMass ≤ action f w l r h := by",
        f"  obtain ⟨left,right,estimate⟩ := {DESIGN_MODULE}.first_well",
        "    length_shifted (by norm_num) transferred level cells well hn cf cw",
        "  rw [sum_shifted] at estimate",
        "  refine ⟨left,right,by norm_num [target,lowerMass],?_⟩",
        "  norm_num [lowerMass] at estimate ⊢", "  exact estimate",
        f"end PlasmaLean.Design.{name}", "",
    ])
    report = dict(endpoint="q0r478", pairs=PAIRS, panels=len(proposals)*48, ticks=ticks,
                  height_drop=str(Fraction(ticks, 2**27)), mass_units=units,
                  lower_mass=str(mass), target=str(TARGET), excess=str(mass-TARGET),
                  minimum_new_squared_speed_digit=floor)
    return name, "\n".join(lines), report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ticks", type=int, default=256,
                        help="decrease the height by this numerator over 2^27")
    parser.add_argument("--cache", type=Path, default=ROOT/".lake/secondary-action-height")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.ticks < 0:
        parser.error("the height decrement must be nonnegative")
    name, lean_source, report = source(args.ticks)

    def lake(*cmd):
        return subprocess.check_output(["lake", "env", *cmd], cwd=ROOT, text=True).strip()

    args.lean = str(Path(lake("lean", "--print-prefix")) / "bin/lean")
    args.lean_path = lake("printenv", "LEAN_PATH")
    archive_sha = digest(ARCHIVE)
    common = [lake("lean", "--version"), digest(DESIGN/(DESIGN_MODULE+".trace")), archive_sha]
    item = (name, lean_source, ["physical_core", "first_well"])
    root, proof = compile_modules(args.cache/name, [item], [], common, args, PACKAGE)
    report.update({k: proof[k] for k in ["module", "key", "theorems", "axioms",
                                         "wall_seconds", "peak_rss_kib"]})
    report.update(proof_root=str(root), archive_sha256=archive_sha)
    save(args.output, report)
    print(name, report["height_drop"], report["lower_mass"], proof["key"])


if __name__ == "__main__":
    main()
