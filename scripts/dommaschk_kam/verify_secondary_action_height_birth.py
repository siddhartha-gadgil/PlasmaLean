"""Attach the shifted action rectangles to the same authenticated secondary birth trajectory."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from screen_secondary_action_archive import ARCHIVE, COUNT, archive
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import ROOT, digest, save
from verify_secondary_action_cover import BIRTH, header, package
from verify_secondary_action_height import MASS_SCALE, PACKAGE, PAIRS, shift_block
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


def application(ticks, k, n, parent, original, born):
    pm = f"DommaschkSignedPrefixQ0R478{n:03}"
    name = f"DommaschkShiftedActionBirth{ticks}R{k:03}Of{n:03}"
    records = [shift_block(word, ticks) for word, _ in archive()[COUNT-k:COUNT+k]]
    units = sum(m for _, m, _ in records)
    mass = Fraction(units, MASS_SCALE)
    floor = min(g for _, _, g in records)
    if floor <= 0:
        raise ValueError("the proposed physical window contains a clipped turning panel")
    src = header(name, [f"{PACKAGE}.{parent}", f"{BIRTH}.{born}"])
    src += f"""
open Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton
open DommaschkLowerActionPath {pm}
abbrev lowerMass : ℝ := {mass.numerator} / {mass.denominator}
abbrev level := DommaschkSecondaryActionMass.height
def rows := ({parent}.shifted.drop {PAIRS-k}).take {2*k}
theorem checked : Certificates.LowerActionHeightShift.blockTest {ticks} {floor}
    {original}.blocks rows = true := by with_unfolding_all rfl
theorem length_rows : rows.length = {k} + {k} := by kernel_fact
theorem sum_rows : total rows = {units} := by kernel_fact

/-- One physical birth trajectory serves every height in the indicated range. -/
def Claims (y : ℝ → Plane) : Prop :=
  Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧
  ∀ h : ℝ, level - {parent}.heightDrop ≤ h →
    lowerMass ≤ Kinetic.MirrorHeightAction.action (field y) (DommaschkNativeWellAction.density y)
      (-{k}/64) ({k}/64) h

theorem on_path {{y : ℝ → Plane}} (old : {born}.Claims y) : Claims y := by
  have path := old.1
  have box := regions path.forward path.backward (n := {n}) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  have valid : ∀ t ∈ Icc (-{k}/64:ℝ) ({k}/64), DommaschkSignedTraceDomain.Region (y t) := by
    intro t ht
    apply box t
    constructor <;> norm_num <;> linarith [ht.1,ht.2]
  have inside : Icc (-{k}/64:ℝ) ({k}/64) ⊆ Ioo (-({n}/64)) ({n}/64) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨cf,cw,eq⟩ := path.inputs inside valid
  have cells := old.2.1
  rw [{original}.Covered, show {original}.start = (-{k}/64:ℝ) by norm_num [{original}.start]] at cells
  refine ⟨path,fun h levelBound => ?_⟩
  have shift : 2*(level-h) ≤ ({ticks}:ℝ)/67108864 := by
    change level - {ticks}/134217728 ≤ h at levelBound
    linarith
  have moved := (Certificates.LowerActionHeightShift.covers shift _ checked cells).1
  have bound := Certificates.NativeActionInterval.exact_lower_mass length_rows moved
    (fun t ht => by rw [← eq t ht]; exact norm_nonneg _) cf cw
  rw [sum_rows] at bound
  have same : Kinetic.MirrorHeightAction.action (field y) (density y) (-{k}/64) ({k}/64) h =
      Kinetic.MirrorHeightAction.action (field y) (DommaschkNativeWellAction.density y)
        (-{k}/64) ({k}/64) h := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact congrArg (fun v => v * _) (eq t ht).symm
  rw [← same]
  norm_num [lowerMass] at bound ⊢
  exact bound

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ Claims := by
  obtain ⟨s,a,y,hs,ha,src,d,j,old⟩ := {born}.from_entry e
  exact ⟨s,a,y,hs,ha,src,d,j,on_path old⟩

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ Claims := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry (entry endpoint φ h)⟩

end PlasmaLean.Design.{name}
"""
    return (name, src, ["on_path", "from_entry", "from_nested_tori"]), mass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=Path, required=True)
    parser.add_argument("--birth-cover", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT/".lake/secondary-action-height")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    height, cover = [json.loads(p.read_text()) for p in (args.height, args.birth_cover)]
    birth = cover["birth"]
    k, n, ticks = cover["pairs"], birth["signed_length"], height["ticks"]
    parent = f"DommaschkQ0R478ShiftedAction{ticks}"
    lo, hi = COUNT-k, COUNT+k
    orig = f"DommaschkLowerCoverQ0R478L{lo:03}R{hi:03}"
    born = f"DommaschkQ0R478BirthCover{k:03}Of{n:03}"
    if (not 1 <= k <= PAIRS or n <= k or cover["block_range"] != [lo, hi]
            or (cover["module"], cover["package"], birth["module"]) != (orig, package(lo, hi), born)
            or (height["module"], height["archive_sha256"]) != (parent, digest(ARCHIVE))
            or cover["packet_sha256"] != digest(load(478)[1])):
        parser.error("a matching checked q0r478 birth and shifted central archive are required")
    paths = [Path(height["proof_root"]), *map(Path, birth["import_paths"])]
    for path, mod, key in [(paths[0], parent, height["key"]), (paths[1], born, birth["key"])]:
        admitted(path, mod, key)

    def lake(*cmd):
        return subprocess.check_output(["lake", "env", *cmd], cwd=ROOT, text=True).strip()

    args.lean = str(Path(lake("lean", "--print-prefix"))/"bin/lean")
    args.lean_path = lake("printenv", "LEAN_PATH")
    keys = [lake("lean", "--version"), height["key"], birth["key"], cover["packet_sha256"]]
    overlay = merge_import_roots(args.cache/"birth", paths, keys)
    item, mass = application(ticks, k, n, parent, orig, born)
    root, proof = compile_modules(args.cache/item[0], [item], [overlay], keys, args,
                                  "SecondaryShiftedBirthCache")
    out = {k: proof[k] for k in ["module", "key", "theorems", "axioms", "wall_seconds", "peak_rss_kib"]}
    out.update(height_drop=height["height_drop"], lower_mass=str(mass), pairs=k,
               physical_cells=2*k*48, signed_length=n, original_birth_key=birth["key"],
               shifted_archive_key=height["key"], import_paths=list(map(str, [root, overlay])))
    save(args.output, out)
    print(item[0], str(mass), proof["key"])


if __name__ == "__main__":
    main()
