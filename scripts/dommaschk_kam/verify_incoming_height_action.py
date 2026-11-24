"""Ground a simultaneous action floor directly on the available signed secondary field line."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_action_cover import header
from verify_secondary_mirror_caps import load
from verify_secondary_shifted_well import checked_paths
from verify_signed_mirror_passage import merge_import_roots
from verify_submirror_prefix_projection import PACKAGE as OBSERVATIONS


def application(prefix, short):
    n, k = prefix["signed_length"], prefix["observed_length"]
    pm = f"DommaschkSignedPrefixQ0R478{n:03}"
    name = f"DommaschkIncomingHeightAction{k:03}Of{n:03}"
    mass = Fraction(short["lower_mass"]) + Fraction(2*(k-32),64)*Fraction(7,8)*Fraction(161,5000)
    strict = Fraction((1000*mass.numerator-1)//mass.denominator,1000)
    src = header(name, ["PlasmaLean.Design.DommaschkIncomingHeightAction",
                        f"{OBSERVATIONS}.{prefix['module']}",
                        "SecondaryShiftedBirthCache.DommaschkShiftedActionBirth267R032Of048"])
    src += f"""
open Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton {pm}
open DommaschkSecondaryHeightCollar DommaschkLowerActionPath Kinetic.MirrorHeightAction
abbrev level := DommaschkSecondaryActionMass.height
abbrev mass : ℝ := {mass.numerator}/{mass.denominator}
abbrev lowerClaim : ℝ := {strict.numerator}/{strict.denominator}
def Claims (y : ℝ → Plane) : Prop :=
  Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧
    ∀ h : ℝ, lower ≤ h → lowerClaim < mass ∧ mass ≤
      action (field y) (DommaschkNativeWellAction.density y) (-{k}/64) ({k}/64) h

theorem on_path {{y : ℝ → Plane}} (path : Signed endpoint.start forwardRows backwardRows ({n}/64) y) :
    Claims y := by
  have cut {{rs : List Step}} {{s : ℝ}} {{z : ℝ → Plane}} (m : ℕ)
      (a : Outward endpoint.start rs s ({n}/64) z) : Outward endpoint.start (rs.take m) s ({n}/64) z :=
    (show Outward endpoint.start (rs.take m ++ rs.drop m) s ({n}/64) z by simpa only [List.take_append_drop] using a).prefix
  have okF : Certificates.PositionFrameSlabs.OnTubes
      (fun t x => DommaschkMirrorTubeCrossing.strength t x < (↑(DommaschkFirstMirrorLaunchSign.height false - (1/270000)) : ℝ))
      endpoint.start 0 (forwardRows.take {k}) := by
    with_unfolding_all exact (DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.fwd_below endpoint.start).take {k}
  have okB : Certificates.PositionFrameSlabs.OnTubes
      (fun t x => DommaschkMirrorTubeCrossing.strength (-t) x < (↑(DommaschkFirstMirrorLaunchSign.height false - (1/270000)) : ℝ))
      endpoint.start 0 (backwardRows.take {k}) := by
    with_unfolding_all exact (DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.back_below endpoint.start).take {k}
  have F := okF.on_initial (y := y) (by norm_num) (by with_unfolding_all change {k} ≤ {n}; norm_num) path.forward.contained
  have B := okB.on_initial (y := fun t => y (-t)) (by norm_num) (by with_unfolding_all change {k} ≤ {n}; norm_num) path.backward.contained
  have clear (t : ℝ) (ht : t ∈ Icc (-{k}/64:ℝ) ({k}/64)) :
      field y t < ↑(DommaschkFirstMirrorLaunchSign.height false - (1/270000)) := by
    rcases le_total 0 t with pos | neg
    · exact F t ⟨pos,by simpa only [Nat.cast_ofNat,zero_add] using ht.2⟩
    · have q := B (-t) ⟨by linarith,by norm_num; linarith [ht.1]⟩
      simpa only [neg_neg,field] using q
  have box := regions (cut {k} path.forward) (cut {k} path.backward) (n := {k}) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  have region : ∀ t ∈ Icc (-{k}/64:ℝ) ({k}/64), DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [Nat.cast_ofNat] using box
  obtain ⟨cf,cw,cart⟩ := DommaschkIncomingHeightAction.closed_inputs path
    (by norm_num : (-{k}/64:ℝ) ≤ {k}/64) (by norm_num) (by norm_num) region
  have smallF : Outward endpoint.start (DommaschkQ0R478MirrorBranch327.fwdRows.take 32) 1 ({n}/64) y := by
    with_unfolding_all exact cut (rs := forwardRows) 32 path.forward
  have smallB : Outward endpoint.start (DommaschkQ0R478MirrorBranch327.backRows.take 32) (-1) ({n}/64) (fun t => y (-t)) := by
    with_unfolding_all exact cut (rs := backwardRows) 32 path.backward
  have old := DommaschkLowerCoverQ0R478L295R359.cover (tracks_of_take smallF smallB)
  rw [DommaschkLowerCoverQ0R478L295R359.Covered,
    show DommaschkLowerCoverQ0R478L295R359.start = (-32/64:ℝ) by norm_num [DommaschkLowerCoverQ0R478L295R359.start]] at old
  have low (t : ℝ) (ht : t ∈ Icc (-{k}/64:ℝ) ({k}/64)) : 7/8 ≤ density y t :=
    DommaschkSignedTraceDensity.density_lower _ (region t ht)
  have sub : Icc (-32/64:ℝ) (32/64) ⊆ Icc (-{k}/64) ({k}/64) := Icc_subset_Icc (by norm_num) (by norm_num)
  refine ⟨path,fun h hh => ⟨by norm_num [lowerClaim,mass],?_⟩⟩
  have moved := (Certificates.LowerActionHeightShift.covers (h := h) (by
    change level-267/134217728 ≤ h at hh; linarith) _ DommaschkShiftedActionBirth267R032Of048.checked old).1
  have inner := Certificates.NativeActionInterval.exact_lower_mass DommaschkShiftedActionBirth267R032Of048.length_rows moved
    (fun t ht => (by norm_num : (0:ℝ) ≤ 7/8).trans (low t (sub ht))) (cf.mono sub) (cw.mono sub)
  rw [DommaschkShiftedActionBirth267R032Of048.sum_rows] at inner
  have A := DommaschkIncomingHeightAction.lower_on_window (A := {k}/64) (by norm_num) hh
    (by simpa only [neg_div] using cf) (by simpa only [neg_div] using cw)
    (by simpa only [neg_div] using low) (by simpa only [neg_div] using clear)
    (by norm_num at inner ⊢; exact inner)
  rw [← cart h]
  norm_num [mass] at A ⊢
  exact A

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ Claims :=
  observe (by rfl) ({pm}.from_entry e) (fun _ => on_path)

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ Claims := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ small => from_entry (entry endpoint φ small)⟩
end PlasmaLean.Design.{name}
"""
    return (name, src, ["on_path","from_entry","from_nested_tori"]), mass, strict


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--observation",type=Path,required=True)
    p.add_argument("--shifted-birth",type=Path,required=True)
    p.add_argument("--cache",type=Path,default=ROOT/".lake/incoming-height-action")
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    prefix,short=[json.loads(x.read_text()) for x in (a.observation,a.shifted_birth)]
    k,n=prefix["observed_length"],prefix["signed_length"]
    if (not 32<=k<=min(n,317) or prefix["drop"]!="1/270000"
            or prefix["module"]!=f"DommaschkQ0R478Drop1Over270000Observation{k:03}On{n:03}From317"
            or prefix["packet_sha256"]!=digest(load(478)[1])
            or short["module"]!="DommaschkShiftedActionBirth267R032Of048"):
        p.error("the q0r478 quantitative observation and the shifted 32-pair core are required")
    def lake(*cmd):
        return subprocess.check_output(["lake","env",*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake("lean","--print-prefix"))/"bin/lean")
    a.lean_path=lake("printenv","LEAN_PATH")
    keys=[lake("lean","--version"),digest(DESIGN/"DommaschkIncomingHeightAction.trace"),prefix["key"],short["key"]]
    overlay=merge_import_roots(a.cache/"parents",[*checked_paths(prefix),*checked_paths(short)],keys)
    item,mass,strict=application(prefix,short)
    root,rec=compile_modules(a.cache/item[0],[item],[overlay],keys,a,"IncomingHeightActionCache")
    out={k:rec[k] for k in ["module","key","axioms","theorems","wall_seconds","peak_rss_kib"]}
    out.update(exact_floor=str(mass),strict_floor=str(strict),signed_length=n,observed_length=k,
               quantitative_observation=prefix["key"],shifted_birth=short["key"],
               import_paths=list(map(str,[root,overlay])))
    save(a.output,out)
    print(item[0],mass,strict,rec["key"])


if __name__=="__main__":
    main()
