/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorTubeCrossing
public import PlasmaLean.Design.DommaschkPhysicalFirstStep

/-! # Field-strength sign throughout the first physical forward tube -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKam DommaschkKam.DkPoly
open Certificates.TrajectoryTaylorModel DommaschkBounceTaylorFirst DommaschkMirrorTubeCrossing
open DommaschkPhysicalFirstStep Set

/-- Lower and upper mirror heights in the archived q0, u=0.470 action cell. -/
def height (upper : Bool) : ℚ :=
  if upper then 5300546391395933 / 5000000000000000 else 5297961656084411 / 5000000000000000

set_option maxRecDepth 16000 in
/-- Field strength on the entire first physical forward tube is below both target heights. -/
theorem first_tube_below {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) {x : Plane}
    (hx : x ∈ (physicalSlab seed row 0).tube t) (upper : Bool) : strength t x < height upper := by
  let m := moving seed row 0 t
  let p := reference 0 row t
  let v := m.symm (x - p)
  have out : ‖v‖ ≤ row.outgoing / (2 : ℝ)^80 := hx.1
  have growth := growth_sound (Bool.and_eq_true_iff.mp checked).2
  have trialBall : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ)^80) := by
    simpa using out.trans growth.2.2.2.2.1.le
  have data := trial_membership ht trialBall
  have same : p + m v = x := by simp [v]
  change trial.u.Mem (128 * t - 1) ((p + m v) 0 - dkR0) ∧
    trial.z.Mem (128 * t - 1) ((p + m v) 1) at data
  rw [same] at data
  have hs : |128*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have re := enclose (c := ⟨[89/1000],1/4000⟩) hs data.1 (by kernel_fact)
  have lowR : 199/200 ≤ x 0 := by
    norm_num [Model.Mem, Certificates.QPoly.eval, dkR0, abs_le] at re
    linarith
  have Rpos : 0 < x 0 := by linarith
  have hc : t ∈ Icc (0/64:ℝ) (1/64) := by simpa using ht
  have mem : trial.Mem (128*t-1) (x 0 - dkR0) (x 1)
      (Real.cos (2*t)) (Real.sin (2*t)) := by
    refine ⟨data.1, data.2, ?_, ?_⟩
    · change (DommaschkHarmonicSlab0.model false 0 false).Mem _ _
      simpa [Certificates.TrajectoryTrig.wave] using
        DommaschkHarmonicSlab0.physical false 0 false hc
    · change (DommaschkHarmonicSlab0.model false 0 true).Mem _ _
      simpa [Certificates.TrajectoryTrig.wave] using DommaschkHarmonicSlab0.physical false 0 true hc
  let f := fun q => atPoint q (x 0) t (x 1)
  have d := dD_range hs (dD_checked.mem hs mem)
  have r := dnR_range hs (dnR_checked.mem hs mem)
  have z := dnZ_range hs (dnZ_checked.mem hs mem)
  change _ ≤ f dD ∧ f dD ≤ _ at d
  change _ ≤ f dnR ∧ f dnR ≤ _ at r
  change _ ≤ f dnZ ∧ f dnZ ≤ _ at z
  have d2 : (f dD)^2 ≤ (101/100 : ℝ)^2 := sq_le_sq' (by linarith [d.1]) (by linarith [d.2])
  have r2 : (f dnR)^2 ≤ (1/1000 : ℝ)^2 := sq_le_sq' (by linarith [r.1]) (by linarith [r.2])
  have z2 : (f dnZ)^2 ≤ (77/1000 : ℝ)^2 := sq_le_sq' (by linarith [z.1]) (by linarith [z.2])
  have field := norm_sq_eq_strengthSq Rpos t (x 1)
  change (strength t x)^2 = (f dD)^2/(x 0)^14 + ((f dnR)^2+(f dnZ)^2)/(x 0)^16 at field
  have bound : (strength t x)^2 ≤ (101/100 : ℝ)^2/(199/200 : ℝ)^14 +
      ((1/1000 : ℝ)^2 + (77/1000 : ℝ)^2)/(199/200 : ℝ)^16 := by
    rw [field]
    gcongr
  have strict : (strength t x)^2 < ((height upper : ℚ):ℝ)^2 := by
    apply bound.trans_lt
    cases upper <;> norm_num [height]
  have pos : (0:ℝ) ≤ (height upper : ℚ) := by cases upper <;> norm_num [height]
  exact (sq_lt_sq₀ (norm_nonneg _) pos).mp strict

end PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
