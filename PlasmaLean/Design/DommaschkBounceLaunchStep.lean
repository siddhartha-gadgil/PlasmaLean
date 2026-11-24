/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceFlowStep
public import PlasmaLean.Design.DommaschkBounceTubeData
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Field-line enclosures from both deep-strip launch sections

The entire phase-zero and phase-π/2 birth rectangles admit a solution of the
physical QA2R field-line ODE for an angular distance of 1/32 in either direction.
The proof checks every monomial on the swept tube, including all intermediate times.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkBounceField

open DommaschkKam Real Set PlasmaLean.Fields.RectangularODEStep
open PlasmaLean.Certificates.ValidatedQuadrature

/-- The two symmetry-section phases. -/
def sectionPhase (inner : Bool) : ℝ := if inner then π/2 else 0

/-- Lower corner of the certified physical tube in radius and vertical height. -/
def tubeLo (inner : Bool) : State := ![if inner then 7/8 else 63/64, -(1/64)]

/-- Upper corner of the certified physical tube. -/
def tubeHi (inner : Bool) : State := ![if inner then 29/32 else 65/64, 1/64]

private theorem angular_bounds {a : ℝ} (ha : |a| ≤ 1/16) :
    15/16 ≤ cos a ∧ cos a ≤ 1 ∧ -(1/16) ≤ sin a ∧ sin a ≤ 1/16 := by
  have hc := (abs_le.mp ((abs_cos_sub_cos_le a 0).trans (by simpa using ha))).1
  have hs := abs_le.mp (abs_sin_le_abs.trans ha)
  exact ⟨by simp only [cos_zero] at hc; linarith, cos_le_one _, hs⟩

private theorem clock_mem (inner : Bool) {phase sign t T : ℝ} (hs : |sign| ≤ 1)
    (hphase : |phase - sectionPhase inner| + T ≤ 1/32) (ht : t ∈ Icc 0 T)
    (x : State) (hx : x ∈ Icc (tubeLo inner) (tubeHi inner)) :
    (if inner then innerBox else outerBox).Mem (x 0 - dkR0) (x 1)
      (cos (2*(phase+sign*t))) (sin (2*(phase+sign*t))) := by
  let a := 2*((phase - sectionPhase inner) + sign*t)
  have ha : |a| ≤ 1/16 := by
    have hst : |sign*t| ≤ t := by
      rw [abs_mul, abs_of_nonneg ht.1]
      simpa using mul_le_mul_of_nonneg_right hs ht.1
    have hsum := abs_add_le (phase - sectionPhase inner) (sign*t)
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [ht.2]
  have he : 2*(phase+sign*t) = (if inner then π else 0) + a := by
    cases inner <;> simp [a, sectionPhase] <;> ring
  obtain ⟨hc₁,hc₂,hs₁,hs₂⟩ := angular_bounds ha
  have lR := hx.1 0
  have hR := hx.2 0
  have lz := hx.1 1
  have hz := hx.2 1
  rw [he]
  cases inner <;>
    norm_num [tubeLo,tubeHi] at lR hR lz hz <;>
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
    norm_num [fxVal, fxScale, innerBox, outerBox, dkR0, cos_add, sin_add] <;>
    constructor <;> linarith

private theorem speed_of_bounds {d r z : ℝ} (hd : 0 < d)
    (hr : -(d/4) ≤ r ∧ r ≤ d/4) (hz : -(d/4) ≤ z ∧ z ≤ d/4) :
    0 < d ∧ |r/d| ≤ 1/4 ∧ |z/d| ≤ 1/4 := by
  refine ⟨hd, ?_, ?_⟩ <;> rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_le] <;>
    constructor <;> linarith

private theorem tube_speeds (inner : Bool) {phase sign t T : ℝ} (hs : |sign| ≤ 1)
    (hphase : |phase - sectionPhase inner| + T ≤ 1/32) (ht : t ∈ Icc 0 T) (x : State) (hx : x ∈ Icc (tubeLo inner) (tubeHi inner)) :
    let k := clockPoly phase sign
    0 < k dD (t,x) ∧ |k dnR (t,x) / k dD (t,x)| ≤ 1/4 ∧
      |k dnZ (t,x) / k dD (t,x)| ≤ 1/4 := by
  have m := clock_mem inner hs hphase ht x hx
  have hd := polyBox_mem m dD
  have hr := polyBox_mem m dnR
  have hz := polyBox_mem m dnZ
  dsimp only [clockPoly, atPoint, Prod.fst, Prod.snd]
  apply speed_of_bounds
  all_goals
    cases inner <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, outer_dD, outer_dnR, outer_dnZ,
        inner_dD, inner_dnR, inner_dnZ] at hd hr hz <;>
      have d := hd rfl <;> have r := hr rfl <;> have z := hz rfl <;>
      norm_num [fxVal, fxScale] at d r z <;>
      first | linarith only [d.1] | constructor <;> linarith only [d.1, r.1, r.2, z.1, z.2]

/-- True QA2R trajectories for the complete two birth rectangles, including the
phase-transfer allowance. The sign chooses either direction of angular travel. -/
theorem exists_launch_step (inner : Bool) (phase sign T : ℝ) (hs : |sign| ≤ 1) (hT : 0 ≤ T)
    (hphase : |phase - sectionPhase inner| + T ≤ 1/32) (x₀ : State)
    (hlo : (if inner then 89299 else 99416 : ℝ)/100000 ≤ x₀ 0)
    (hhi : x₀ 0 ≤ (if inner then 89649 else 99723 : ℝ)/100000)
    (hz : |x₀ 1| ≤ 1/1000) :
    ∃ x : ℝ → State, x 0 = x₀ ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt x (physicalFlow phase sign t (x t)) (Icc 0 T) t ∧
      x t ∈ Icc (tubeLo inner) (tubeHi inner) ∧
      ∃ v ∈ Icc (fun _ : Fin 2 => -(1/4:ℝ)) (fun _ => 1/4), x t = x₀ + t • v := by
  have hTle : T ≤ 1/32 := by linarith [abs_nonneg (phase - sectionPhase inner)]
  apply exists_physical_step hT
  · intro i
    cases inner <;> fin_cases i <;> norm_num [tubeLo, tubeHi]
  · cases inner <;> norm_num [tubeLo]
  · intro t ht x hx
    exact (tube_speeds inner hs hphase ht x hx).1
  · intro t ht x hx
    obtain ⟨_,hr,hz'⟩ := tube_speeds inner hs hphase ht x hx
    have mul_bound (a : ℝ) (ha : |a| ≤ 1/4) : -(1/4) ≤ sign*a ∧ sign*a ≤ 1/4 := by
      apply abs_le.mp
      rw [abs_mul]
      simpa using mul_le_mul hs ha (abs_nonneg a) (by norm_num : (0:ℝ) ≤ 1)
    constructor <;> intro i <;> fin_cases i
    · exact (mul_bound _ hr).1
    · exact (mul_bound _ hz').1
    · exact (mul_bound _ hr).2
    · exact (mul_bound _ hz').2
  · intro t ht v hv
    apply tube_of_endpoints _ _ _ ht hv
    all_goals
      have hz' := abs_le.mp hz
      cases inner <;> norm_num at hlo hhi <;>
        first | constructor <;> intro i <;> fin_cases i | intro i <;> fin_cases i
      all_goals norm_num [tubeLo, tubeHi] <;> linarith

end PlasmaLean.Design.DommaschkBounceField
