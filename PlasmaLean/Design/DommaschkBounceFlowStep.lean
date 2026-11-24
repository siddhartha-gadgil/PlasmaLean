/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceField
public import PlasmaLean.Theory.Fields.RectangularODEStep
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Existence on a certified rectangular tube of the QA2R field

The denominator and the two speed bounds suffice to construct the actual
field line on the entire rectangle in time, in either direction.
-/

@[expose] public section
noncomputable section

set_option maxHeartbeats 2500000

namespace PlasmaLean.Design.DommaschkBounceField
open DommaschkKam DkPoly Real Set
open PlasmaLean.Fields.RectangularODEStep

/-- Poloidal coordinates in the order radius, height. -/
abbrev State := Fin 2 → ℝ

/-- Field-line ODE in increasing local time with phase `phase + sign * t`. -/
def physicalFlow (phase sign t : ℝ) (x : State) : State :=
  let φ := phase + sign * t
  ![sign * (x 0 * cylBR (x 0) φ (x 1) / cylBphi (x 0) φ (x 1)),
    sign * (x 0 * cylBz (x 0) φ (x 1) / cylBphi (x 0) φ (x 1))]

/-- Polynomial value along the local clock. -/
def clockPoly (phase sign : ℝ) (p : SP) (a : ℝ × State) : ℝ :=
  atPoint p (a.2 0) (phase + sign * a.1) (a.2 1)

/-- Polynomial representation of both velocities. -/
def ratioFlow (phase sign t : ℝ) (x : State) : State :=
  ![sign * (clockPoly phase sign dnR (t,x) / clockPoly phase sign dD (t,x)),
    sign * (clockPoly phase sign dnZ (t,x) / clockPoly phase sign dD (t,x))]

private theorem clockPoly_smooth (phase sign : ℝ) (p : SP) :
    ContDiff ℝ 1 (clockPoly phase sign p) := by
  induction p with
  | nil =>
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × State => (0:ℝ)))
  | cons t ts ih =>
    change ContDiff ℝ 1 (fun a : ℝ × State =>
      (t.q:ℝ) * ((a.2 0 - dkR0)^t.a * (a.2 1)^t.b *
        (cos (2 * (phase + sign*a.1)))^t.c * (sin (2 * (phase + sign*a.1)))^t.d) +
      clockPoly phase sign ts a)
    apply ContDiff.add _ ih
    fun_prop

/-- The ratio evaluation is the identified cylindrical candidate flow. -/
theorem ratio_eq_physical (phase sign t : ℝ) (x : State) (hr : 0 < x 0)
    (hd : clockPoly phase sign dD (t,x) ≠ 0) :
    ratioFlow phase sign t x = physicalFlow phase sign t x := by
  obtain ⟨hD,hR,hZ⟩ := field_id hr (phase+sign*t) (x 1)
  unfold clockPoly at hd
  rw [hD] at hd
  have hB := right_ne_zero_of_mul hd
  have h₀ := hr.ne'
  funext i
  fin_cases i <;> simp [ratioFlow, physicalFlow, clockPoly, hD, hR, hZ] <;>
    field_simp <;> ring <;> simp

private theorem clockContinuous {f : ℝ → State → State} {T : ℝ} {lo hi x : State}
    (h : ContinuousOn (fun a : ℝ × State => f a.1 a.2) (Icc 0 T ×ˢ Icc lo hi))
    (hx : x ∈ Icc lo hi) : ContinuousOn (fun t => f t x) (Icc 0 T) := by
  have hg : ContinuousOn (fun t : ℝ => (t,x)) (Icc 0 T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  exact h.comp' hg (fun _ ht => ⟨ht,hx⟩)

/-- Produce the actual field-line step using velocity, positivity and inclusion certificates. -/
theorem exists_physical_step {phase sign T : ℝ} {lo hi vlo vhi x₀ : State}
    (hT : 0 ≤ T) (hbox : lo ≤ hi) (hR : 0 < lo 0)
    (hD : ∀ t ∈ Icc 0 T, ∀ x ∈ Icc lo hi, 0 < clockPoly phase sign dD (t,x))
    (hvel : ∀ t ∈ Icc 0 T, ∀ x ∈ Icc lo hi, ratioFlow phase sign t x ∈ Icc vlo vhi)
    (htube : ∀ t ∈ Icc 0 T, ∀ v ∈ Icc vlo vhi, x₀ + t • v ∈ Icc lo hi) :
    ∃ x : ℝ → State, x 0 = x₀ ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt x (physicalFlow phase sign t (x t)) (Icc 0 T) t ∧
      x t ∈ Icc lo hi ∧ ∃ v ∈ Icc vlo vhi, x t = x₀ + t • v := by
  let domain := Icc (0:ℝ) T ×ˢ Icc lo hi
  have hs : ContDiffOn ℝ 1 (fun a : ℝ × State => ratioFlow phase sign a.1 a.2) domain := by
    intro a ha
    have hd := (hD a.1 ha.1 a.2 ha.2).ne'
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro i
    have hc (p : SP) : ContDiffAt ℝ 1 (fun b : ℝ × State =>
        sign * (clockPoly phase sign p b / clockPoly phase sign dD b)) a :=
      contDiffAt_const.mul ((clockPoly_smooth phase sign p).contDiffAt.div
        (clockPoly_smooth phase sign dD).contDiffAt hd)
    fin_cases i
    · exact hc dnR
    · exact hc dnZ
  obtain ⟨K,hK⟩ := hs.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  have hL (t) (ht : t ∈ Icc 0 T) : LipschitzOnWith K (ratioFlow phase sign t) (Icc lo hi) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    simpa [Prod.dist_eq] using hK.dist_le_mul (t,x) ⟨ht,hx⟩ (t,y) ⟨ht,hy⟩
  have hC (x) (hx : x ∈ Icc lo hi) :
      ContinuousOn (fun t => ratioFlow phase sign t x) (Icc 0 T) :=
    clockContinuous (f := ratioFlow phase sign) hs.continuousOn hx
  obtain ⟨x, hx, he⟩ := exists_step (f := ratioFlow phase sign) hT hbox hL hC hvel htube
  refine ⟨x,hx,fun t ht => ?_⟩
  obtain ⟨hd,hm,hv⟩ := he t ht
  rw [ratio_eq_physical _ _ _ _ (hR.trans_le (hm.1 0)) (hD t ht _ hm).ne'] at hd
  exact ⟨hd,hm,hv⟩

end PlasmaLean.Design.DommaschkBounceField
