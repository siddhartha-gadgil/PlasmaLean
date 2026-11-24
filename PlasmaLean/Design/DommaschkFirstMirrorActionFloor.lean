/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedActionFloor

/-! # Lower bounds on the physical action between the first two mirror contacts -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFirstMirrorActionFloor

open Certificates.PositionFrameSlabs DommaschkSignedTraceDomain DommaschkJacobian
open DommaschkSignedActionFloor DommaschkSignedObservable DommaschkMirrorTubeCrossing
open Kinetic.CylindricalActionSensitivity MeasureTheory Set

/-- True field and speed regularity imply integrability on the complete interval,
including a bracket extending past a mirror. -/
theorem integrable {a b : ℝ} {y : ℝ → Plane} (hab : a ≤ b) (h : ℝ)
    (ode : ∀ t ∈ Icc a b, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc a b) t)
    (region : ∀ t ∈ Icc a b, Region (y t)) : IntervalIntegrable (integrand h y) volume a b := by
  have cy : ContinuousOn y (Icc a b) := fun t ht => (ode t ht).continuousWithinAt
  have cb : ContinuousOn (fun t => strength t (y t)) (Icc a b) := by
    simpa only [one_mul] using continuousOn_strength cy 1
      (fun t ht => by linarith [(region t ht).1.1])
  obtain ⟨low, cap⟩ := isCompact_Icc.bddAbove_image cb
  exact (action_floor (h := h) hab ode region (fun t ht => cap (mem_image_of_mem _ ht))).1

/-- One-sided action between the earliest mirrors surrounding this birth,
with the same true trajectory furnishing both mirror states and the integral. -/
def FirstAction (near far h floor : ℝ) (y : ℝ → Plane) : Prop :=
  ∃ pos ∈ Ioo near far, ∃ back ∈ Ioo near far,
    strength pos (y pos) = h ∧ (∀ t ∈ Ico 0 pos, strength t (y t) < h) ∧
    strength (-back) (y (-back)) = h ∧ (∀ t ∈ Ico 0 back, strength (-t) (y (-t)) < h) ∧
    IntervalIntegrable (integrand h y) volume (-back) pos ∧
    floor < physicalAction (fun t => y t 0) (fun t => y t 1) (fun t => strength t (y t))
      (-back) pos h

/-- The contribution of any verified inner window lower-bounds the complete
physical action from the first negative mirror to the first positive mirror. -/
theorem from_core {y : ℝ → Plane} {near far limit cut h floor : ℝ}
    (contacts : FirstBoth near far h y) (hcut : 0 ≤ cut) (inner : cut ≤ near) (outer : far ≤ limit)
    (ode : ∀ t ∈ Icc (-limit) limit,
      HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-limit) limit) t)
    (region : ∀ t ∈ Icc (-limit) limit, Region (y t))
    (mass : floor < physicalAction (fun t => y t 0) (fun t => y t 1)
      (fun t => strength t (y t)) (-cut) cut h) : FirstAction near far h floor y := by
  obtain ⟨⟨pos, hp, eqp, beforep⟩, ⟨back, hb, eqb, beforeb⟩⟩ := contacts
  have left : -back ≤ -cut := neg_le_neg (inner.trans hb.1.le)
  have right : cut ≤ pos := inner.trans hp.1.le
  have middle : -cut ≤ cut := by linarith
  have within : Icc (-back) pos ⊆ Icc (-limit) limit :=
    Icc_subset_Icc (neg_le_neg (hb.2.le.trans outer)) (hp.2.le.trans outer)
  have feasible := integrable (left.trans (middle.trans right)) h
    (fun t ht => (ode t (within ht)).mono within) (fun t ht => region t (within ht))
  refine ⟨pos, hp, back, hb, eqp, beforep, eqb, beforeb, feasible, mass.trans_le ?_⟩
  exact intervalIntegral.integral_mono_interval left middle right
    (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
    feasible

end PlasmaLean.Design.DommaschkFirstMirrorActionFloor
