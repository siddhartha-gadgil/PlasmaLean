/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameWide
public import PlasmaLean.Theory.Fields.MovingFrameBackward

/-!
# Backward steps and two-sided distances for position-frame records

A lower bound for the quadratic form of the frame Jacobian on the trial ball of one
recorded slab lets every point of a frame ball at a time of the slab be followed back to
the start of the slab. Together with the recorded upper bound it also compares the frame
separation of two solutions at two times of the slab.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameBackward

open Set PositionFrameSlabs
open scoped RealInnerProductSpace

/-- Lower logarithmic-norm bound of one slab on the whole trial ball and the closed slab. -/
def Lower (s : State) (r : Step) (a : ℝ) (J : ℝ → Plane → Plane →L[ℝ] Plane) : Prop :=
  ∀ t ∈ Icc a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
    ∀ w : Plane, -((r.mu : ℝ) * ‖w‖ ^ 2) ≤ ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (J t (reference a r t + moving s r a t v)) (moving s r a t)
      (frameVelocity s.frame r.frame) w⟫

/-- The recorded defect bound extends from the half-open slab to its right endpoint. -/
theorem residual_closed {domain : RegularityDomain} {lim : Limits} {s : State} {r : Step}
    {a : ℝ} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (geo : geometry lim s r = true) (bounds : FieldBounds s r a F J domain) :
    ∀ t ∈ Icc a (a + 1 / 64),
      ‖(moving s r a t).symm (F t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect := by
  have zero : (0 : Plane) ∈ domain.region (r.trial / (2 : ℝ) ^ 80) :=
    (domain.facts (by positivity)).2.2.1 (Metric.mem_closedBall_self (by positivity))
  have cF : ContinuousOn (fun t => F t (reference a r t)) (Icc a (a + 1 / 64)) := by
    have h := bounds.field.comp (f := fun t : ℝ => ((t, 0) : ℝ × Plane))
      (by fun_prop : Continuous fun t : ℝ => ((t, 0) : ℝ × Plane)).continuousOn
      (fun t ht => ⟨ht, zero⟩)
    simpa only [Function.comp_def, map_zero, add_zero] using h
  have cont : ContinuousOn (fun t => ‖(moving s r a t).symm
      (F t (reference a r t) - referenceVelocity a r t)‖) (Icc a (a + 1 / 64)) :=
    ((continuousOn_frame_inverse geo a).clm_apply
      (cF.sub (continuous_referenceVelocity a r).continuousOn)).norm
  intro t ht
  have hcl : t ∈ closure (Ico a (a + 1 / 64)) := by
    rw [closure_Ico (by linarith : a < a + 1 / 64).ne]
    exact ht
  exact ContinuousWithinAt.closure_le hcl ((cont t ht).mono Ico_subset_Icc_self)
    continuousWithinAt_const bounds.residual

/-- Backward step inside one recorded slab. Every point within frame radius `ρ` of the
reference at a time `t₁` of the slab is the value at `t₁` of a solution defined back to
the start of the slab, which stays within the propagated frame radius. -/
theorem backward_step {domain : RegularityDomain} {lim : Limits} {s : State} {r : Step} {a : ℝ}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (geo : geometry lim s r = true) (bounds : FieldBounds s r a F J domain) (lower : Lower s r a J)
    (defect : 0 ≤ (r.defect : ℝ)) (rate : max 0 (r.mu : ℝ) / 64 < 1)
    {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : (ρ + r.defect / 64) / (1 - max 0 (r.mu : ℝ) / 64) ≤ σ)
    (trial : σ < r.trial / (2 : ℝ) ^ 80)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a (a + 1 / 64)) {x : Plane}
    (hx : ‖(moving s r a t₁).symm (x - reference a r t₁)‖ ≤ ρ) :
    ∃ v : ℝ → Plane, v t₁ = x ∧ ∀ t ∈ Icc a t₁,
      HasDerivWithinAt v (F t (v t)) (Icc a t₁) t ∧
      ‖(moving s r a t).symm (v t - reference a r t)‖ ≤ σ := by
  have sub : Icc a t₁ ⊆ Icc a (a + 1 / 64) := Icc_subset_Icc_right ht₁.2
  have len : a + 1 / 64 - a = (1 / 64 : ℝ) := by ring
  have full : max 0 (r.mu : ℝ) * (a + 1 / 64 - a) < 1 := by
    simpa only [len, mul_one_div] using rate
  have tight : Fields.TrajectorySlabs.MovingFrame.propagated a t₁ ρ r.mu r.defect ≤ σ := by
    refine (Fields.TrajectorySlabs.MovingFrame.propagated_mono_right ht₁.1 ht₁.2 hρ defect
      full).trans ?_
    simpa only [Fields.TrajectorySlabs.MovingFrame.propagated, len, mul_one_div,
      one_div_mul_eq_div] using hσ
  have short : max 0 (r.mu : ℝ) * (t₁ - a) < 1 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right ht₁.2 a) (le_max_left _ _)).trans_lt full
  obtain ⟨compact, conv, tube, retract⟩ :=
    domain.facts (T := r.trial / (2 : ℝ) ^ 80) (by positivity)
  have region : Icc a t₁ ×ˢ domain.region (r.trial / (2 : ℝ) ^ 80) ⊆
      Icc a (a + 1 / 64) ×ˢ domain.region (r.trial / (2 : ℝ) ^ 80) :=
    prod_mono sub subset_rfl
  obtain ⟨v, stop, _, within⟩ := Fields.TrajectorySlabs.MovingFrame.backward_step_of_defect
    (a := a) (b := t₁) (r := ρ) (L := (r.mu : ℝ)) (ε := (r.defect : ℝ))
    (T := r.trial / (2 : ℝ) ^ 80) (M := moving s r a) ht₁.1 hρ defect short
    (tight.trans_lt trial) compact conv tube retract
    (fun t _ => (hasDerivAt_reference a r t).hasDerivWithinAt)
    (fun _ ht => (hasDerivWithinAt_frame geo a (sub ht)).mono sub)
    ((continuousOn_frame_inverse geo a).mono sub)
    (continuous_referenceVelocity a r).continuousOn continuousOn_const
    (bounds.field.mono region) (bounds.jac.mono region)
    (fun t ht => bounds.derivative t (sub ht))
    (fun t ht => lower t (sub (Ioc_subset_Icc_self ht)))
    (fun t ht => residual_closed geo bounds t (sub (Ioc_subset_Icc_self ht))) x hx
  exact ⟨v, stop, fun t ht => ⟨(within t ht).1, (within t ht).2.trans tight⟩⟩

/-- Two solutions that stay in the trial ball of one recorded slab between two times
have frame separations at these times within the factor `exp (max 0 μ (t₁ - t₀))` of
each other. -/
theorem frame_dist_le {domain : RegularityDomain} {lim : Limits} {s : State} {r : Step} {a : ℝ}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (geo : geometry lim s r = true) (bounds : FieldBounds s r a F J domain) (lower : Lower s r a J)
    {t₀ t₁ : ℝ} (h₀ : a ≤ t₀) (h₀₁ : t₀ ≤ t₁) (h₁ : t₁ ≤ a + 1 / 64) {x₁ x₂ : ℝ → Plane}
    (hx₁ : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt x₁ (F t (x₁ t)) (Icc t₀ t₁) t)
    (hx₂ : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt x₂ (F t (x₂ t)) (Icc t₀ t₁) t)
    (hm₁ : ∀ t ∈ Ioo t₀ t₁,
      ‖(moving s r a t).symm (x₁ t - reference a r t)‖ ≤ r.trial / (2 : ℝ) ^ 80)
    (hm₂ : ∀ t ∈ Ioo t₀ t₁,
      ‖(moving s r a t).symm (x₂ t - reference a r t)‖ ≤ r.trial / (2 : ℝ) ^ 80) :
    ‖(moving s r a t₀).symm (x₁ t₀ - x₂ t₀)‖ ≤ Real.exp (max 0 (r.mu : ℝ) * (t₁ - t₀)) *
      ‖(moving s r a t₁).symm (x₁ t₁ - x₂ t₁)‖ ∧
    ‖(moving s r a t₁).symm (x₁ t₁ - x₂ t₁)‖ ≤ Real.exp (max 0 (r.mu : ℝ) * (t₁ - t₀)) *
      ‖(moving s r a t₀).symm (x₁ t₀ - x₂ t₀)‖ := by
  have sub : Icc t₀ t₁ ⊆ Icc a (a + 1 / 64) := Icc_subset_Icc h₀ h₁
  have sub' : Ico t₀ t₁ ⊆ Ico a (a + 1 / 64) := Ico_subset_Ico h₀ h₁
  have tube := (domain.facts (T := r.trial / (2 : ℝ) ^ 80) (by positivity)).2.2.1
  have cref : Continuous (reference a r) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_reference a r t).continuousAt
  exact Fields.TrajectorySlabs.MovingFrame.norm_symm_sub_le_exp_mul (M := moving s r a)
    (J := J) (dM := fun _ => frameVelocity s.frame r.frame) (L := max 0 (r.mu : ℝ))
    (T := r.trial / (2 : ℝ) ^ 80) h₀₁ cref.continuousOn
    (fun _ ht => (hasDerivWithinAt_frame geo a (sub ht)).mono sub)
    ((continuousOn_frame_inverse geo a).mono sub)
    (fun t ht v hv => bounds.derivative t (sub (Ico_subset_Icc_self ht)) v (tube hv))
    (fun t ht v hv w => (bounds.quadratic t (sub' ht) v hv w).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))
    (fun t ht v hv w => (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (sq_nonneg _))).trans (lower t (sub (Ico_subset_Icc_self ht)) v hv w))
    hx₁ hx₂ hm₁ hm₂

/-- The stationary record with the zero field satisfies the lower bound. -/
theorem lower_stationary (a : ℝ) : Lower (next stationary) stationary a (fun _ _ => 0) := by
  intro t _ v _ w
  have frame : frameVelocity (next stationary).frame stationary.frame = 0 := by
    simp [frameVelocity, next, forward, entry]
  rw [frame]
  simp [Fields.LogNormTrajectory.MovingFrame.jacobian, stationary]

/-- For the stationary record with the zero field all hypotheses of `backward_step` hold:
the reference point at any time of the slab is the endpoint of a solution on the earlier
part of the slab that stays at frame distance zero from the reference. -/
theorem stationary_backward_step (a : ℝ) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a (a + 1 / 64)) :
    ∃ v : ℝ → Plane, v t₁ = reference a stationary t₁ ∧ ∀ t ∈ Icc a t₁,
      HasDerivWithinAt v 0 (Icc a t₁) t ∧
      ‖(moving (next stationary) stationary a t).symm (v t - reference a stationary t)‖ ≤ 0 := by
  have geo : geometry pilotLimits (next stationary) stationary = true :=
    (Bool.and_eq_true_iff.mp stationary_checked).1
  have velocity (t : ℝ) : referenceVelocity a stationary t = 0 := by
    ext i
    fin_cases i <;> norm_num [referenceVelocity, polynomial, stationary,
      TrajectoryTaylorModel.ofDyadic, QPoly.scale, QPoly.deriv, QPoly.add, QPoly.eval,
      List.replicate_succ]
  have frame : frameVelocity (next stationary).frame stationary.frame = 0 := by
    simp [frameVelocity, next, forward, entry]
  have bounds : FieldBounds (next stationary) stationary a (fun _ _ => 0) (fun _ _ => 0) := by
    refine ⟨continuousOn_const, continuousOn_const, fun _ _ _ _ => hasFDerivAt_const _ _, ?_, ?_⟩
    · intro t _ v _ w
      rw [frame]
      simp [Fields.LogNormTrajectory.MovingFrame.jacobian, stationary]
    · intro t _
      rw [velocity]
      simp [stationary]
  exact backward_step (F := fun _ _ => 0) geo bounds (lower_stationary a)
    (by simp [stationary]) (by simp [stationary]) le_rfl (by simp [stationary])
    (by simp [stationary]) ht₁ (by simp)

end PlasmaLean.Certificates.PositionFrameBackward
