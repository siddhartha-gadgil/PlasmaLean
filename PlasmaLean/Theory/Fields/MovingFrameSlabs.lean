/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.TrajectorySlabs
public import PlasmaLean.Theory.Fields.MovingFrameTrajectory

/-!
# Connecting moving-frame enclosures to a physical trajectory

A known defect, logarithmic norm and incoming radius give the propagated radius
on a closed time slab. The local theorem starts from every point of the incoming
ellipsoid. Containment at a change of reference or frame lets the next slab
start with the physical endpoint produced by the previous one.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.TrajectorySlabs.MovingFrame

open Set
open scoped RealInnerProductSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Physical points within a specified norm radius in the given frame. -/
def ellipsoid (M : E ≃L[ℝ] E) (p : E) (r : ℝ) : Set E :=
  {x | ‖M.symm (x - p)‖ ≤ r}

/-- Exact handoff test when two reference polynomials share their endpoint frame. -/
theorem ellipsoid_shift (M : E ≃L[ℝ] E) (old next : E) {out incoming : ℝ}
    (handoff : out + ‖M.symm (old - next)‖ ≤ incoming) :
    ellipsoid M old out ⊆ ellipsoid M next incoming := by
  intro x hx
  exact (LogNormTrajectory.MovingFrame.radius_after_reference_jump M x old next).trans
    ((add_le_add hx le_rfl).trans handoff)

/-- A change of frame uses the operator norm of the transition map and the
displacement of the two reference points in the incoming frame. -/
theorem ellipsoid_change (M N : E ≃L[ℝ] E) (old next : E) {out incoming : ℝ}
    (handoff : ‖N.symm.toContinuousLinearMap.comp M.toContinuousLinearMap‖ * out +
      ‖N.symm (old - next)‖ ≤ incoming) :
    ellipsoid M old out ⊆ ellipsoid N next incoming := by
  intro x hx
  have bound := (N.symm.toContinuousLinearMap.comp M.toContinuousLinearMap).le_opNorm_of_le hx
  change ‖N.symm (M (M.symm (x - old)))‖ ≤ _ at bound
  rw [M.apply_symm_apply] at bound
  exact (LogNormTrajectory.MovingFrame.radius_after_reference_jump N x old next).trans
    ((add_le_add bound le_rfl).trans handoff)

/-- A verified inclusion can pass the previous exit set into the next solver. -/
theorem restrict_entry {F : ℝ → E → E} {s : Slab E} {entry old exit : Set E}
    (step : Step F s old exit) (included : entry ⊆ old) : Step F s entry exit :=
  ⟨step.ordered, fun x hx => step.solve x (included hx)⟩

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform propagated frame radius from the one-sided estimate on one interval. -/
def propagated (a b incoming logNorm defect : ℝ) : ℝ :=
  (incoming + (b - a) * defect) / (1 - max 0 logNorm * (b - a))

/-- Frame and physical norm bounds on the full interval certified by the local solver. -/
def slab (a b : ℝ) (p : ℝ → E) (M : ℝ → E ≃L[ℝ] E) (out : ℝ) : Slab E :=
  ⟨a, b, fun t => ellipsoid (M t) (p t) out ∩
    {x | dist x (p t) ≤ ‖(M t).toContinuousLinearMap‖ * out}⟩

/-- The analytic moving-frame theorem certifies a step for every initial state
in the incoming ellipsoid. Both its whole-slab bounds become enclosures on the
single trajectory returned by `Chain.exists_trajectory`. -/
theorem step_of_defect [CompleteSpace E] {F : ℝ → E → E} {J : ℝ → E → E →L[ℝ] E}
    {p dp : ℝ → E} {M : ℝ → E ≃L[ℝ] E} {dM : ℝ → E →L[ℝ] E} {S : Set E}
    {a b r L ε T : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hLen : max 0 L * (b - a) < 1) (hTrial : propagated a b r L ε < T)
    (hS : IsCompact S) (hconv : Convex ℝ S) (hTube : Metric.closedBall (0 : E) T ⊆ S)
    (hRet : ∃ P : E → E, LipschitzWith 1 P ∧ (∀ v, P v ∈ S) ∧ ∀ v ∈ S, P v = v)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (dp t) (Icc a b) t)
    (hM : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u => (M u).toContinuousLinearMap) (dM t) (Icc a b) t)
    (hcInv : ContinuousOn (fun t => (M t).symm.toContinuousLinearMap) (Icc a b))
    (hcdp : ContinuousOn dp (Icc a b)) (hcdM : ContinuousOn dM (Icc a b))
    (hF : ContinuousOn (fun q : ℝ × E => F q.1 (p q.1 + M q.1 q.2)) (Icc a b ×ˢ S))
    (hJ : ContinuousOn (fun q : ℝ × E => J q.1 (p q.1 + M q.1 q.2)) (Icc a b ×ˢ S))
    (hd : ∀ t ∈ Icc a b, ∀ v ∈ S, HasFDerivAt (F t) (J t (p t + M t v)) (p t + M t v))
    (quad : ∀ t ∈ Ico a b, ∀ v ∈ Metric.closedBall (0 : E) T, ∀ d : E,
      ⟪d, LogNormTrajectory.MovingFrame.jacobian (J t (p t + M t v)) (M t) (dM t) d⟫ ≤
        L * ‖d‖ ^ 2)
    (hres : ∀ t ∈ Ico a b, ‖(M t).symm (F t (p t) - dp t)‖ ≤ ε) :
    Step F (slab a b p M (propagated a b r L ε)) (ellipsoid (M a) (p a) r)
      (ellipsoid (M b) (p b) (propagated a b r L ε)) := by
  refine ⟨hab, fun x hx => ?_⟩
  obtain ⟨v, start, bounds⟩ := LogNormTrajectory.MovingFrame.exists_rational_step
    hab hr hε hLen hTrial hS hconv hTube hRet hp hM hcInv hcdp hcdM hF hJ hd quad hres hx
  exact ⟨v, start, (bounds b (right_mem_Icc.mpr hab)).2.1,
    fun t ht => ⟨(bounds t ht).1, (bounds t ht).2⟩⟩

/-- Enlarging the exact analytic propagated radius to a checked dyadic upper bound
preserves the frame, physical norm, and endpoint guarantees needed by the chain. -/
theorem round_outward {F : ℝ → E → E} {p : ℝ → E} {M : ℝ → E ≃L[ℝ] E}
    {a b tight out : ℝ} {entry : Set E}
    (step : Step F (slab a b p M tight) entry (ellipsoid (M b) (p b) tight))
    (bound : tight ≤ out) :
    Step F (slab a b p M out) entry (ellipsoid (M b) (p b) out) := by
  refine ⟨step.ordered, fun x hx => ?_⟩
  obtain ⟨v, start, final, h⟩ := step.solve x hx
  refine ⟨v, start, (le_trans final bound), fun t ht => ?_⟩
  obtain ⟨der, frame, physical⟩ := h t ht
  exact ⟨der, le_trans frame bound,
    physical.trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))⟩

/-- A zero defect and nonpositive logarithmic norm pass the incoming radius unchanged. -/
theorem propagated_zero_defect (a b r : ℝ) {L : ℝ} (hL : L ≤ 0) :
    propagated a b r L 0 = r := by simp [propagated, max_eq_left hL]

end Hilbert
end PlasmaLean.Fields.TrajectorySlabs.MovingFrame
