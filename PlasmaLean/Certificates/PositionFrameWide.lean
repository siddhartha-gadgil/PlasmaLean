/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameODE

/-! # Propagation on a moving frame with a user-supplied physical tube -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameWide
open Set PositionFrameSlabs
open scoped RealInnerProductSpace
set_option linter.style.longLine false

/-- The conditions used by first exit, endpoint matching and conversion to physical distance. -/
def growth (s : State) (r : Step) : Bool :=
  let g := max 0 r.mu
  (r.incoming == s.radius + r.jumpBound) && leQ 0 r.defect && ltQ g 64 &&
    leQ (64 * r.incoming + 2^80 * r.defect) (r.outgoing * (64-g)) &&
    r.outgoing.blt r.trial && leQ (r.op * r.outgoing) r.physicalOut

def valid (s : State) (r : Step) : Bool := geometry allLimits s r && growth s r

/-- Any absolute width goal can be checked separately from the propagation of these radii. -/
theorem growth_sound {s : State} {r : Step} (h : growth s r = true) :
    r.incoming = s.radius + r.jumpBound ∧ 0 ≤ (r.defect : ℝ) ∧
    max 0 (r.mu : ℝ) / 64 < 1 ∧
    ((r.incoming : ℝ) / 2^80 + r.defect / 64) / (1 - max 0 (r.mu : ℝ) / 64) ≤ (r.outgoing : ℝ) / 2^80 ∧
    (r.outgoing : ℝ) / 2^80 < (r.trial : ℝ) / 2^80 ∧ (r.op : ℝ) * r.outgoing ≤ r.physicalOut := by
  simp only [growth, Bool.and_eq_true, beq_iff_eq, leQ_true, ltQ_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨initial, defect⟩, rate⟩, propagated⟩, trial⟩, physical⟩ := h
  have rate' : max 0 (r.mu : ℝ) < 64 := by exact_mod_cast rate
  have bound : 64 * (r.incoming : ℝ) + 2^80 * (r.defect : ℝ) ≤
      r.outgoing * (64 - max 0 (r.mu : ℝ)) := by exact_mod_cast propagated
  refine ⟨initial, by exact_mod_cast defect, by linarith, ?_, ?_, by exact_mod_cast physical⟩
  · apply (div_le_iff₀ (by linarith)).mpr
    nlinarith only [bound]
  · gcongr

/-- Solve the actual IVP and carry the original physical tube and endpoint through this step. -/
theorem physical_step_on {domain : RegularityDomain} {s : State} {r : Step}
    {a : ℝ} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (ok : valid s r = true) (bounds : FieldBounds s r a F J domain) :
    Fields.TrajectorySlabs.Step F (physicalSlab s r a) (stateSet s) (stateSet (next r)) := by
  obtain ⟨hg,hr⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨inc,hε,hlen,hprop,htrial,hop⟩ := growth_sound hr
  have ab : a ≤ a + 1 / 64 := by linarith
  have len : a + 1 / 64-a = (1 / 64 : ℝ) := by ring
  have tight : Fields.TrajectorySlabs.MovingFrame.propagated a (a + 1 / 64)
      (r.incoming/(2:ℝ)^80) r.mu r.defect ≤ r.outgoing/(2:ℝ)^80 := by
    simpa only [Fields.TrajectorySlabs.MovingFrame.propagated, len, mul_one_div, one_div_mul_eq_div]
      using hprop
  obtain ⟨compact,conv,tube,retract⟩ := domain.facts (T := r.trial/(2:ℝ)^80) (by positivity)
  have step := Fields.TrajectorySlabs.MovingFrame.step_of_defect
    (a := a) (b := a + 1 / 64) (r := r.incoming/(2:ℝ)^80) (L := (r.mu : ℝ))
    (ε := (r.defect : ℝ)) (T := r.trial/(2:ℝ)^80) ab (by positivity) hε
    (by simpa only [len, mul_one_div] using hlen) (tight.trans_lt htrial)
    compact conv tube retract (fun t _ => (hasDerivAt_reference a r t).hasDerivWithinAt)
    (fun _ ht => hasDerivWithinAt_frame hg a ht) (continuousOn_frame_inverse hg a)
    (continuous_referenceVelocity a r).continuousOn continuousOn_const
    bounds.field bounds.jac bounds.derivative bounds.quadratic bounds.residual
  have rounded := Fields.TrajectorySlabs.MovingFrame.round_outward step tight
  have start : moving s r a a = frameEquiv s.frame s.frame 0 := by
    simpa [moving,coord] using frame_start hg
  have stop : moving s r a (a + 1 / 64) = frameEquiv r.frame r.frame 0 := by
    have z : coord a (a + 1 / 64) = 1 := by unfold coord; ring
    simpa only [moving,z] using frame_end hg
  have shift : stateSet s ⊆ Fields.TrajectorySlabs.MovingFrame.ellipsoid
        (moving s r a a) (reference a r a) (r.incoming/(2:ℝ)^80) := by
    rw [reference_start,start]
    apply Fields.TrajectorySlabs.MovingFrame.ellipsoid_shift
    have hj := norm_reference_jump hg
    rw [frame_start hg] at hj
    rw [inc,Nat.cast_add,add_div]
    exact add_le_add le_rfl hj
  refine ⟨ab,fun x hx => ?_⟩
  obtain ⟨v,x₀,final,within⟩ := rounded.solve x (shift hx)
  refine ⟨v,x₀,?_,fun t ht => ?_⟩
  · change v (a + 1 / 64) ∈ Fields.TrajectorySlabs.MovingFrame.ellipsoid
      (moving s r a (a + 1 / 64)) (reference a r (a + 1 / 64)) (r.outgoing/(2:ℝ)^80) at final
    simpa only [stop,reference_end,stateSet,next,physicalSlab] using final
  · obtain ⟨deriv,ellipsoid,physical⟩ := within t ht
    refine ⟨deriv,ellipsoid,?_⟩
    change dist (v t) (reference a r t) ≤ r.physicalOut/(2:ℝ)^80
    change dist (v t) (reference a r t) ≤ ‖(moving s r a t).toContinuousLinearMap‖ * _ at physical
    apply physical.trans
    apply (mul_le_mul_of_nonneg_right (frame_op_norm hg (abs_coord_le ht)) (by positivity)).trans
    simpa only [← mul_div_assoc] using div_le_div_of_nonneg_right hop (by positivity : (0:ℝ) ≤ 2^80)

end PlasmaLean.Certificates.PositionFrameWide
