/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBackwardRectangle
public import PlasmaLean.Design.DommaschkEndpointSignedTrace

/-! # Continuing physical field lines from either canonical section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkEndpointContinuation

open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkBounceTaylor Set
open DommaschkPhysicalTraceStep DommaschkKam DommaschkKam.DkPoly DommaschkJacobian
open DommaschkBounceField (atPoint)
open scoped RealInnerProductSpace

/-- A forward reference-centred rectangle can be enlarged to also cover its reflected
partner. The scalar frame and defect remain those of the forward physical row. -/
theorem forward_rectangle {lim : Limits} {s : State} {r : Step} {a α : ℝ} {box : Inputs}
    {left right : Frame} {radial vertical : ℕ} (ok : test lim s r = true)
    (axes : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (centres : CenterMatches r box)
    (u : (box.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (z : (box.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    (safe : box.u.radius + magnitude (difference box.u.poly [0]) ≤ 1 / 2)
    (l : s.frame = left) (c : r.frame = right)
    (den : ∀ t ∈ Icc a (a + 1 / 64), ∀ R z,
      box.u.Mem (coord a t) (R - dkR0) → box.z.Mem (coord a t) z → 0 < atPoint dD R (α + t) z)
    (jac : ∀ t ∈ Icc a (a + 1 / 64), ∀ R z,
      box.u.Mem (coord a t) (R - dkR0) → box.z.Mem (coord a t) z → ∀ w : Plane,
      ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
        (spatialMatrix (R - dkR0) z (Real.cos (2 * (α + t))) (Real.sin (2 * (α + t))))
        (frameEquiv left right (coord a t)) (frameVelocity left right) w⟫ ≤ r.mu * ‖w‖ ^ 2)
    (res : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
      (euclideanFlow α 1 t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect) :
    FieldBounds s r a (euclideanFlow α 1) (velocityJacobian α 1) ballDomain := by
  apply DommaschkPhysicalTraceStep.field_bounds ok _ _ res
  · intro t ht v hv
    let x := reference a r t + moving s r a t v
    obtain ⟨hu, hz⟩ := DommaschkProjectedTrial.trial_membership ok centres axes u z ht hv
    have hr := enclose (c := ⟨[0], 1 / 2⟩) (abs_coord_le ht) hu safe
    change (⟨[0], 1 / 2⟩ : Model).Mem (coord a t) (x 0 - dkR0) at hr
    norm_num [Model.Mem, dkR0, abs_le] at hr
    have pos : 0 < x 0 := by linarith
    exact ⟨pos, by simpa only [one_mul] using (den t ht (x 0) (x 1) hu hz).ne'⟩
  · intro t ht v hv w
    let x := reference a r t + moving s r a t v
    have ht' := Ico_subset_Icc_self ht
    obtain ⟨hu, hz⟩ := DommaschkProjectedTrial.trial_membership ok centres axes u z ht' hv
    have hj := jac t ht' (x 0) (x 1) hu hz w
    change ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian α 1 t x)
      (moving s r a t) (frameVelocity s.frame r.frame) w⟫ ≤ _
    rw [velocityJacobian_spatial]
    simpa only [one_mul, one_smul, moving, l, c] using hj

/-- Prepend a physical step on the archive's uniform clock. -/
theorem cons_step (i : ℕ) {F : ℝ → Plane → Plane} {s : State} {r : Step} {rows : List Step}
    {endTime : ℝ} {exit : Set Plane}
    (first : Fields.TrajectorySlabs.Step F (physicalSlab s r (i / 64))
      (stateSet s) (stateSet (next r)))
    (rest : Fields.TrajectorySlabs.Chain F (((i + 1 : ℕ) : ℝ) / 64) (stateSet (next r)) endTime exit
      (physicalSlabs (next r) (((i + 1 : ℕ) : ℝ) / 64) rows)) :
    Fields.TrajectorySlabs.Chain F (i / 64) (stateSet s) endTime exit
      (physicalSlabs s (i / 64) (r::rows)) := by
  have time : (i : ℝ) / 64 + 1 / 64 = ((i + 1 : ℕ) : ℝ) / 64 := by push_cast; ring
  unfold physicalSlabs
  apply Fields.TrajectorySlabs.Chain.cons first
  change Fields.TrajectorySlabs.Chain F ((i : ℝ) / 64 + 1 / 64) _ _ _ _
  simpa only [time] using rest

open DommaschkMirrorLaunch DommaschkEndpointSignedTrace DommaschkKamC KamNewton
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- The short signed pilot passage and a second endpoint passage can refer to exactly
the same nested tori, even when their angular extents are different. -/
def WithPilot (e : MirrorEndpoint) (T : ℝ) (fe be : Set Plane)
    (fs bs : List (Fields.TrajectorySlabs.Slab Plane)) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    (∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → FourSlabPassage uC zC uA zA φ) ∧
    (∀ φ : ℝ, |φ - azimuth e.opposite| ≤ e.width → FromBirth e uC zC uA zA φ T fe be fs bs)

theorem with_pilot_of_entry {e : MirrorEndpoint} {T : ℝ} {fe be : Set Plane}
    {fs bs : List (Fields.TrajectorySlabs.Slab Plane)}
    (path : ∀ {uC zC uA zA : FA} {φ : ℝ}, SectionEntry e uC zC uA zA φ →
      FromBirth e uC zC uA zA φ T fe be fs bs) : WithPilot e T fe be fs bs := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, entries⟩ := exists_nested_section_entry
  refine ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, ?_, fun φ hp => path (entries e φ hp)⟩
  intro φ hp
  apply four_slabs_of_entry (entries .q0r470 φ ?_)
  simpa [MirrorEndpoint.width, MirrorEndpoint.opposite, azimuth] using hp

end PlasmaLean.Design.DommaschkEndpointContinuation
