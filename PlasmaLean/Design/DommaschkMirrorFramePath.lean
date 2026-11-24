/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFrameLaunch
public import PlasmaLean.Design.DommaschkPhysicalJacobian
public import PlasmaLean.Certificates.PositionFrameBall
public import PlasmaLean.Certificates.PositionFrameChain

/-!
# Sufficient per-row bounds for the physical long field-line trace

The same pair of Q-16 surfaces works for every endpoint, both outward directions
and every checked prefix of the stored trace. The remaining analytic input is a
field-bound certificate on each recorded trial ball.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKamC KamNewton Set
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2

/-- A physical approach to the section followed by a specified outward trace. The two
segments share their physical state. Every enclosure in the list applies to the same trace. -/
def FollowsFrames (e : MirrorEndpoint) (uC zC uA zA : FA) (φ sign : ℝ) (n : ℕ)
    (exit : Certificates.PositionFrameSlabs.State) (rows : List Step) : Prop :=
  let phase := azimuth e.opposite
  let duration := |φ - phase|
  ∃ (approachSign : ℝ) (approach path : ℝ → DommaschkBounceField.State),
    |approachSign| = 1 ∧ φ + approachSign * duration = phase ∧
    approach 0 = birth uC zC uA zA e.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt approach
      (physicalFlow φ approachSign t (approach t)) (Icc 0 duration) t) ∧
    path 0 = approach duration ∧ coordinates.symm (path (n / 64)) ∈ stateSet exit ∧
    (∀ t ∈ Icc 0 (n / 64 : ℝ), HasDerivWithinAt path (physicalFlow phase sign t (path t))
      (Icc 0 (n / 64)) t) ∧
    ∀ slab ∈ physicalSlabs e.start 0 rows, ∀ t ∈ Icc slab.start slab.stop,
      coordinates.symm (path t) ∈ slab.tube t

/-- Discharging the actual QA2R field bounds on each accepted trial ball suffices for
the physical trace, pointwise through the full recorded interval. -/
theorem followsFrames_of_bounds {e : MirrorEndpoint} {uC zC uA zA : FA} {φ sign : ℝ}
    {n : ℕ} {lim : Limits} {exit : Certificates.PositionFrameSlabs.State} {blocks : List (List Step)}
    (hEntry : SectionEntry e uC zC uA zA φ) (accepted : Chain lim e.start blocks n exit)
    (bounds : FieldBoundsOn (DommaschkJacobian.euclideanFlow (azimuth e.opposite) sign)
      (DommaschkJacobian.velocityJacobian (azimuth e.opposite) sign) e.start 0
      blocks.flatten ballDomain) : FollowsFrames e uC zC uA zA φ sign n exit blocks.flatten := by
  obtain ⟨direction, approach, hd, ha, hb, ode, ball⟩ := hEntry
  have identity : e.start.frame = ⟨2^40, 0, 0, 2^40⟩ := by cases e <;> rfl
  have member : coordinates.symm (approach |φ - azimuth e.opposite|) ∈ stateSet e.start :=
    (mem_stateSet_identity identity _).mpr ball
  obtain ⟨path, same, out, flow, tubes⟩ := accepted.cartesian_trajectory
    (F := physicalFlow (azimuth e.opposite) sign) bounds member
  exact ⟨direction, approach, path, hd, ha, hb, ode, same, by simpa using out,
    by simpa using flow, tubes⟩

/-- The same pair of nested physical tori supports every certified trace and every
certified prefix, for every birth in the applicable endpoint sector. -/
theorem exists_nested_frame_paths :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ (e : MirrorEndpoint) (φ sign : ℝ), |φ - azimuth e.opposite| ≤ e.width →
        ∀ (n : ℕ) (lim : Limits) (exit : Certificates.PositionFrameSlabs.State)
          (blocks : List (List Step)), Chain lim e.start blocks n exit →
          FieldBoundsOn (DommaschkJacobian.euclideanFlow (azimuth e.opposite) sign)
            (DommaschkJacobian.velocityJacobian (azimuth e.opposite) sign) e.start 0
            blocks.flatten ballDomain → FollowsFrames e uC zC uA zA φ sign n exit blocks.flatten := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, entries⟩ := exists_nested_section_entry
  exact ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, fun e φ _ h _ _ _ _ hc hb =>
    followsFrames_of_bounds (entries e φ h) hc hb⟩

end PlasmaLean.Design.DommaschkMirrorLaunch
