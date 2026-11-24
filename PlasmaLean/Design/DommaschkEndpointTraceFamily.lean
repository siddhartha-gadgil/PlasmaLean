/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkEndpointSignedTrace
public import PlasmaLean.Design.DommaschkBackwardPairedPrefix

/-! # Endpoint-dependent trace lengths on one fixed pair of nested Q-16 tori -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkEndpointTraceFamily
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkBounceField
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkEndpointSignedTrace DommaschkBackwardPairedPrefix
open DommaschkJacobian (euclideanFlow velocityJacobian)

/-- A signed trajectory has its own duration, two exit ellipsoids and two ordered
rows of physical tubes. The numerical rows can vary with the endpoint. -/
structure Checkpoint where
  length : ℕ
  forwardExit : Certificates.PositionFrameSlabs.State
  backwardExit : Certificates.PositionFrameSlabs.State
  forwardRows : List Step
  backwardRows : List Step

def Checkpoint.Passage (c : Checkpoint) (e : MirrorEndpoint) (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  FromBirth e uC zC uA zA φ ((c.length : ℝ) / 64) (stateSet c.forwardExit)
    (stateSet c.backwardExit) (physicalSlabs e.start 0 c.forwardRows)
    (physicalSlabs e.start 0 c.backwardRows)

/-- The torus witnesses precede the choice of endpoint and angle. -/
def Common (c : MirrorEndpoint → Checkpoint) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    ∀ e φ, |φ - azimuth e.opposite| ≤ e.width → (c e).Passage e uC zC uA zA φ

theorem common_of_entry (c : MirrorEndpoint → Checkpoint)
    (each : ∀ e {uC zC uA zA : FA} {φ : ℝ},
      SectionEntry e uC zC uA zA φ → (c e).Passage e uC zC uA zA φ) : Common c := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, entries⟩ :=
    exists_nested_section_entry
  exact ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, fun e φ in_sector =>
    each e (entries e φ in_sector)⟩

/-- The pilot's checked scalar chain and physical field bounds give a physical chain
from any point in its section entry set. -/
theorem pilot_chain {sign : ℝ} {n : ℕ} {e : Certificates.PositionFrameSlabs.State}
    {rows : List Step} (d : Direction sign n e rows) :
    Fields.TrajectorySlabs.Chain (euclideanFlow 0 sign) 0 (stateSet (MirrorEndpoint.start .q0r470))
      ((n : ℝ) / 64) (stateSet e) (physicalSlabs (MirrorEndpoint.start .q0r470) 0 rows) := by
  have b : FieldBoundsOn (euclideanFlow 0 sign) (velocityJacobian 0 sign)
      (MirrorEndpoint.start .q0r470) 0 [rows].flatten ballDomain := by simpa using d.bounds
  simpa using d.checked.physical b

theorem pilot_from_entry {c : Checkpoint} {uC zC uA zA : FA} {φ : ℝ}
    (entry : SectionEntry .q0r470 uC zC uA zA φ)
    (f : Direction 1 c.length c.forwardExit c.forwardRows)
    (b : Direction (-1) c.length c.backwardExit c.backwardRows) :
    c.Passage .q0r470 uC zC uA zA φ :=
  DommaschkEndpointSignedTrace.from_entry entry (pilot_chain f) (pilot_chain b)

end PlasmaLean.Design.DommaschkEndpointTraceFamily
