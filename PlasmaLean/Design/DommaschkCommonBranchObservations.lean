/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCommonPilotObservables
public import PlasmaLean.Design.DommaschkPhaseZeroRegularBirth

/-! # Attaching observations to one embedded pair and to the original physical birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCommonBranchObservations
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointTraceFamily
open DommaschkSignedObservable DommaschkBirthVariation DommaschkPhaseZeroRegularBirth
open DommaschkLowerActionPath DommaschkSignedTraceDomain Set
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- All eight sector passages, the pilot's launch tangent and its signed physical observables,
on four specified radial profile functions. -/
structure OnPair (c : MirrorEndpoint → Checkpoint) (P : ℝ → (ℝ → Plane) → Prop)
    (uC zC uA zA : FA) : Prop where
  tangent : Pilot uC zC uA zA
  passage : ∀ e φ, |φ - azimuth e.opposite| ≤ e.width → (c e).Passage e uC zC uA zA φ
  pilot : ∀ φ, |φ| ≤ 1 / 2 ^ 19 → ∃ x y,
    y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) ∧
    Path (c .q0r470).length (c .q0r470).forwardExit (c .q0r470).backwardExit
      (c .q0r470).forwardRows (c .q0r470).backwardRows x y ∧ P φ y

/-- The profile functions and both embedded tori precede every additional endpoint observation. -/
def ExistsOnPair (c : MirrorEndpoint → Checkpoint) (P : ℝ → (ℝ → Plane) → Prop)
    (Q : FA → FA → FA → FA → Prop) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    OnPair c P uC zC uA zA ∧ Q uC zC uA zA

theorem of_pair {c P Q} (family : DommaschkCommonPilotObservables.Common c P)
    (attach : ∀ {uC zC uA zA}, OnPair c P uC zC uA zA → Q uC zC uA zA) :
    ExistsOnPair c P Q := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,variation,each,pilot⟩ := family
  have pair : OnPair c P uC zC uA zA := ⟨variation,each,pilot⟩
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,pair,attach pair⟩

/-- Extend an observation on its original profiles while retaining the pilot path claims. -/
theorem extend {c P Q} {S : FA → FA → FA → FA → Prop} (family : ExistsOnPair c P Q)
    (attach : ∀ {uC zC uA zA}, OnPair c P uC zC uA zA → Q uC zC uA zA → S uC zC uA zA) :
    ExistsOnPair c P (fun uC zC uA zA => Q uC zC uA zA ∧ S uC zC uA zA) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,pair,q⟩ := family
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,pair,q,attach pair q⟩

/-- A phase-zero signed path retains its true birth position when a physical observation is
valid for every enclosed trajectory. The whole signed path and the observation use the same y. -/
theorem fixed_birth_observation {e : MirrorEndpoint} (phase : e.opposite = false)
    {c : Checkpoint} {uC zC uA zA : FA} {φ : ℝ} {Q : (ℝ → Plane) → Prop}
    (passage : c.Passage e uC zC uA zA φ) (room : |φ| ≤ c.length / 64)
    (positive : 0 < c.length) (lf : c.forwardRows.length = c.length)
    (lb : c.backwardRows.length = c.length) (rf : c.forwardRows.all packed = true)
    (rb : c.backwardRows.all packed = true)
    (observe : ∀ y, Signed e.start c.forwardRows c.backwardRows (c.length / 64) y → Q y) :
    ∃ y, y φ = coordinates.symm (birth uC zC uA zA e.radius φ) ∧
      Signed e.start c.forwardRows c.backwardRows (c.length / 64) y ∧ Q y := by
  apply at_original_birth phase passage room
  intro y path
  exact ⟨regions path.forward path.backward positive lf lb rf rb,path,observe y path⟩

end PlasmaLean.Design.DommaschkCommonBranchObservations
