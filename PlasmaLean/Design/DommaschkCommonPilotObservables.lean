/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPilotBirthVariation
public import PlasmaLean.Design.DommaschkSignedBirthApproach

/-! # Observables on the pilot trajectory of an eight-sector embedded torus family -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCommonPilotObservables
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointTraceFamily
open DommaschkSignedObservable DommaschkSignedBirthApproach DommaschkBirthVariation
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- Keep the full trajectory and every sector while strengthening the pilot statement.
The same witnesses are chosen before the sector and the physical birth angle. -/
def Common (c : MirrorEndpoint → Checkpoint) (P : ℝ → (ℝ → Plane) → Prop) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    Pilot uC zC uA zA ∧
    (∀ e φ, |φ - azimuth e.opposite| ≤ e.width → (c e).Passage e uC zC uA zA φ) ∧
    ∀ φ, |φ| ≤ 1 / 2 ^ 19 → ∃ x y,
      y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) ∧
      Path (c .q0r470).length (c .q0r470).forwardExit (c .q0r470).backwardExit
        (c .q0r470).forwardRows (c .q0r470).backwardRows x y ∧ P φ y

/-- A conclusion uniform over every enclosed pilot trajectory applies on the very surfaces
selected by the proved birth-tangent and common-sector theorem. -/
theorem of_paths {c : MirrorEndpoint → Checkpoint} {P : ℝ → (ℝ → Plane) → Prop}
    (family : CommonPilot c) (hn : 0 < (c .q0r470).length)
    (hf : (c .q0r470).forwardRows = DommaschkPositionFramesFwd.blocks.flatten.take
      (c .q0r470).length)
    (hb : (c .q0r470).backwardRows = DommaschkPositionFramesBack.blocks.flatten.take
      (c .q0r470).length)
    (lf : (c .q0r470).forwardRows.length = (c .q0r470).length)
    (lb : (c .q0r470).backwardRows.length = (c .q0r470).length)
    (prove : ∀ {φ x y}, |φ| ≤ 1 / 2 ^ 19 →
      Path (c .q0r470).length (c .q0r470).forwardExit (c .q0r470).backwardExit
        (c .q0r470).forwardRows (c .q0r470).backwardRows x y → P φ y) : Common c P := by
  obtain ⟨uC,zC,uA,zA,R,z,C,A,ic,ia,nested,ec,ea,slope,_,each⟩ := family
  refine ⟨uC,zC,uA,zA,R,z,C,A,ic,ia,nested,ec,ea,slope,each,fun φ small => ?_⟩
  obtain ⟨sign, approach, unit, clock, start, ode, y, ys, ye, yf, dy, ft, bt⟩ :=
    each .q0r470 φ (by simpa [MirrorEndpoint.opposite, MirrorEndpoint.width, azimuth] using small)
  simp only [MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ↓reduceIte, sub_zero] at *
  have path : Path (c .q0r470).length (c .q0r470).forwardExit (c .q0r470).backwardExit
      (c .q0r470).forwardRows (c .q0r470).backwardRows (coordinates.symm (approach |φ|)) y :=
    ⟨ys, by simpa only [neg_div] using ye, yf, by simpa only [neg_div] using dy, ft, bt⟩
  have birth_eq : approach 0 = birth uC zC uA zA (47 / 100) φ := by
    convert start using 1
    norm_num [MirrorEndpoint.radius]
  exact ⟨_, y, birth_position path unit clock small birth_eq ode hn hf hb lf lb,
    path, prove small path⟩

end PlasmaLean.Design.DommaschkCommonPilotObservables
