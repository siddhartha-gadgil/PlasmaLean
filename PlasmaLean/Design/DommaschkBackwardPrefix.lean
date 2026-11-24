/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorTwoBackwardSlabs

/-! # Composable physical certificates for a backward prefix of the zero-section pilot

Each scalar transition and analytic field bound uses the true previous exit and
its own angular clock. The launch theorem then constructs one trajectory for the
whole prefix.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBackwardPrefix
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkKamC KamNewton
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2

/-- Add the first scalar row while retaining the previously checked tail. -/
theorem cons_run {s e : State} {r : Step} {tail : List Step}
    (h : test pilotLimits s r = true) (rest : run pilotLimits (next r) tail = (true, e)) :
    run pilotLimits s (r::tail) = (true, e) := by simp only [run,rest,h,Bool.and_true]

/-- A backward field certificate composes with the following one at the exact clock. -/
theorem cons_bounds (i : ℕ) {s : State} {r : Step} {tail : List Step}
    (h : FieldBounds s r ((i : ℝ) / 64) (DommaschkJacobian.euclideanFlow 0 (-1))
      (DommaschkJacobian.velocityJacobian 0 (-1)) ballDomain)
    (rest : FieldBoundsOn (DommaschkJacobian.euclideanFlow 0 (-1))
      (DommaschkJacobian.velocityJacobian 0 (-1)) (next r) ((i + 1 : ℕ) / 64) tail ballDomain) :
    FieldBoundsOn (DommaschkJacobian.euclideanFlow 0 (-1))
      (DommaschkJacobian.velocityJacobian 0 (-1))
      s ((i:ℝ)/64) (r::tail) ballDomain := by
  refine ⟨h,?_⟩
  have eq : (i:ℝ)/64 + 1/64 = ((i+1:ℕ):ℝ)/64 := by push_cast; ring
  simpa only [eq] using rest

/-- A qualifying physical Q-16 birth followed by the entire certified backward prefix. -/
def Passage (n : ℕ) (e : State) (rows : List Step) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    ∀ φ : ℝ, |φ| ≤ 1 / 2^19 → FollowsFrames .q0r470 uC zC uA zA φ (-1) n e rows

theorem passage {n : ℕ} {rows : List Step} {exit : State}
    (hc : Chain pilotLimits (MirrorEndpoint.start .q0r470) [rows] n exit)
    (hb : FieldBoundsOn (DommaschkJacobian.euclideanFlow 0 (-1))
      (DommaschkJacobian.velocityJacobian 0 (-1))
      (MirrorEndpoint.start .q0r470) 0 rows ballDomain) : Passage n exit rows := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,paths⟩ := exists_nested_frame_paths
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ hp => ?_⟩
  have full := paths .q0r470 φ (-1) (by
    simpa [MirrorEndpoint.width,MirrorEndpoint.opposite,azimuth] using hp)
    n pilotLimits exit [rows] hc (by simpa [MirrorEndpoint.opposite,azimuth] using hb)
  simpa using full

end PlasmaLean.Design.DommaschkBackwardPrefix
