/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorFramePath
public import PlasmaLean.Design.DommaschkPhysicalSecondStep

/-!
# A two-slab physical field-line trace from the Q-16 launch

The first two forward rows at zero phase are joined at the actual solution
value. The derivative theorem applies throughout the closed interval [0,1/32],
including the change of reference and moving frame at 1/64.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKamC KamNewton Set
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2

/-- First two recorded forward steps at the phase-zero radius 0.470. -/
def twoRows : List Step := [DommaschkPhysicalFirstStep.row, DommaschkPhysicalSecondStep.row]

/-- Terminal centre, frame and validated error radius at t=1/32. -/
abbrev twoExit := next DommaschkPhysicalSecondStep.row

private theorem two_checked :
    Chain pilotLimits (MirrorEndpoint.start .q0r470) [twoRows] 2 twoExit := by
  apply Chain.cons (m := twoExit) (n := 0)
  · change run pilotLimits DommaschkPhysicalFirstStep.seed
      [DommaschkPhysicalFirstStep.row, DommaschkPhysicalSecondStep.row] = _
    simp only [run, DommaschkPhysicalFirstStep.checked, DommaschkPhysicalSecondStep.checked,
      Bool.and_true]
  · exact .nil _

private theorem two_bounds :
    FieldBoundsOn (DommaschkJacobian.euclideanFlow 0 1) (DommaschkJacobian.velocityJacobian 0 1)
      (MirrorEndpoint.start .q0r470) 0 twoRows ballDomain := by
  refine ⟨DommaschkPhysicalFirstStep.ball_field_bounds, ?_, trivial⟩
  simpa only [zero_add] using DommaschkPhysicalSecondStep.field_bounds

/-- A single nested profile pair has an actual forward solution in both moving tubes, for
every birth within 2⁻¹⁹ radian of the common section. -/
theorem exists_nested_two_slabs :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2^19 → FollowsFrames .q0r470 uC zC uA zA φ 1 2 twoExit twoRows := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, paths⟩ := exists_nested_frame_paths
  refine ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, fun φ hp => ?_⟩
  exact paths .q0r470 φ 1 (by
    simpa [MirrorEndpoint.width, MirrorEndpoint.opposite, azimuth] using hp)
    2 pilotLimits twoExit [twoRows] two_checked two_bounds

/-- The reference for each clock is the one used in the corresponding stored polynomial. -/
def twoReference (t : ℝ) : Plane :=
  if t ≤ 1 / 64 then reference 0 DommaschkPhysicalFirstStep.row t
  else reference (1 / 64) DommaschkPhysicalSecondStep.row t

/-- Uniform Euclidean error across the join, for any path in the two physical tubes. -/
theorem two_tube_error {path : ℝ → Plane}
    (inside : ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 twoRows,
      ∀ t ∈ Icc slab.start slab.stop, path t ∈ slab.tube t) {t : ℝ} (ht : t ∈ Icc 0 (1 / 32)) :
    dist (path t) (twoReference t) ≤ 1232 / 10^9 := by
  by_cases h : t ≤ 1 / 64
  · simp only [twoReference, h, ↓reduceIte]
    have here := inside
      (physicalSlab DommaschkPhysicalFirstStep.seed DommaschkPhysicalFirstStep.row 0)
      (List.Mem.head _) t (by simpa [physicalSlab] using And.intro ht.1 h)
    refine here.2.trans ?_
    change (1481700234749866732 : ℝ) / 2^80 ≤ _
    norm_num
  · simp only [twoReference, h, ↓reduceIte]
    let slab := physicalSlab DommaschkPhysicalSecondStep.previous DommaschkPhysicalSecondStep.row
      (1 / 64)
    have here := inside slab (by simp [slab, twoRows, physicalSlabs])
      t (by change 1 / 64 ≤ t ∧ t ≤ 1 / 64 + 1 / 64
            exact ⟨(lt_of_not_ge h).le, by linarith [ht.2]⟩)
    refine here.2.trans ?_
    change (1488403201111526573 : ℝ) / 2^80 ≤ _
    norm_num

end PlasmaLean.Design.DommaschkMirrorLaunch
