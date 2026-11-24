/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorFramePath
public import PlasmaLean.Design.DommaschkPhysicalBackwardSecondStep

/-! # Two consecutive backward slabs from the physical Q-16 birth

The second row inherits the true exit of the first. One solution satisfies the
signed field equation and the two recorded physical tubes across their join.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKamC KamNewton Set
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2

/-- Rows zero and one of the backward archive from the zero-section pilot. -/
def twoBackwardRows : List Step :=
  [DommaschkJacobianBackward000.row, DommaschkPhysicalBackwardSecondStep.row]

/-- Endpoint ellipsoid at elapsed angle 1/32. -/
abbrev twoBackwardExit := next DommaschkPhysicalBackwardSecondStep.row

theorem two_backward_checked :
    Chain pilotLimits (MirrorEndpoint.start .q0r470) [twoBackwardRows] 2 twoBackwardExit := by
  apply Chain.cons (m := twoBackwardExit) (n := 0)
  · change run pilotLimits DommaschkJacobianBackward000.seed
      [DommaschkJacobianBackward000.row, DommaschkPhysicalBackwardSecondStep.row] = _
    simp only [run, DommaschkPhysicalBackwardFirstStep.checked,
      DommaschkPhysicalBackwardSecondStep.checked, Bool.and_true]
  · exact .nil _

theorem two_backward_bounds :
    FieldBoundsOn (DommaschkJacobian.euclideanFlow 0 (-1))
      (DommaschkJacobian.velocityJacobian 0 (-1))
      (MirrorEndpoint.start .q0r470) 0 twoBackwardRows ballDomain := by
  refine ⟨DommaschkPhysicalBackwardFirstStep.field_bounds, ?_, trivial⟩
  simpa only [zero_add] using DommaschkPhysicalBackwardSecondStep.field_bounds

/-- Each qualifying birth on the same pair of nested Q-16 tori has a genuine
two-slab backward passage, including its physical launch into the section. -/
theorem exists_nested_two_backward_slabs :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2^19 →
        FollowsFrames .q0r470 uC zC uA zA φ (-1) 2 twoBackwardExit twoBackwardRows := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,paths⟩ := exists_nested_frame_paths
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ hp => ?_⟩
  exact paths .q0r470 φ (-1) (by
    simpa [MirrorEndpoint.width,MirrorEndpoint.opposite,azimuth] using hp)
    2 pilotLimits twoBackwardExit [twoBackwardRows] two_backward_checked two_backward_bounds

/-- Actual recorded comparison curve on each side of the 1/64 join. -/
def twoBackwardReference (t : ℝ) : Plane :=
  if t ≤ 1/64 then reference 0 DommaschkJacobianBackward000.row t
  else reference (1/64) DommaschkPhysicalBackwardSecondStep.row t

/-- Uniform physical position error across both adjoining backward slabs. -/
theorem two_backward_tube_error {path : ℝ → Plane}
    (inside : ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 twoBackwardRows,
      ∀ t ∈ Icc slab.start slab.stop, path t ∈ slab.tube t) {t : ℝ} (ht : t ∈ Icc 0 (1 / 32)) :
    dist (path t) (twoBackwardReference t) ≤ 1232 / 10^9 := by
  by_cases h : t ≤ 1/64
  · simp only [twoBackwardReference,h,↓reduceIte]
    have here := inside
      (physicalSlab DommaschkJacobianBackward000.seed DommaschkJacobianBackward000.row 0)
      (List.Mem.head _) t (by simpa [physicalSlab] using And.intro ht.1 h)
    refine here.2.trans ?_
    change (1481700234749866733:ℝ)/2^80 ≤ _
    norm_num
  · simp only [twoBackwardReference,h,↓reduceIte]
    let slab := physicalSlab DommaschkPhysicalBackwardSecondStep.previous
      DommaschkPhysicalBackwardSecondStep.row (1/64)
    have here := inside slab (by simp [slab,twoBackwardRows,physicalSlabs]) t
      (by change 1/64 ≤ t ∧ t ≤ 1/64+1/64
          exact ⟨(lt_of_not_ge h).le, by linarith [ht.2]⟩)
    refine here.2.trans ?_
    change (1488403201111526574:ℝ)/2^80 ≤ _
    norm_num

end PlasmaLean.Design.DommaschkMirrorLaunch
