/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianReflection
public import PlasmaLean.Design.DommaschkSignedTraceDomain

/-!
# The phase-zero reflection of the planar field-line equation

The reflection `flip` = diag(1, −1) of the poloidal plane is a linear isometric involution. At
phase zero it conjugates the field of the planar field-line equation to its time reversal about
the time zero, which is the symmetry hypothesis of `FlowLabel.HalfTube`.

* `flipIso`: the reflection as a linear isometric equivalence, with `flipIso_involutive`.
* `flow_symm`, `flow_symm_neg`: at positive radius,
  `euclideanFlow 0 1 (-t) (flipIso x) = -flipIso (euclideanFlow 0 1 t x)`.
* `region_flip`: the cylindrical envelope `Region` is invariant under the reflection.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTubeSymmetry

open Certificates.PositionFrameSlabs DommaschkJacobian DommaschkJacobianReflection
open DommaschkSectionReflection DommaschkSignedTraceDomain

/-- The reflection diag(1, −1) of the plane as a linear isometric equivalence. -/
def flipIso : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv := LinearEquiv.ofInvolutive flip.toLinearMap flip_twice
  norm_map' := flip_norm

@[simp] theorem flipIso_apply (x : Plane) : flipIso x = flip x := rfl

/-- The reflection is an involution. -/
theorem flipIso_involutive : ∀ x, flipIso (flipIso x) = x := flip_twice

/-- In coordinates the reflection of the plane is the midplane reflection. -/
theorem coordinates_flip (x : Plane) :
    DommaschkJacobian.coordinates (flip x) = reflect (DommaschkJacobian.coordinates x) := by
  funext i
  fin_cases i <;> simp [reflect]

/-- Reversing the time of the forward field at phase zero gives minus the backward field. -/
theorem physicalFlow_neg (t : ℝ) (q : DommaschkBounceField.State) :
    DommaschkBounceField.physicalFlow 0 1 (-t) q =
      -DommaschkBounceField.physicalFlow 0 (-1) t q := by
  funext i
  fin_cases i <;> simp [DommaschkBounceField.physicalFlow]

/-- **Time-reversal symmetry at phase zero**, with the reversed time written `-t`. -/
theorem flow_symm_neg (t : ℝ) (x : Plane) (hR : 0 < x 0) :
    euclideanFlow 0 1 (-t) (flipIso x) = -flipIso (euclideanFlow 0 1 t x) := by
  have key := flow_reflect t (DommaschkJacobian.coordinates x) hR
  rw [flipIso_apply, flipIso_apply, euclideanFlow, coordinates_flip, physicalFlow_neg, key,
    map_neg, neg_inj, ContinuousLinearEquiv.symm_apply_eq, coordinates_flip, euclideanFlow,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **Time-reversal symmetry at phase zero**, in the form of `FlowLabel.HalfTube.symm` with the
section time zero. -/
theorem flow_symm (t : ℝ) (x : Plane) (hR : 0 < x 0) :
    euclideanFlow 0 1 (2 * 0 - t) (flipIso x) = -flipIso (euclideanFlow 0 1 t x) := by
  rw [show 2 * 0 - t = -t by ring]
  exact flow_symm_neg t x hR

/-- The cylindrical envelope is invariant under the reflection. -/
theorem region_flip {x : Plane} (h : Region x) : Region (flipIso x) := by
  simpa [Region] using h

/-- Sanity: the reflection fixes the points of the midplane. -/
theorem flipIso_midplane {x : Plane} (h : x 1 = 0) : flipIso x = x := by
  ext i
  fin_cases i <;> simp [h]

end PlasmaLean.Design.DommaschkTubeSymmetry
