/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeActionGeometry
public import PlasmaLean.Design.DommaschkJacobianReflection

/-! # Reflection of the physical quantities used by the native action packet -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkNativeActionReflection
open Certificates.PositionFrameSlabs DommaschkKam DommaschkBounceField DommaschkJacobianReflection
open DommaschkMirrorTubeCrossing DommaschkSectionReflection
set_option maxRecDepth 8192

theorem denominator (φ : ℝ) (x : Plane) :
    atPoint dD (x 0) (-φ) (x 1) = atPoint dD ((flip x) 0) φ ((flip x) 1) := by
  have even : parity dD 0 = true := by kernel_fact
  simpa only [neg_neg, pow_zero, one_mul, flip_zero, flip_one] using
    atPoint_reflect even (x 0) φ (-(x 1))

theorem norm {x : Plane} (hr : 0 < x 0) (φ : ℝ) :
    strength (-φ) x = strength φ (flip x) := by
  simpa only [strength, neg_neg, flip_zero, flip_one] using strength_reflected hr φ (-(x 1))

end PlasmaLean.Design.DommaschkNativeActionReflection
