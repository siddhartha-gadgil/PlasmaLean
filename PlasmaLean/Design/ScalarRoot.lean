/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.Contraction
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Exact nonlinear scalar validation fixture

Validate x²=2 on the entire closed ball centered at 3/2 with radius 1/2, via
T(x)=x+(2-x²)/3. The residual is 1/12, the Lipschitz constant is 1/3, and the
ball-invariance budget is 1/4 ≤ 1/2. This tests the existence pipeline, not a
plasma equilibrium. All coefficients are exact; there is no numerical solver.
-/
public section
noncomputable section
namespace PlasmaLean.Design

/-- A preconditioned fixed-point map for the scalar equation x²=2. -/
@[expose] def rootMap (x : ℝ) : ℝ := x + (2 - x ^ 2) / 3

/-- Exact derivative of the validation map. -/
theorem rootMap_derivative (x : ℝ) : HasDerivAt rootMap (1 - 2 * x / 3) x := by
  convert (hasDerivAt_id x).add
    (((hasDerivAt_const x 2).sub ((hasDerivAt_id x).pow 2)).div_const 3) using 1
  · funext y
    dsimp [rootMap]
  · dsimp
    ring

/-- A bound throughout the ball, not a derivative sampled at the center. -/
theorem rootMap_lipschitz :
    LipschitzOnWith (1 / 3 : NNReal) rootMap (Metric.closedBall (3 / 2 : ℝ) (1 / 2)) := by
  apply (convex_closedBall (3 / 2 : ℝ) (1 / 2)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (rootMap_derivative x).hasDerivWithinAt)
  intro x hx
  have hx' : |x - 3 / 2| ≤ 1 / 2 := by simpa [Real.dist_eq] using hx
  have hab := abs_le.mp hx'
  change ‖1 - 2 * x / 3‖ ≤ ((1 / 3 : NNReal) : ℝ)
  simp only [Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

/-- The contraction pipeline proves existence and uniqueness of the positive root
inside the certified ball, without appealing to a pre-existing square-root value. -/
theorem validated_scalar_root :
    ∃ x ∈ Metric.closedBall (3 / 2 : ℝ) (1 / 2), x ^ 2 = 2 ∧
      ∀ y ∈ Metric.closedBall (3 / 2 : ℝ) (1 / 2), y ^ 2 = 2 → y = x := by
  obtain ⟨x, hx, hfix, unique⟩ := Certificates.local_fixedPoint rootMap (3 / 2 : ℝ)
    (r := 1 / 2) (Y := 1 / 12) (K := 1 / 3) (by norm_num) (by norm_num)
    (by norm_num [rootMap, Real.dist_eq]) rootMap_lipschitz (by norm_num)
  have hroot : x ^ 2 = 2 := by dsimp [rootMap] at hfix; linarith
  refine ⟨x, hx, hroot, ?_⟩
  intro y hy hysq
  apply unique y hy
  simp [rootMap, hysq]

end PlasmaLean.Design
