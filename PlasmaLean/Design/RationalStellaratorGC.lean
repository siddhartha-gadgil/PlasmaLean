/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellarator
public import PlasmaLean.Theory.Kinetic.GuidingCentreLittlejohn
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The guiding-centre field of the rational stellarator (`gcField`)

The passing (`μ = 0`) guiding centres of the Littlejohn model move along the field lines of the
modified field `B̃ = B + ρ ∇×b`, `b = B/|B|` (`Theory/Kinetic/GuidingCentreLittlejohn`:
`modField`, `littlejohn_mu0_confined`), where `ρ = ρ_s = m v_∥/(q B₀ R₀)` in the model units of
`Design/RationalStellarator` (`R₀ = B₀ = 1`). For the rational stellarator `B = field (1/4)` this
file defines `gcField ρ = modField ρ (field (1/4))` and proves its algebraic form:

* `gcField_eq`: off the `z`-axis and where `B ≠ 0`,
  `B̃ = B + (ρ/2) Q^{−3/2} B × ∇Q` with `Q = |B|²` (`Qf`).

The proof differentiates `b = Q^{−1/2} B` (`bhat_eq`, `HasFDerivAt.rpow_const`), uses that the
Jacobian of the vacuum field is symmetric (`curl_fieldDeriv`, from `JB_symm`) and the curl of a
rank-one operator `curl (⟨g, ·⟩ v) = g × v` (`curl_innerSL_smulRight`). This is the form whose
flow-form components are the expressions of `Design/RationalStellaratorGCFlow`
(`W = q^{−1/2}`, `q = R⁸ Q`).

**Sanity.** `gcField_zero`: `ρ = 0` gives `field (1/4)`; `gradient_Qf`: `⟨∇Q, h⟩ = 2⟨B, DB h⟩`.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Kinetic.GCLittlejohn
  WithLp

/-- `Q = |B|²` for `B = field (1/4)`. -/
def Qf (y : Space) : ℝ := ‖field (1 / 4) y‖ ^ 2

/-- **The guiding-centre field** `B̃ = B + ρ ∇×b` of the rational stellarator (`B = field (1/4)`,
`ρ = ρ_s` in model units). -/
def gcField (ρ : ℝ) (x : Space) : Space := modField ρ (field (1 / 4)) x

/-- Sanity: `ρ = 0` gives the vacuum field. -/
theorem gcField_zero : gcField 0 = field (1 / 4) := by
  funext x; simp [gcField, modField]

/-- Rank-one operators are homogeneous in the functional. -/
theorem smulRight_smul' (c : ℝ) (l : Space →L[ℝ] ℝ) (v : Space) :
    (c • l).smulRight v = c • l.smulRight v :=
  ContinuousLinearMap.ext fun h => by simp [smul_smul]

/-- `curl` is additive. -/
theorem curl_add (L M : Space →L[ℝ] Space) : curl (L + M) = curl L + curl M :=
  map_add curlCLM L M

/-- `curl` is homogeneous. -/
theorem curl_smul (a : ℝ) (L : Space →L[ℝ] Space) : curl (a • L) = a • curl L :=
  map_smul curlCLM a L

/-- The curl of a rank-one operator: `curl (h ↦ ⟨g, h⟩ v) = g × v`. -/
theorem curl_innerSL_smulRight (g v : Space) :
    curl ((innerSL ℝ g).smulRight v) = cross g v := by
  obtain ⟨h0, h1, h2⟩ := curl_coords ((innerSL ℝ g).smulRight v)
  rw [← sub_eq_zero, space_eq_zero_iff]
  simp only [PiLp.sub_apply, h0, h1, h2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    PiLp.smul_apply, smul_eq_mul, cross, cross_apply, basis, EuclideanSpace.inner_single_right]
  simp

/-- The Jacobian of the vacuum field is curl free. -/
theorem curl_fieldDeriv {x : Space} (hx : x ∈ domain) : curl (fieldDeriv (1 / 4) x) = 0 := by
  have hs := JB_symm (1 / 4) (ne_of_gt hx)
  obtain ⟨h0, h1, h2⟩ := curl_coords (fieldDeriv (1 / 4) x)
  rw [space_eq_zero_iff]
  have e : ∀ i j : Fin 3, fieldDeriv (1 / 4) x (basis j) i = JB (1 / 4) x i j :=
    fun i j => fieldDeriv_entry x (1 / 4) i j
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, e, e, hs]; ring
  · rw [h1, e, e, hs]; ring
  · rw [h2, e, e, hs]; ring

/-- `‖v‖⁻¹ = (‖v‖²)^{−1/2}`. -/
theorem inv_norm_eq_rpow (v : Space) : ‖v‖⁻¹ = (‖v‖ ^ 2) ^ (-(1 / 2) : ℝ) := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg v)]

/-- `b = Q^{−1/2} B`. -/
theorem bhat_eq : bhat (field (1 / 4)) = fun y => Qf y ^ (-(1 / 2) : ℝ) • field (1 / 4) y := by
  funext y; rw [bhat, Qf, inv_norm_eq_rpow]

/-- The derivative of `Q`. -/
theorem hasFDerivAt_Qf {x : Space} (hx : x ∈ domain) :
    HasFDerivAt Qf (2 • (innerSL ℝ (field (1 / 4) x)).comp (fieldDeriv (1 / 4) x)) x :=
  (field_hasFDerivAt x (1 / 4) hx).norm_sq

/-- Sanity: `⟨∇Q, h⟩ = 2⟨B, DB h⟩`. -/
theorem gradient_Qf {x : Space} (hx : x ∈ domain) (h : Space) :
    ⟪gradient Qf x, h⟫ = 2 * ⟪field (1 / 4) x, fieldDeriv (1 / 4) x h⟫ := by
  rw [gradient, InnerProductSpace.toDual_symm_apply, (hasFDerivAt_Qf hx).fderiv]
  simp

/-- The derivative of `Q` is `⟨∇Q, ·⟩`. -/
theorem innerSL_gradient_Qf {x : Space} (hx : x ∈ domain) :
    innerSL ℝ (gradient Qf x) = 2 • (innerSL ℝ (field (1 / 4) x)).comp (fieldDeriv (1 / 4) x) := by
  ext h
  rw [innerSL_apply_apply, gradient_Qf hx]
  simp

/-- **The algebraic form of the guiding-centre field**: off the `z`-axis, where `B ≠ 0`,
`B̃ = B + (ρ/2) Q^{−3/2} B × ∇Q` with `Q = |B|²`. -/
theorem gcField_eq (ρ : ℝ) {x : Space} (hx : x ∈ domain) (hB : field (1 / 4) x ≠ 0) :
    gcField ρ x = field (1 / 4) x +
      (ρ / 2 * Qf x ^ (-(3 : ℝ) / 2)) • cross (field (1 / 4) x) (gradient Qf x) := by
  have hQ : Qf x ≠ 0 := by
    rw [Qf]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hB)
  have hQd := hasFDerivAt_Qf hx
  have hf := hQd.rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl hQ)
  have hb0 := hf.smul (field_hasFDerivAt x (1 / 4) hx)
  have hb : HasFDerivAt (bhat (field (1 / 4)))
      (Qf x ^ (-(1 / 2) : ℝ) • fieldDeriv (1 / 4) x + ContinuousLinearMap.smulRight
        (((-(1 / 2) : ℝ) * Qf x ^ ((-(1 / 2) : ℝ) - 1)) •
          (2 • (innerSL ℝ (field (1 / 4) x)).comp (fieldDeriv (1 / 4) x))) (field (1 / 4) x))
      x := by
    rw [bhat_eq]; exact hb0
  have hcurl : curlb (field (1 / 4)) x =
      ((-(1 / 2) : ℝ) * Qf x ^ ((-(1 / 2) : ℝ) - 1)) •
        cross (gradient Qf x) (field (1 / 4) x) := by
    rw [curlb, hb.fderiv, curl_add, curl_smul, curl_fieldDeriv hx, smul_zero, zero_add,
      ← innerSL_gradient_Qf hx, smulRight_smul', curl_smul, curl_innerSL_smulRight]
  have ha : cross (gradient Qf x) (field (1 / 4) x) = -cross (field (1 / 4) x) (gradient Qf x) := by
    simp only [cross]
    rw [← WithLp.toLp_neg, ← cross_anticomm]
  rw [gcField, modField, hcurl, ha, smul_neg, smul_neg, smul_smul, ← neg_smul]
  congr 2
  rw [show (-(1 / 2) : ℝ) - 1 = -(3 : ℝ) / 2 by norm_num]
  ring

end PlasmaLean.Design.RationalStellaratorGC
