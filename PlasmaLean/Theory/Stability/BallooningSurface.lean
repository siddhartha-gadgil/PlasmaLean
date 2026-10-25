/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.BallooningReduction
public import PlasmaLean.Theory.Fields.FieldDerivative
public import PlasmaLean.Theory.Fields.ClebschDivergence

/-!
# Ballooning on a flux surface: the transported eikonal and surface Riccati certificates

This module specializes the SUPPLIED ballooning reduction of `BallooningReduction` to a
general three-dimensional equilibrium with a flux function, without any symmetry and without
straight-field-line coordinates. Throughout, `B` is the field, `M = DB` its derivative,
`g = ∇ψ` the gradient of a flux function (`B · g = 0`), and `t ↦ X(t)` a field line,
`X' = B(X)` (line element `ℓ = 1`).

## The covering-space eikonal

An eikonal `S` with `B · ∇S = 0` has, along a field line, a gradient `k(t) = ∇S(X(t))` with
`k · B = 0` that is *transported*: `k' = −Mᵀ k` (differentiate `B · ∇S = 0`). Here:

* `eikBase B g = B × g/|g|²` satisfies `g × eikBase = B` (`cross_eikBase`, a local Clebsch
  representation `B = ∇ψ × k₀`) and `eikBase ⊥ B, g`;
* `shearRate M B g = (⟪k₀, M g⟫ + ⟪M k₀, g⟫)/|g|²` (the *local shear*; only first
  derivatives of `B` enter);
* `hasDerivAt_eik`: if `∇ψ` is transported along the line (`(g ∘ X)' = −Mᵀ g`; for a flux
  function this follows from the symmetry of the Hessian, `transport_of_hessian`) and
  `∇ · B = 0`, then for every `σ` with `σ' = shearRate` and every shift `c` the vector
  `k(t) = k₀(X) − (σ(t) − c) ∇ψ(X)` is transported, `k' = −Mᵀ k`. The shift `c` is the
  eikonal family (`θ_k`). The algebraic core is `transport_identity`
  (`L_B k₀ = (shearRate) ∇ψ`, which uses `tr M = 0` and `B · g = 0`).
* `eik_complete`: conversely EVERY transported `k` with `k · B = 0` along the line is of this
  form up to a constant factor `m` (`k = m k₀ − s ∇ψ`, `m' = 0`, `s' = m · shearRate`); since
  `P` and `Q` are quadratic in `k`, the family `k₀ − (σ − c)∇ψ` exhausts all eikonals (the
  case `m = 0`, `k ∥ ∇ψ`, has no drive).

## Ballooning coefficients

For `k = k₀ − s g` and `μ₀∇p = μ g` (`ballooningP_eik`, `ballooningQ_eik`):

  `P = 1/|g|² + s² |g|²/|B|²`,
  `Q = −2μ ⟪g, κ⟫/|g|² + s · (−2μ ⟪B × g, κ⟫/|B|²)`

(normal and geodesic curvature drives).

## Surface Riccati certificates

`energy_nonneg_of_surfaceCert` / `eikLine_stable_of_surfaceCert` (for the line data
`eikLine`): if `Φ(x, s)` is a `C¹` function with
`DΦ(x, s)(B(x), shearRate(x)) + Φ²/P ≤ Q` at every point of the line and every `s`, then
the line is ballooning stable for EVERY shift `c` (all `θ_k`), via
`BallooningReduction.riccati2D_energy_nonneg` with `F(t, s) = Φ(X(t), s)`. For a field line
filling an irrational flux surface the hypothesis is a pointwise inequality on
`surface × ℝ`; it does not refer to the (non-periodic) line.

Sanity: `eikLine_noDrive_stable` (degenerate case `μ = 0`: always stable).
-/

public section
noncomputable section

namespace PlasmaLean.Stability.BallooningSurface

open Set PlasmaLean.Fields PlasmaLean.Stability PlasmaLean.Stability.BallooningInfinite
open PlasmaLean.Stability.BallooningReduction WithLp
open scoped RealInnerProductSpace

/-! ## Coordinates -/

/-- Transpose of a linear map applied to a vector: `(Mᵀ v)ᵢ = ⟪v, M eᵢ⟫`. -/
@[expose] def tApply (M : Space →L[ℝ] Space) (v : Space) : Space :=
  toLp 2 ![⟪v, M (basis 0)⟫, ⟪v, M (basis 1)⟫, ⟪v, M (basis 2)⟫]

/-- Inner product in coordinates. -/
theorem inner_coords (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]; ring

/-- Squared norm in coordinates. -/
theorem norm_sq_coords (u : Space) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]; ring

/-- Expansion of a vector in the coordinate basis. -/
theorem eq_sum_basis (v : Space) : v = v 0 • basis 0 + v 1 • basis 1 + v 2 • basis 2 := by
  apply space_ext <;> simp [basis]

/-- A linear map in coordinates. -/
theorem clm_coords (M : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    M v i = v 0 * M (basis 0) i + v 1 * M (basis 1) i + v 2 * M (basis 2) i := by
  conv_lhs => rw [eq_sum_basis v]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- The transpose in coordinates. -/
theorem tApply_coords (M : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    tApply M v i = v 0 * M (basis i) 0 + v 1 * M (basis i) 1 + v 2 * M (basis i) 2 := by
  fin_cases i <;> simp [tApply, inner_coords]

/-- `⟪Mᵀ v, w⟫ = ⟪v, M w⟫`. -/
theorem inner_tApply (M : Space →L[ℝ] Space) (v w : Space) : ⟪tApply M v, w⟫ = ⟪v, M w⟫ := by
  rw [inner_coords, inner_coords v, tApply_coords, tApply_coords, tApply_coords,
    clm_coords M w 0, clm_coords M w 1, clm_coords M w 2]
  ring

/-- Coordinates of the cross product. -/
theorem cross_coords (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
      cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cross, cross_apply]

/-! ## The base eikonal and the local shear -/

/-- The base eikonal `k₀ = B × g/|g|²`. -/
@[expose] def eikBase (B g : Space) : Space := (‖g‖ ^ 2)⁻¹ • cross B g

/-- The covering-space eikonal `k = k₀ − s g`. -/
@[expose] def eik (B g : Space) (s : ℝ) : Space := eikBase B g - s • g

/-- The local shear `(⟪k₀, M g⟫ + ⟪M k₀, g⟫)/|g|²`, the rate of the secular variable. -/
@[expose] def shearRate (M : Space →L[ℝ] Space) (B g : Space) : ℝ :=
  (⟪eikBase B g, M g⟫ + ⟪M (eikBase B g), g⟫) / ‖g‖ ^ 2

/-- `k₀ ⊥ B`. -/
theorem inner_eikBase_B (B g : Space) : ⟪eikBase B g, B⟫ = 0 := by
  rw [eikBase, real_inner_smul_left, inner_cross_self_left B g, mul_zero]

/-- `k₀ ⊥ g`. -/
theorem inner_eikBase_g (B g : Space) : ⟪eikBase B g, g⟫ = 0 := by
  rw [eikBase, real_inner_smul_left, inner_cross_self_right B g, mul_zero]

/-- `k ⊥ B` (if `B ⊥ g`). -/
theorem inner_eik_B {B g : Space} (hBg : ⟪B, g⟫ = 0) (s : ℝ) : ⟪eik B g s, B⟫ = 0 := by
  rw [eik, inner_sub_left, inner_eikBase_B, real_inner_smul_left, real_inner_comm, hBg]; ring

/-- **Local Clebsch representation**: `g × k₀ = B` when `B ⊥ g`, `g ≠ 0`. -/
theorem cross_eikBase {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) :
    cross g (eikBase B g) = B := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  rw [norm_sq_coords] at hn
  rw [inner_coords] at hBg
  obtain ⟨c0, c1, c2⟩ := cross_coords g (eikBase B g)
  obtain ⟨d0, d1, d2⟩ := cross_coords B g
  apply space_ext
  · rw [c0]; simp only [eikBase, PiLp.smul_apply, smul_eq_mul, d1, d2, norm_sq_coords]
    field_simp; linear_combination (-(g 0)) * hBg
  · rw [c1]; simp only [eikBase, PiLp.smul_apply, smul_eq_mul, d0, d2, norm_sq_coords]
    field_simp; linear_combination (-(g 1)) * hBg
  · rw [c2]; simp only [eikBase, PiLp.smul_apply, smul_eq_mul, d0, d1, norm_sq_coords]
    field_simp; linear_combination (-(g 2)) * hBg

/-- `g × k = B` for every `s`: every member of the family is a Clebsch partner of `∇ψ`. -/
theorem cross_eik {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) (s : ℝ) :
    cross g (eik B g s) = B := by
  rw [eik, cross_sub_smul, cross_eikBase hBg hg]
  have : cross g g = 0 := by apply space_ext <;> simp [cross]
  rw [this, smul_zero, sub_zero]

/-- `|k₀|² = |B|²/|g|²` when `B ⊥ g`. -/
theorem norm_eikBase_sq {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) :
    ‖eikBase B g‖ ^ 2 = ‖B‖ ^ 2 / ‖g‖ ^ 2 := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  have hc : ‖cross B g‖ ^ 2 = ‖B‖ ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_sq_coords, norm_sq_coords, norm_sq_coords]
    obtain ⟨d0, d1, d2⟩ := cross_coords B g
    rw [d0, d1, d2]; rw [inner_coords] at hBg
    linear_combination (-(B 0 * g 0 + B 1 * g 1 + B 2 * g 2)) * hBg
  rw [eikBase, norm_smul, mul_pow, hc, Real.norm_eq_abs, sq_abs]
  field_simp

/-- `|k|² = |B|²/|g|² + s² |g|²`. -/
theorem norm_eik_sq {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) (s : ℝ) :
    ‖eik B g s‖ ^ 2 = ‖B‖ ^ 2 / ‖g‖ ^ 2 + s ^ 2 * ‖g‖ ^ 2 := by
  rw [eik, norm_sub_sq_real, norm_eikBase_sq hBg hg, real_inner_smul_right, inner_eikBase_g,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- `k ≠ 0` (if `B ≠ 0`). -/
theorem eik_ne {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    eik B g s ≠ 0 := by
  intro h
  have := cross_eik hBg hg s
  rw [h] at this
  apply hB; rw [← this]; apply space_ext <;> simp [cross, cross_apply]

/-! ## The ballooning coefficients on the eikonal family -/

/-- **Bending coefficient** on the family (`ℓ = 1`): `P = 1/|g|² + s² |g|²/|B|²`. -/
theorem ballooningP_eik {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    ballooningP 1 B (eik B g s) = 1 / ‖g‖ ^ 2 + s ^ 2 * (‖g‖ ^ 2 / ‖B‖ ^ 2) := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  have hb : ‖B‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hB)
  rw [ballooningP, norm_eik_sq hBg hg]
  field_simp

/-- `⟪B × k₀, g⟫ = −|B|²` (when `B ⊥ g`). -/
theorem inner_cross_eikBase_g {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) :
    ⟪cross B (eikBase B g), g⟫ = -‖B‖ ^ 2 := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  rw [norm_sq_coords] at hn ⊢
  rw [inner_coords] at hBg ⊢
  obtain ⟨c0, c1, c2⟩ := cross_coords B (eikBase B g)
  obtain ⟨d0, d1, d2⟩ := cross_coords B g
  rw [c0, c1, c2]
  simp only [eikBase, PiLp.smul_apply, smul_eq_mul, d0, d1, d2, norm_sq_coords]
  field_simp
  linear_combination (B 0 * g 0 + B 1 * g 1 + B 2 * g 2) * hBg

/-- `⟪B × k₀, κ⟫ = −|B|² ⟪g, κ⟫/|g|²` (when `B ⊥ g`). -/
theorem inner_cross_eikBase_kappa {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) (κ : Space) :
    ⟪cross B (eikBase B g), κ⟫ = -(‖B‖ ^ 2 * ⟪g, κ⟫) / ‖g‖ ^ 2 := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  rw [norm_sq_coords] at hn ⊢
  rw [inner_coords] at hBg ⊢
  rw [inner_coords, norm_sq_coords]
  obtain ⟨c0, c1, c2⟩ := cross_coords B (eikBase B g)
  obtain ⟨d0, d1, d2⟩ := cross_coords B g
  rw [c0, c1, c2]
  simp only [eikBase, PiLp.smul_apply, smul_eq_mul, d0, d1, d2, norm_sq_coords]
  field_simp
  linear_combination (B 0 * κ 0 + B 1 * κ 1 + B 2 * κ 2) * hBg

/-- **Drive** on the family (`ℓ = 1`, `μ₀∇p = μ g`):
`Q = −2μ ⟪g, κ⟫/|g|² + s (−2μ ⟪B × g, κ⟫/|B|²)` (normal and geodesic curvature). -/
theorem ballooningQ_eik {B g : Space} (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) (hB : B ≠ 0)
    (μ s : ℝ) (κ : Space) :
    ballooningQ 1 B (eik B g s) (μ • g) κ =
      -(2 * μ * ⟪g, κ⟫) / ‖g‖ ^ 2 + s * (-(2 * μ * ⟪cross B g, κ⟫) / ‖B‖ ^ 2) := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  have hb : ‖B‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hB)
  have h1 : ⟪cross B (eik B g s), μ • g⟫ = -(μ * ‖B‖ ^ 2) := by
    rw [eik, cross_sub_smul, real_inner_smul_right, inner_sub_left, inner_cross_eikBase_g hBg hg,
      real_inner_smul_left, inner_cross_self_right]
    ring
  have h2 : ⟪cross B (eik B g s), κ⟫ =
      -(‖B‖ ^ 2 * ⟪g, κ⟫) / ‖g‖ ^ 2 - s * ⟪cross B g, κ⟫ := by
    rw [eik, cross_sub_smul, inner_sub_left, inner_cross_eikBase_kappa hBg hg,
      real_inner_smul_left]
  rw [ballooningQ, h1, h2]
  field_simp
  ring

/-! ## Transport of the eikonal -/

/-- **Algebraic core of the transport**: with `g' = −Mᵀ g` and `tr M = 0`, `B ⊥ g`, the
Lie derivative `k₀' + Mᵀ k₀` of the base eikonal along `B` is `shearRate · g`. Here
`k₀' = −(2⟪g, g'⟫/|g|⁴) B × g + (M B × g + B × g')/|g|²`. -/
theorem transport_identity (M : Space →L[ℝ] Space) (B g : Space) (htr : divergence M = 0)
    (hBg : ⟪B, g⟫ = 0) (hg : g ≠ 0) :
    (-(2 * ⟪g, -tApply M g⟫) / (‖g‖ ^ 2) ^ 2) • cross B g +
        (‖g‖ ^ 2)⁻¹ • (cross (M B) g + cross B (-tApply M g)) +
        tApply M ((‖g‖ ^ 2)⁻¹ • cross B g) = shearRate M B g • g := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  rw [norm_sq_coords] at hn
  rw [divergence_apply] at htr
  rw [inner_coords] at hBg
  have e : ∀ v : Space, ∀ i, M v i = v 0 * M (basis 0) i + v 1 * M (basis 1) i +
      v 2 * M (basis 2) i := clm_coords M
  apply space_ext
  · simp only [shearRate, eikBase, inner_coords, norm_sq_coords, PiLp.add_apply,
      PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, tApply_coords, map_smul, e B, e g,
      e (cross B g), (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
    generalize M (basis 0) 0 = m00 at *
    generalize M (basis 0) 1 = m10 at *
    generalize M (basis 0) 2 = m20 at *
    generalize M (basis 1) 0 = m01 at *
    generalize M (basis 1) 1 = m11 at *
    generalize M (basis 1) 2 = m21 at *
    generalize M (basis 2) 0 = m02 at *
    generalize M (basis 2) 1 = m12 at *
    generalize M (basis 2) 2 = m22 at *
    field_simp
    linear_combination (-(-(B 1)*(g 2) + (B 2)*(g 1))*((g 0)^2 + (g 1)^2 + (g 2)^2)) * htr + (-(g
      0)*(g 1)*m02 - (g 0)*(g 1)*m20 + (g 0)*(g 2)*m01 + (g 0)*(g 2)*m10 - (g 1)^2*m12 - (g
      1)^2*m21 + 2*(g 1)*(g 2)*m11 - 2*(g 1)*(g 2)*m22 + (g 2)^2*m12 + (g 2)^2*m21) * hBg
  · simp only [shearRate, eikBase, inner_coords, norm_sq_coords, PiLp.add_apply,
      PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, tApply_coords, map_smul, e B, e g,
      e (cross B g), (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
    generalize M (basis 0) 0 = m00 at *
    generalize M (basis 0) 1 = m10 at *
    generalize M (basis 0) 2 = m20 at *
    generalize M (basis 1) 0 = m01 at *
    generalize M (basis 1) 1 = m11 at *
    generalize M (basis 1) 2 = m21 at *
    generalize M (basis 2) 0 = m02 at *
    generalize M (basis 2) 1 = m12 at *
    generalize M (basis 2) 2 = m22 at *
    field_simp
    linear_combination (-3*(B 0)*(g 0)^2*(g 2) - (B 0)*(g 1)^2*(g 2) - (B 0)*(g 2)^3 - 2*(B 1)*(g
      0)*(g 1)*(g 2) + (B 2)*(g 0)^3 + (B 2)*(g 0)*(g 1)^2 - (B 2)*(g 0)*(g 2)^2) * htr + ((g
      0)^2*m02 + (g 0)^2*m20 + (g 0)*(g 1)*m12 + (g 0)*(g 1)*m21 + 2*(g 0)*(g 2)*m11 + 4*(g 0)*(g
      2)*m22 - (g 1)*(g 2)*m01 - (g 1)*(g 2)*m10 - (g 2)^2*m02 - (g 2)^2*m20) * hBg
  · simp only [shearRate, eikBase, inner_coords, norm_sq_coords, PiLp.add_apply,
      PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, tApply_coords, map_smul, e B, e g,
      e (cross B g), (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
    generalize M (basis 0) 0 = m00 at *
    generalize M (basis 0) 1 = m10 at *
    generalize M (basis 0) 2 = m20 at *
    generalize M (basis 1) 0 = m01 at *
    generalize M (basis 1) 1 = m11 at *
    generalize M (basis 1) 2 = m21 at *
    generalize M (basis 2) 0 = m02 at *
    generalize M (basis 2) 1 = m12 at *
    generalize M (basis 2) 2 = m22 at *
    field_simp
    linear_combination (3*(B 0)*(g 0)^2*(g 1) + (B 0)*(g 1)^3 + (B 0)*(g 1)*(g 2)^2 - (B 1)*(g
      0)^3 + (B 1)*(g 0)*(g 1)^2 - (B 1)*(g 0)*(g 2)^2 + 2*(B 2)*(g 0)*(g 1)*(g 2)) * htr + (-(g
      0)^2*m01 - (g 0)^2*m10 - 4*(g 0)*(g 1)*m11 - 2*(g 0)*(g 1)*m22 - (g 0)*(g 2)*m12 - (g 0)*(g
      2)*m21 + (g 1)^2*m01 + (g 1)^2*m10 + (g 1)*(g 2)*m02 + (g 1)*(g 2)*m20) * hBg

/-- Derivative of a cross product along a curve. -/
theorem hasDerivAt_cross {u v : ℝ → Space} {u' v' : Space} {t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun t => cross (u t) (v t)) (cross u' (v t) + cross (u t) v') t := by
  have := crossBilinear.hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hv)
  simp only [crossBilinear_apply] at this
  rw [add_comm]; exact this

/-- **Transport of the covering-space eikonal.** Along a field line `X' = B(X)` with
`(∇ψ ∘ X)' = −Mᵀ ∇ψ` (`hG`), `∇ · B = 0` and `B ⊥ ∇ψ ≠ 0`, if `σ' = shearRate` then
`k(t) = k₀(X) − (σ(t) − c) ∇ψ(X)` satisfies `k' = −Mᵀ k`, for every shift `c`. -/
theorem hasDerivAt_eik {X : ℝ → Space} {Bf gf : Space → Space} {M G : Space →L[ℝ] Space}
    {σ : ℝ → ℝ} {t c : ℝ} (hX : HasDerivAt X (Bf (X t)) t) (hB : HasFDerivAt Bf M (X t))
    (hg : HasFDerivAt gf G (X t)) (hG : G (Bf (X t)) = -tApply M (gf (X t)))
    (htr : divergence M = 0) (hBg : ⟪Bf (X t), gf (X t)⟫ = 0) (hg0 : gf (X t) ≠ 0)
    (hσ : HasDerivAt σ (shearRate M (Bf (X t)) (gf (X t))) t) :
    HasDerivAt (fun t => eik (Bf (X t)) (gf (X t)) (σ t - c))
      (-tApply M (eik (Bf (X t)) (gf (X t)) (σ t - c))) t := by
  have hb : HasDerivAt (fun t => Bf (X t)) (M (Bf (X t))) t := hB.comp_hasDerivAt t hX
  have hgl : HasDerivAt (fun t => gf (X t)) (-tApply M (gf (X t))) t := by
    have := hg.comp_hasDerivAt t hX; rwa [hG] at this
  have hn : ‖gf (X t)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg0)
  have hN := (hgl.norm_sq).inv hn
  have hC := hasDerivAt_cross hb hgl
  have hk := ((hN.smul hC).sub ((hσ.sub_const c).smul hgl))
  refine hk.congr_deriv ?_
  have key := transport_identity M (Bf (X t)) (gf (X t)) htr hBg hg0
  set B := Bf (X t)
  set g := gf (X t)
  rw [eik, eikBase]
  have lin : tApply M (((‖g‖ ^ 2)⁻¹ • cross B g) - (σ t - c) • g) =
      tApply M ((‖g‖ ^ 2)⁻¹ • cross B g) - (σ t - c) • tApply M g := by
    apply space_ext <;> simp [tApply_coords] <;> ring
  rw [lin]
  rw [← sub_eq_zero]
  have : (-(2 * ⟪g, -tApply M g⟫) / (‖g‖ ^ 2) ^ 2) • cross B g +
        (‖g‖ ^ 2)⁻¹ • (cross (M B) g + cross B (-tApply M g)) =
      shearRate M B g • g - tApply M ((‖g‖ ^ 2)⁻¹ • cross B g) := by
    rw [← key]; abel
  have e : (fun x => ‖gf (X x)‖ ^ 2)⁻¹ t = (‖g‖ ^ 2)⁻¹ := rfl
  rw [e, add_comm ((‖g‖ ^ 2)⁻¹ • _), this, smul_neg]
  abel

/-- **The flux-function gradient is transported.** If `ψ` is `C²` at `x`, has gradient `g` on
a neighbourhood of `x`, and `B · g = 0` there, then `g` is differentiable at `x` with a
derivative `G` such that `G B = −Mᵀ g` (`M = DB(x)`): differentiate `B · ∇ψ = 0` and use the
symmetry of the Hessian. -/
theorem transport_of_hessian {ψ : Space → ℝ} {Bf gf : Space → Space} {V : Set Space}
    {x : Space} {M : Space →L[ℝ] Space} (hV : V ∈ nhds x) (hψ : ContDiffAt ℝ 2 ψ x)
    (hgrad : ∀ y ∈ V, HasFDerivAt ψ (innerSL ℝ (gf y)) y)
    (htan : ∀ y ∈ V, ⟪Bf y, gf y⟫ = 0) (hB : HasFDerivAt Bf M x) :
    ∃ G : Space →L[ℝ] Space, HasFDerivAt gf G x ∧ G (Bf x) = -tApply M (gf x) := by
  set H := fderiv ℝ (fderiv ℝ ψ) x
  have hH : HasFDerivAt (fderiv ℝ ψ) H x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm := hψ.isSymmSndFDerivAt (by simp)
  have hfd : ∀ y ∈ V, fderiv ℝ ψ y = innerSL ℝ (gf y) := fun y hy => (hgrad y hy).fderiv
  -- coordinates of `g`
  have hcoord : ∀ k : Fin 3, HasFDerivAt (fun y => gf y k)
      ((ContinuousLinearMap.apply ℝ ℝ (basis k)).comp H) x := by
    intro k
    have h1 : HasFDerivAt (fun y => fderiv ℝ ψ y (basis k))
        ((ContinuousLinearMap.apply ℝ ℝ (basis k)).comp H) x :=
      (ContinuousLinearMap.apply ℝ ℝ (basis k)).hasFDerivAt.comp x hH
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hV] with y hy
    rw [hfd y hy, innerSL_apply_apply]
    fin_cases k <;> simp [basis, inner_coords]
  refine ⟨_, hasFDerivAt_of_coords hcoord, ?_⟩
  -- derivative of `⟪B, g⟫ = 0`
  have hzero : HasFDerivAt (fun y => fderiv ℝ ψ y (Bf y)) (0 : Space →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hV] with y hy
    rw [hfd y hy, innerSL_apply_apply, real_inner_comm, htan y hy]
  have happ := hH.clm_apply hB
  have huniq := happ.unique hzero
  have hrow : ∀ w : Space, H w (Bf x) = -⟪gf x, M w⟫ := by
    intro w
    have := congrArg (fun L : Space →L[ℝ] ℝ => L w) huniq
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, zero_apply] at this
    rw [hfd x (mem_of_mem_nhds hV), innerSL_apply_apply] at this
    linarith
  apply space_ext <;>
  · rw [coords_apply]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      PiLp.neg_apply, tApply]
    rw [hsymm, hrow]
    simp

/-! ## Surface Riccati certificates -/

/-- The bending coefficient on the eikonal family as a function of the point data:
`1/|g|² + s² |g|²/|B|²` (`ballooningP_eik`). -/
@[expose] def eikP (B g : Space) (s : ℝ) : ℝ := 1 / ‖g‖ ^ 2 + s ^ 2 * (‖g‖ ^ 2 / ‖B‖ ^ 2)

/-- The drive on the eikonal family (`μ₀∇p = μ g`) as a function of the point data
(`ballooningQ_eik`). -/
@[expose] def eikQ (μ : ℝ) (B g κ : Space) (s : ℝ) : ℝ :=
  -(2 * μ * ⟪g, κ⟫) / ‖g‖ ^ 2 + s * (-(2 * μ * ⟪cross B g, κ⟫) / ‖B‖ ^ 2)

/-- `eikP > 0`. -/
theorem eikP_pos {B g : Space} (hg : g ≠ 0) (s : ℝ) : 0 < eikP B g s := by
  have : 0 < ‖g‖ := norm_pos_iff.mpr hg
  unfold eikP; positivity

/-- **Surface certificate theorem.** Let `t ↦ X(t)` be a field line (`X' = B(X)`), `d` a rate
function, and `Φ(x, s)` a `C¹` function with derivative `DΦ` such that, at every point of the
line and every `s`, `DΦ(x, s)(B(x), d(x)) + Φ²/P(x, s) ≤ Q(x, s)`. Then for every `σ` with
`σ' = d(X)` and every shift `c`, the line energy with coefficients `P(X, σ − c)`,
`Q(X, σ − c)` is nonnegative on every compactly supported `C¹` mode. -/
theorem energy_nonneg_of_surfaceCert {X : ℝ → Space} {Bf : Space → Space} {d : Space → ℝ}
    {Pf Qf : Space → ℝ → ℝ} {Φ : Space × ℝ → ℝ} {DΦ : Space × ℝ → (Space × ℝ →L[ℝ] ℝ)}
    (hX : ∀ t, HasDerivAt X (Bf (X t)) t) (hBc : Continuous fun t => Bf (X t))
    (hdc : Continuous fun t => d (X t))
    (hΦ : ∀ t s, HasFDerivAt Φ (DΦ (X t, s)) (X t, s))
    (hDΦ : Continuous fun p : ℝ × ℝ => DΦ (X p.1, p.2))
    (hP : ∀ t s, 0 < Pf (X t) s) (hPc : Continuous fun p : ℝ × ℝ => Pf (X p.1) p.2)
    (hQc : Continuous fun p : ℝ × ℝ => Qf (X p.1) p.2)
    (hcert : ∀ t s, DΦ (X t, s) (Bf (X t), d (X t)) + Φ (X t, s) ^ 2 / Pf (X t) s ≤
      Qf (X t) s)
    {σ : ℝ → ℝ} (hσ : ∀ t, HasDerivAt σ (d (X t)) t) (c : ℝ) {ξ ξ' : ℝ → ℝ} {a b : ℝ}
    (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy (fun t => Pf (X t) (σ t - c)) (fun t => Qf (X t) (σ t - c)) ξ ξ' := by
  have hXc : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
  let R : Riccati2D (fun t s => Pf (X t) s) (fun t s => Qf (X t) s) (fun t => d (X t)) :=
    { F := fun t s => Φ (X t, s)
      Ft := fun t s => DΦ (X t, s) (Bf (X t), 0)
      Fs := fun t s => DΦ (X t, s) (0, 1)
      hasFDeriv := fun t s => by
        have hq : HasFDerivAt (fun p : ℝ × ℝ => (X p.1, p.2))
            ((((1 : ℝ →L[ℝ] ℝ).smulRight (Bf (X t))).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
              (ContinuousLinearMap.snd ℝ ℝ ℝ)) (t, s) :=
          ((hX t).hasFDerivAt.comp (t, s) hasFDerivAt_fst).prodMk hasFDerivAt_snd
        refine ((hΦ t s).comp (t, s) hq).congr_fderiv ?_
        ext <;> simp
      Ft_cont := (hDΦ.clm_apply ((hBc.comp continuous_fst).prodMk continuous_const))
      Fs_cont := hDΦ.clm_apply continuous_const
      P_pos := hP
      ineq := fun t s => by
        have h1 := hcert t s
        have e : DΦ (X t, s) (Bf (X t), d (X t)) =
            DΦ (X t, s) (Bf (X t), 0) + d (X t) * DΦ (X t, s) (0, 1) := by
          rw [← smul_eq_mul, ← map_smul, ← map_add]; simp
        rw [e] at h1; exact h1 }
  exact riccati2D_energy_nonneg R hPc hQc hσ hdc c h

/-! ## The line data of the supplied reduction on the eikonal family -/

/-- Continuity of the eikonal along a curve. -/
theorem continuous_eik {Bt gt : ℝ → Space} {σ : ℝ → ℝ} (hB : Continuous Bt) (hg : Continuous gt)
    (hσ : Continuous σ) (hg0 : ∀ t, gt t ≠ 0) :
    Continuous fun t => eik (Bt t) (gt t) (σ t) := by
  unfold eik eikBase
  have hc : Continuous fun t => cross (Bt t) (gt t) := continuous_cross.comp (hB.prodMk hg)
  have hn : Continuous fun t => (‖gt t‖ ^ 2)⁻¹ :=
    (hg.norm.pow 2).inv₀ fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hg0 t))
  exact (hn.smul hc).sub (hσ.smul hg)

/-- **Line data of the supplied ballooning reduction on a field line** `X` (line element
`ℓ = 1`), with field `B(X)`, eikonal `k = k₀(X) − (σ − c) ∇ψ(X)`, `μ₀∇p = μ ∇ψ(X)` and
curvature `κ(X)`. -/
@[expose] def eikLine (X : ℝ → Space) (Bf gf κf : Space → Space) (μ : ℝ) (σ : ℝ → ℝ) (c : ℝ)
    (hB0 : ∀ t, Bf (X t) ≠ 0) (hg0 : ∀ t, gf (X t) ≠ 0) (hBg : ∀ t, ⟪Bf (X t), gf (X t)⟫ = 0)
    (hBc : Continuous fun t => Bf (X t)) (hgc : Continuous fun t => gf (X t))
    (hκc : Continuous fun t => κf (X t)) (hσc : Continuous σ) : LineData where
  ℓ := fun _ => 1
  B := fun t => Bf (X t)
  k := fun t => eik (Bf (X t)) (gf (X t)) (σ t - c)
  gp := fun t => μ • gf (X t)
  κ := fun t => κf (X t)
  ℓ_pos := fun _ => one_pos
  B_ne := hB0
  k_ne := fun t => eik_ne (hBg t) (hg0 t) (hB0 t) _
  ℓ_cont := continuous_const
  B_cont := hBc
  k_cont := continuous_eik hBc hgc (hσc.sub continuous_const) hg0
  gp_cont := (continuous_const (y := μ)).smul hgc
  κ_cont := hκc

/-- **Stability of every eikonal family of a field line from a surface certificate.** If `Φ`
satisfies the transport–Riccati inequality
`DΦ(x, s)(B(x), d(x)) + Φ²/eikP ≤ eikQ` at every point of the line and every `s`, and
`σ' = d(X)`, then `eikLine … σ c` is ballooning stable for every shift `c`. -/
theorem eikLine_stable_of_surfaceCert {X : ℝ → Space} {Bf gf κf : Space → Space} {μ : ℝ}
    {d : Space → ℝ} {σ : ℝ → ℝ} {Φ : Space × ℝ → ℝ} {DΦ : Space × ℝ → (Space × ℝ →L[ℝ] ℝ)}
    (hX : ∀ t, HasDerivAt X (Bf (X t)) t)
    (hB0 : ∀ t, Bf (X t) ≠ 0) (hg0 : ∀ t, gf (X t) ≠ 0) (hBg : ∀ t, ⟪Bf (X t), gf (X t)⟫ = 0)
    (hBc : Continuous fun t => Bf (X t)) (hgc : Continuous fun t => gf (X t))
    (hκc : Continuous fun t => κf (X t)) (hdc : Continuous fun t => d (X t))
    (hσ : ∀ t, HasDerivAt σ (d (X t)) t)
    (hΦ : ∀ t s, HasFDerivAt Φ (DΦ (X t, s)) (X t, s))
    (hDΦ : Continuous fun p : ℝ × ℝ => DΦ (X p.1, p.2))
    (hcert : ∀ t s, DΦ (X t, s) (Bf (X t), d (X t)) +
      Φ (X t, s) ^ 2 / eikP (Bf (X t)) (gf (X t)) s ≤ eikQ μ (Bf (X t)) (gf (X t)) (κf (X t)) s)
    (c : ℝ) :
    (eikLine X Bf gf κf μ σ c hB0 hg0 hBg hBc hgc hκc
      (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)).Stable := by
  intro ξ ξ' a b h
  have hP : (eikLine X Bf gf κf μ σ c hB0 hg0 hBg hBc hgc hκc
      (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)).P =
      fun t => eikP (Bf (X t)) (gf (X t)) (σ t - c) := funext fun t =>
    ballooningP_eik (hBg t) (hg0 t) (hB0 t) _
  have hQ : (eikLine X Bf gf κf μ σ c hB0 hg0 hBg hBc hgc hκc
      (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)).Q =
      fun t => eikQ μ (Bf (X t)) (gf (X t)) (κf (X t)) (σ t - c) := funext fun t =>
    ballooningQ_eik (hBg t) (hg0 t) (hB0 t) _ _ _
  rw [hP, hQ]
  have hXc : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
  have hgn : Continuous fun t => ‖gf (X t)‖ ^ 2 := hgc.norm.pow 2
  have hBn : Continuous fun t => ‖Bf (X t)‖ ^ 2 := hBc.norm.pow 2
  have hg2 : ∀ t, ‖gf (X t)‖ ^ 2 ≠ 0 := fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hg0 t))
  have hB2 : ∀ t, ‖Bf (X t)‖ ^ 2 ≠ 0 := fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hB0 t))
  refine energy_nonneg_of_surfaceCert (Pf := fun x s => eikP (Bf x) (gf x) s)
    (Qf := fun x s => eikQ μ (Bf x) (gf x) (κf x) s) hX hBc hdc hΦ hDΦ
    (fun t s => eikP_pos (hg0 t) s) ?_ ?_ hcert hσ c h
  · unfold eikP
    have h1 : Continuous fun p : ℝ × ℝ => ‖gf (X p.1)‖ ^ 2 := hgn.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => ‖Bf (X p.1)‖ ^ 2 := hBn.comp continuous_fst
    refine (continuous_const.div h1 fun p => hg2 p.1).add
      ((continuous_snd.pow 2).mul (h1.div h2 fun p => hB2 p.1))
  · unfold eikQ
    have hi1 : Continuous fun t => ⟪gf (X t), κf (X t)⟫ := hgc.inner hκc
    have hi2 : Continuous fun t => ⟪cross (Bf (X t)) (gf (X t)), κf (X t)⟫ :=
      (continuous_cross.comp (hBc.prodMk hgc)).inner hκc
    have h1 : Continuous fun p : ℝ × ℝ => ‖gf (X p.1)‖ ^ 2 := hgn.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => ‖Bf (X p.1)‖ ^ 2 := hBn.comp continuous_fst
    have j1 : Continuous fun p : ℝ × ℝ => ⟪gf (X p.1), κf (X p.1)⟫ := hi1.comp continuous_fst
    have j2 : Continuous fun p : ℝ × ℝ => ⟪cross (Bf (X p.1)) (gf (X p.1)), κf (X p.1)⟫ :=
      hi2.comp continuous_fst
    exact (((continuous_const.mul j1).neg).div h1 fun p => hg2 p.1).add (continuous_snd.mul
        (((continuous_const.mul j2).neg).div h2 fun p => hB2 p.1))

/-- Sanity (degenerate case): with no pressure gradient (`μ = 0`) the eikonal family of every
field line is stable (certificate `Φ = 0`). -/
theorem eikLine_noDrive_stable {X : ℝ → Space} {Bf gf κf : Space → Space} {d : Space → ℝ}
    {σ : ℝ → ℝ} (hX : ∀ t, HasDerivAt X (Bf (X t)) t)
    (hB0 : ∀ t, Bf (X t) ≠ 0) (hg0 : ∀ t, gf (X t) ≠ 0) (hBg : ∀ t, ⟪Bf (X t), gf (X t)⟫ = 0)
    (hBc : Continuous fun t => Bf (X t)) (hgc : Continuous fun t => gf (X t))
    (hκc : Continuous fun t => κf (X t)) (hdc : Continuous fun t => d (X t))
    (hσ : ∀ t, HasDerivAt σ (d (X t)) t) (c : ℝ) :
    (eikLine X Bf gf κf 0 σ c hB0 hg0 hBg hBc hgc hκc
      (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)).Stable :=
  eikLine_stable_of_surfaceCert (Φ := fun _ => 0) (DΦ := fun _ => 0) hX hB0 hg0 hBg hBc hgc
    hκc hdc hσ (fun _ _ => hasFDerivAt_const _ _) continuous_const
    (fun t s => by simp [eikQ]) c

/-! ## Completeness of the eikonal family -/

/-- Every `k ⊥ B` decomposes as `a k₀ − s g` with `a = ⟪k, B × g⟫/|B|²`,
`s = −⟪k, g⟫/|g|²`. -/
theorem eq_decomp {B g k : Space} (hBg : ⟪B, g⟫ = 0) (hkB : ⟪k, B⟫ = 0) (hg : g ≠ 0)
    (hB : B ≠ 0) :
    k = (⟪k, cross B g⟫ / ‖B‖ ^ 2) • eikBase B g - (-(⟪k, g⟫ / ‖g‖ ^ 2)) • g := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  have hb : ‖B‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hB)
  rw [norm_sq_coords] at hn hb
  rw [inner_coords] at hBg hkB
  apply space_ext
  · simp only [eikBase, inner_coords, norm_sq_coords, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
    field_simp
    linear_combination (-(B 0)*(g 0)*(k 0) - (B 0)*(g 1)*(k 1) - (B 0)*(g 2)*(k 2) - (B 1)*(g
      0)*(k 1) + (B 1)*(g 1)*(k 0) - (B 2)*(g 0)*(k 2) + (B 2)*(g 2)*(k 0)) * hBg + ((B 0)*((g
      0)^2 + (g 1)^2 + (g 2)^2)) * hkB
  · simp only [eikBase, inner_coords, norm_sq_coords, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
    field_simp
    linear_combination ((B 0)*(g 0)*(k 1) - (B 0)*(g 1)*(k 0) - (B 1)*(g 0)*(k 0) - (B 1)*(g
      1)*(k 1) - (B 1)*(g 2)*(k 2) - (B 2)*(g 1)*(k 2) + (B 2)*(g 2)*(k 1)) * hBg + ((B 1)*((g
      0)^2 + (g 1)^2 + (g 2)^2)) * hkB
  · simp only [eikBase, inner_coords, norm_sq_coords, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
    field_simp
    linear_combination ((B 0)*(g 0)*(k 2) + (B 1)*(g 1)*(k 2) - (B 2)*(g 0)*(k 0) - (B 2)*(g
      1)*(k 1)) * hBg + (-(B 0)*(g 0)*(g 2) - (B 1)*(g 1)*(g 2) + (B 2)*(g 0)^2 + (B 2)*(g 1)^2)
      * hkB

/-- Along the line, the coefficient `a = ⟪k, B × g⟫/|B|²` of a transported `k ⊥ B` has zero
derivative (algebraic core: `tr M = 0`, `B ⊥ g`, `k ⊥ B`). -/
theorem coeff_deriv_identity (M : Space →L[ℝ] Space) (B g k : Space) (htr : divergence M = 0)
    (hBg : ⟪B, g⟫ = 0) (hkB : ⟪k, B⟫ = 0) :
    (⟪-tApply M k, cross B g⟫ + ⟪k, cross (M B) g + cross B (-tApply M g)⟫) * ‖B‖ ^ 2 -
      ⟪k, cross B g⟫ * (2 * ⟪B, M B⟫) = 0 := by
  rw [divergence_apply] at htr
  rw [inner_coords] at hBg hkB
  have e : ∀ v : Space, ∀ i, M v i = v 0 * M (basis 0) i + v 1 * M (basis 1) i +
      v 2 * M (basis 2) i := clm_coords M
  simp only [inner_coords, norm_sq_coords, PiLp.add_apply, PiLp.neg_apply, tApply_coords, e B,
    (cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
  generalize M (basis 0) 0 = m00 at *
  generalize M (basis 0) 1 = m10 at *
  generalize M (basis 0) 2 = m20 at *
  generalize M (basis 1) 0 = m01 at *
  generalize M (basis 1) 1 = m11 at *
  generalize M (basis 1) 2 = m21 at *
  generalize M (basis 2) 0 = m02 at *
  generalize M (basis 2) 1 = m12 at *
  generalize M (basis 2) 2 = m22 at *
  linear_combination (-(B 0)^3*(g 1)*(k 2) + (B 0)^3*(g 2)*(k 1) + (B 0)^2*(B 1)*(g 0)*(k 2) - (B
    0)^2*(B 1)*(g 2)*(k 0) + (B 0)^2*(B 2)*(g 0)*(k 1) - (B 0)^2*(B 2)*(g 1)*(k 0) - (B 0)*(B
    1)^2*(g 1)*(k 2) + (B 0)*(B 1)^2*(g 2)*(k 1) - 3*(B 0)*(B 2)^2*(g 1)*(k 2) + 3*(B 0)*(B
    2)^2*(g 2)*(k 1) + (B 1)^3*(g 0)*(k 2) - (B 1)^3*(g 2)*(k 0) + (B 1)^2*(B 2)*(g 0)*(k 1) - (B
    1)^2*(B 2)*(g 1)*(k 0) + 3*(B 1)*(B 2)^2*(g 0)*(k 2) - 3*(B 1)*(B 2)^2*(g 2)*(k 0) - (B
    2)^3*(g 0)*(k 1) + (B 2)^3*(g 1)*(k 0)) * htr + ((B 0)^2*(k 0)*m12 + (B 0)^2*(k 0)*m21 + (B
    0)^2*(k 1)*m02 + (B 0)^2*(k 1)*m20 - (B 0)^2*(k 2)*m01 - (B 0)^2*(k 2)*m10 - 2*(B 0)*(B 1)*(k
    0)*m02 - 2*(B 0)*(B 1)*(k 0)*m20 + 2*(B 0)*(B 1)*(k 1)*m12 + 2*(B 0)*(B 1)*(k 1)*m21 + 2*(B
    0)*(B 1)*(k 2)*m00 - 2*(B 0)*(B 1)*(k 2)*m11 + (B 0)*(B 2)*(k 0)*m01 + (B 0)*(B 2)*(k 0)*m10
    - 4*(B 0)*(B 2)*(k 1)*m00 - 2*(B 0)*(B 2)*(k 1)*m11 - (B 1)^2*(k 0)*m12 - (B 1)^2*(k 0)*m21 -
    (B 1)^2*(k 1)*m02 - (B 1)^2*(k 1)*m20 + (B 1)^2*(k 2)*m01 + (B 1)^2*(k 2)*m10 + 2*(B 1)*(B
    2)*(k 0)*m00 + 4*(B 1)*(B 2)*(k 0)*m11 - (B 1)*(B 2)*(k 1)*m01 - (B 1)*(B 2)*(k 1)*m10 + (B
    2)^2*(k 0)*m12 + (B 2)^2*(k 0)*m21 - (B 2)^2*(k 1)*m02 - (B 2)^2*(k 1)*m20) * hBg + (-(B
    0)^2*(g 0)*m12 - (B 0)^2*(g 0)*m21 - (B 0)^2*(g 1)*m02 - (B 0)^2*(g 1)*m20 + (B 0)^2*(g
    2)*m01 + (B 0)^2*(g 2)*m10 + 2*(B 0)*(B 1)*(g 0)*m02 + 2*(B 0)*(B 1)*(g 0)*m20 - 2*(B 0)*(B
    1)*(g 1)*m12 - 2*(B 0)*(B 1)*(g 1)*m21 - 2*(B 0)*(B 1)*(g 2)*m00 + 2*(B 0)*(B 1)*(g 2)*m11 -
    (B 0)*(B 2)*(g 0)*m01 - (B 0)*(B 2)*(g 0)*m10 + 4*(B 0)*(B 2)*(g 1)*m00 + 2*(B 0)*(B 2)*(g
    1)*m11 + (B 1)^2*(g 0)*m12 + (B 1)^2*(g 0)*m21 + (B 1)^2*(g 1)*m02 + (B 1)^2*(g 1)*m20 - (B
    1)^2*(g 2)*m01 - (B 1)^2*(g 2)*m10 - 2*(B 1)*(B 2)*(g 0)*m00 - 4*(B 1)*(B 2)*(g 0)*m11 + (B
    1)*(B 2)*(g 1)*m01 + (B 1)*(B 2)*(g 1)*m10 - (B 2)^2*(g 0)*m12 - (B 2)^2*(g 0)*m21 + (B
    2)^2*(g 1)*m02 + (B 2)^2*(g 1)*m20) * hkB

/-- Algebra of the secular rate for `k = m k₀ − s g`: the derivative of `s = −⟪k, g⟫/|g|²`
(with `k' = −Mᵀ k`, `g' = −Mᵀ g`) is `m · shearRate`. -/
theorem secular_deriv_alg (M : Space →L[ℝ] Space) (B g : Space) (m s : ℝ) (hg : g ≠ 0) :
    -((⟪m • eikBase B g - s • g, -tApply M g⟫ + ⟪-tApply M (m • eikBase B g - s • g), g⟫) *
          ‖g‖ ^ 2 - ⟪m • eikBase B g - s • g, g⟫ * (2 * ⟪g, -tApply M g⟫)) / (‖g‖ ^ 2) ^ 2 =
      m * shearRate M B g := by
  have hn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  have t1 : ⟪m • eikBase B g - s • g, -tApply M g⟫ =
      -(m * ⟪M (eikBase B g), g⟫ - s * ⟪M g, g⟫) := by
    rw [inner_neg_right, real_inner_comm, inner_tApply, map_sub, map_smul, map_smul,
      inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm g (M (eikBase B g)), real_inner_comm g (M g)]
  have t2 : ⟪-tApply M (m • eikBase B g - s • g), g⟫ =
      -(m * ⟪eikBase B g, M g⟫ - s * ⟪g, M g⟫) := by
    rw [inner_neg_left, inner_tApply, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  have t3 : ⟪m • eikBase B g - s • g, g⟫ = -(s * ‖g‖ ^ 2) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_eikBase_g,
      real_inner_self_eq_norm_sq]; ring
  have t4 : ⟪g, -tApply M g⟫ = -⟪g, M g⟫ := by
    rw [inner_neg_right, real_inner_comm, inner_tApply]
  rw [t1, t2, t3, t4, shearRate, real_inner_comm (M g) g]
  field_simp
  ring

/-- **Completeness of the eikonal family.** Along a field line with transported `∇ψ`,
`∇ · B = 0`, `B ⊥ ∇ψ`, every transported `k` (`k' = −Mᵀ k`) with `k ⊥ B` is
`k = m k₀(X) − s ∇ψ(X)` with a CONSTANT `m` and `s = −⟪k, ∇ψ⟫/|∇ψ|²`, `s' = m · shearRate`.
Hence (as `P`, `Q` are quadratic in `k`) the family `k₀ − (σ − c)∇ψ`, `σ' = shearRate`, covers
every eikonal up to scale; `m = 0` (`k ∥ ∇ψ`) carries no drive. -/
theorem eik_complete {X : ℝ → Space} {Bf gf : Space → Space} {M G : ℝ → (Space →L[ℝ] Space)}
    {k : ℝ → Space} (hX : ∀ t, HasDerivAt X (Bf (X t)) t) (hB : ∀ t, HasFDerivAt Bf (M t) (X t))
    (hg : ∀ t, HasFDerivAt gf (G t) (X t)) (hG : ∀ t, G t (Bf (X t)) = -tApply (M t) (gf (X t)))
    (htr : ∀ t, divergence (M t) = 0) (hBg : ∀ t, ⟪Bf (X t), gf (X t)⟫ = 0)
    (hg0 : ∀ t, gf (X t) ≠ 0) (hB0 : ∀ t, Bf (X t) ≠ 0)
    (hk : ∀ t, HasDerivAt k (-tApply (M t) (k t)) t) (hkB : ∀ t, ⟪k t, Bf (X t)⟫ = 0) :
    ∃ m : ℝ, ∀ t, k t = m • eikBase (Bf (X t)) (gf (X t)) -
        (-(⟪k t, gf (X t)⟫ / ‖gf (X t)‖ ^ 2)) • gf (X t) ∧
      HasDerivAt (fun t => -(⟪k t, gf (X t)⟫ / ‖gf (X t)‖ ^ 2))
        (m * shearRate (M t) (Bf (X t)) (gf (X t))) t := by
  have hb : ∀ t, HasDerivAt (fun t => Bf (X t)) (M t (Bf (X t))) t :=
    fun t => (hB t).comp_hasDerivAt t (hX t)
  have hgl : ∀ t, HasDerivAt (fun t => gf (X t)) (-tApply (M t) (gf (X t))) t := by
    intro t; have := (hg t).comp_hasDerivAt t (hX t); rwa [hG t] at this
  set a : ℝ → ℝ := fun t => ⟪k t, cross (Bf (X t)) (gf (X t))⟫ / ‖Bf (X t)‖ ^ 2 with ha_def
  have ha : ∀ t, HasDerivAt a 0 t := by
    intro t
    have hb2 : ‖Bf (X t)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hB0 t))
    have h := ((hk t).inner ℝ (hasDerivAt_cross (hb t) (hgl t))).div (hb t).norm_sq hb2
    refine h.congr_deriv ?_
    have key := coeff_deriv_identity (M t) (Bf (X t)) (gf (X t)) (k t) (htr t) (hBg t) (hkB t)
    rw [div_eq_zero_iff]; left
    linear_combination key
  have hconst : ∀ t, a t = a 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (ha t).differentiableAt) (fun t => (ha t).deriv) t 0
  refine ⟨a 0, fun t => ⟨?_, ?_⟩⟩
  · rw [← hconst t]; exact eq_decomp (hBg t) (hkB t) (hg0 t) (hB0 t)
  · have hn : ‖gf (X t)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hg0 t))
    have h := (((hk t).inner ℝ (hgl t)).div (hgl t).norm_sq hn).neg
    refine h.congr_deriv ?_
    have hdec := eq_decomp (hBg t) (hkB t) (hg0 t) (hB0 t)
    rw [show ⟪k t, cross (Bf (X t)) (gf (X t))⟫ / ‖Bf (X t)‖ ^ 2 = a 0 from hconst t] at hdec
    have := secular_deriv_alg (M t) (Bf (X t)) (gf (X t)) (a 0)
      (-(⟪k t, gf (X t)⟫ / ‖gf (X t)‖ ^ 2)) (hg0 t)
    rw [← hdec] at this
    rw [← this]
    ring

end PlasmaLean.Stability.BallooningSurface
