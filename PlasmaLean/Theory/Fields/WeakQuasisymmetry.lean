/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CurlProduct
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Weak quasisymmetry, its defect, and the magnetic-axis obstruction

Source: Constantin, Drivas & Ginsberg, *On quasisymmetric plasma equilibria sustained by small
force*, arXiv:2009.08860, Definition 1, eqs. (1.7)–(1.9) (the weak form of Rodríguez, Helander &
Bhattacharjee, arXiv:2004.11431). Research note: `notes/theory/quasisymmetric-solution.md` (N-27),
§2 and §5.1; question Q-16.

## Definitions

A magnetic field `B` is **weakly quasisymmetric** on a set `T ⊆ ℝ³` with generator `ξ` and
potential `ψ` (`WeakQS B ξ ψ T`) if, at every point of `T`,

* `ξ ≠ 0` (CDG require a non-vanishing generator),
* `div ξ = 0`,
* `B × ξ = -∇ψ`,
* `ξ · ∇|B| = 0` (`qsError B ξ x = 0`),

with `|B|`, `ξ` and `ψ` differentiable there (so no condition is satisfied vacuously through
Lean's totalized `fderiv`). Consequences: `ψ` is a first integral of both `B` and `ξ`
(`WeakQS.inner_field_gradient`, `WeakQS.inner_xi_gradient`), so `ξ` is tangent to the level
sets of `ψ`. CDG's tangency of `ξ` to `∂T` is a boundary condition used only for global
arguments and is not part of this pointwise definition; neither is `[ξ, B] = 0` (CDG derive
it) nor the strong-QS condition `ξ × J = ∇(B · ξ)`.

`WeakQSDefect B ξ ψ T δ₀ δ₁ δ₂` is the certified-defect version of N-27 §2:
`|div ξ| ≤ δ₀`, `‖B × ξ + ∇ψ‖ ≤ δ₁`, `|ξ · ∇|B|| ≤ δ₂` on `T`. `weakQS_iff_defect_zero`:
exact weak QS is the case `δ₀ = δ₁ = δ₂ = 0`. The scalar measure
`qsDefect B ξ T = sup_{x ∈ T} |ξ · ∇|B||` takes values in `ℝ≥0∞`, so an unbounded error is `⊤`
rather than a totalized `0` (`qsDefect_le_ofReal_iff`, `qsDefect_eq_zero_iff`).

## Exact symmetry is a special case

`qsError_eq_zero_of_invariant`: if `|B|` is invariant along a curve through `x` with velocity
`ξ x`, then `ξ · ∇|B| = 0` at `x`. `qsError_rotGen_eq_zero_of_axisymmetric` applies this to the
rotations about the `z`-axis, with generator `∂_φ = e_z × x` (`rotGen`).

## The axis lemma (N-27 §5.1)

`WeakQS.normB_const_of_gradient_eq_zero`: if `B` is weakly QS on `T`, `γ` is a field line of `B`
(up to an arbitrary time change, `γ' = κ B(γ)`) lying in `T`, and `∇ψ = 0` along `γ`, then
`|B|` is constant along `γ`. (On `γ`, `B × ξ = 0` and `ξ ≠ 0` force `B ∥ ξ`, so `γ` is tangent
to `ξ`, along which `|B|` is invariant.) `div ξ = 0` is not used. `∇ψ = 0` holds when `ψ` has a
local extremum at each point of `γ` (`WeakQS.normB_const_of_isLocalExtr`), e.g. when `ψ` is a
differentiable function of a flux label minimal on the magnetic axis.

## Sanity triad

* degenerate: the uniform field `e_z` with generator `e_z` (`weakQS_uniform`);
* concrete instance: the axisymmetric screw-pinch field `B = e_z × x + e_z` with `ξ = ∂_φ` and
  `ψ = (x² + y²)/2` (flux surfaces: cylinders) on `{x² + y² > 0}` (`weakQS_screw`);
* counterexample: the mirror field `(1 + x²) e_x` is not weakly QS on any set containing the
  `x`-axis with `∇ψ = 0` there (`not_weakQS_mirror`), because `|B|` varies along that field line.
-/

open scoped RealInnerProductSpace ENNReal
open InnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Fields
open WithLp

/-! ## Definitions -/

/-- The quasisymmetry error `ξ · ∇|B|` at `x`: the derivative of `|B|` along `ξ(x)`. -/
@[expose] def qsError (B ξ : Space → Space) (x : Space) : ℝ :=
  fderiv ℝ (fun y => ‖B y‖) x (ξ x)

/-- **Weak quasisymmetry** (CDG Definition 1, pointwise on `T`): a non-vanishing,
divergence-free generator `ξ` and a potential `ψ` with `B × ξ = -∇ψ` and `ξ · ∇|B| = 0`, all
quantities differentiable on `T`. -/
structure WeakQS (B ξ : Space → Space) (ψ : Space → ℝ) (T : Set Space) : Prop where
  /-- `|B|` is differentiable on `T` (this excludes zeros of a non-trivial `B`). -/
  normB_diff : ∀ x ∈ T, DifferentiableAt ℝ (fun y => ‖B y‖) x
  /-- The generator is differentiable on `T`. -/
  xi_diff : ∀ x ∈ T, DifferentiableAt ℝ ξ x
  /-- The potential is differentiable on `T`. -/
  psi_diff : ∀ x ∈ T, DifferentiableAt ℝ ψ x
  /-- The generator does not vanish on `T`. -/
  xi_ne : ∀ x ∈ T, ξ x ≠ 0
  /-- `div ξ = 0`. -/
  div_free : ∀ x ∈ T, divergence (fderiv ℝ ξ x) = 0
  /-- `B × ξ = -∇ψ`. -/
  cross_eq : ∀ x ∈ T, cross (B x) (ξ x) = -gradient ψ x
  /-- `ξ · ∇|B| = 0`. -/
  qs : ∀ x ∈ T, qsError B ξ x = 0

/-- **Certified weak-QS defect** (N-27 §2): the three defining equations of `WeakQS` hold up to
`δ₀`, `δ₁`, `δ₂` pointwise on `T`, with the same regularity and non-vanishing conditions. -/
structure WeakQSDefect (B ξ : Space → Space) (ψ : Space → ℝ) (T : Set Space)
    (δ₀ δ₁ δ₂ : ℝ) : Prop where
  /-- `|B|` is differentiable on `T`. -/
  normB_diff : ∀ x ∈ T, DifferentiableAt ℝ (fun y => ‖B y‖) x
  /-- The generator is differentiable on `T`. -/
  xi_diff : ∀ x ∈ T, DifferentiableAt ℝ ξ x
  /-- The potential is differentiable on `T`. -/
  psi_diff : ∀ x ∈ T, DifferentiableAt ℝ ψ x
  /-- The generator does not vanish on `T`. -/
  xi_ne : ∀ x ∈ T, ξ x ≠ 0
  /-- `|div ξ| ≤ δ₀`. -/
  div_le : ∀ x ∈ T, |divergence (fderiv ℝ ξ x)| ≤ δ₀
  /-- `‖B × ξ + ∇ψ‖ ≤ δ₁`. -/
  cross_le : ∀ x ∈ T, ‖cross (B x) (ξ x) + gradient ψ x‖ ≤ δ₁
  /-- `|ξ · ∇|B|| ≤ δ₂`. -/
  qs_le : ∀ x ∈ T, |qsError B ξ x| ≤ δ₂

/-- The scalar quasisymmetry defect `sup_{x ∈ T} |ξ · ∇|B||`, in `ℝ≥0∞` (an unbounded error
gives `⊤`, not a totalized `0`). -/
@[expose] def qsDefect (B ξ : Space → Space) (T : Set Space) : ℝ≥0∞ :=
  ⨆ x ∈ T, ENNReal.ofReal |qsError B ξ x|

/-! ## Basic properties -/

/-- **Exact weak QS is the zero-defect case.** -/
theorem weakQS_iff_defect_zero {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space} :
    WeakQS B ξ ψ T ↔ WeakQSDefect B ξ ψ T 0 0 0 := by
  constructor
  · intro h
    refine ⟨h.normB_diff, h.xi_diff, h.psi_diff, h.xi_ne, fun x hx => ?_, fun x hx => ?_,
      fun x hx => ?_⟩
    · rw [h.div_free x hx, abs_zero]
    · rw [h.cross_eq x hx, neg_add_cancel, norm_zero]
    · rw [h.qs x hx, abs_zero]
  · intro h
    refine ⟨h.normB_diff, h.xi_diff, h.psi_diff, h.xi_ne, fun x hx => ?_, fun x hx => ?_,
      fun x hx => ?_⟩
    · exact abs_nonpos_iff.mp (h.div_le x hx)
    · exact eq_neg_of_add_eq_zero_left (norm_le_zero_iff.mp (h.cross_le x hx))
    · exact abs_nonpos_iff.mp (h.qs_le x hx)

/-- Defect bounds can be relaxed. -/
theorem WeakQSDefect.mono {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    {δ₀ δ₁ δ₂ δ₀' δ₁' δ₂' : ℝ} (h : WeakQSDefect B ξ ψ T δ₀ δ₁ δ₂) (h₀ : δ₀ ≤ δ₀')
    (h₁ : δ₁ ≤ δ₁') (h₂ : δ₂ ≤ δ₂') : WeakQSDefect B ξ ψ T δ₀' δ₁' δ₂' :=
  ⟨h.normB_diff, h.xi_diff, h.psi_diff, h.xi_ne, fun x hx => (h.div_le x hx).trans h₀,
    fun x hx => (h.cross_le x hx).trans h₁, fun x hx => (h.qs_le x hx).trans h₂⟩

/-- Weak QS restricts to subsets. -/
theorem WeakQS.mono {B ξ : Space → Space} {ψ : Space → ℝ} {T T' : Set Space}
    (h : WeakQS B ξ ψ T) (hT : T' ⊆ T) : WeakQS B ξ ψ T' :=
  ⟨fun x hx => h.normB_diff x (hT hx), fun x hx => h.xi_diff x (hT hx),
    fun x hx => h.psi_diff x (hT hx), fun x hx => h.xi_ne x (hT hx),
    fun x hx => h.div_free x (hT hx), fun x hx => h.cross_eq x (hT hx),
    fun x hx => h.qs x (hT hx)⟩

/-- `qsDefect B ξ T ≤ δ` exactly when `|ξ · ∇|B|| ≤ δ` pointwise on `T` (`δ ≥ 0`). -/
theorem qsDefect_le_ofReal_iff {B ξ : Space → Space} {T : Set Space} {δ : ℝ} (hδ : 0 ≤ δ) :
    qsDefect B ξ T ≤ ENNReal.ofReal δ ↔ ∀ x ∈ T, |qsError B ξ x| ≤ δ := by
  simp only [qsDefect, iSup₂_le_iff]
  exact forall₂_congr fun x _ => ENNReal.ofReal_le_ofReal_iff hδ

/-- `qsDefect B ξ T = 0` exactly when `ξ · ∇|B| = 0` on `T`. -/
theorem qsDefect_eq_zero_iff {B ξ : Space → Space} {T : Set Space} :
    qsDefect B ξ T = 0 ↔ ∀ x ∈ T, qsError B ξ x = 0 := by
  rw [← nonpos_iff_eq_zero, ← ENNReal.ofReal_zero, qsDefect_le_ofReal_iff le_rfl]
  exact forall₂_congr fun x _ => abs_nonpos_iff

/-- A certified defect bounds the scalar defect: `qsDefect ≤ δ₂`. -/
theorem WeakQSDefect.qsDefect_le {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    {δ₀ δ₁ δ₂ : ℝ} (h : WeakQSDefect B ξ ψ T δ₀ δ₁ δ₂) :
    qsDefect B ξ T ≤ ENNReal.ofReal δ₂ :=
  iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (h.qs_le x hx)

/-- An exactly weakly QS field has zero scalar defect. -/
theorem WeakQS.qsDefect_eq_zero {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (h : WeakQS B ξ ψ T) : qsDefect B ξ T = 0 :=
  qsDefect_eq_zero_iff.mpr h.qs

/-- `⟪u, u × v⟫ = 0`. -/
theorem inner_cross_left_self (u v : Space) : ⟪u, cross u v⟫ = 0 := by
  obtain ⟨h0, h1, h2⟩ := cross_coords u v
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, h0, h1, h2,
    star_trivial]
  ring

/-- `⟪v, u × v⟫ = 0`. -/
theorem inner_cross_right_self (u v : Space) : ⟪v, cross u v⟫ = 0 := by
  obtain ⟨h0, h1, h2⟩ := cross_coords u v
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, h0, h1, h2,
    star_trivial]
  ring

/-- `ψ` is a first integral of `B`: `B · ∇ψ = 0` on `T`. -/
theorem WeakQS.inner_field_gradient {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (h : WeakQS B ξ ψ T) {x : Space} (hx : x ∈ T) : ⟪B x, gradient ψ x⟫ = 0 := by
  rw [← neg_neg (gradient ψ x), ← h.cross_eq x hx, inner_neg_right, inner_cross_left_self,
    neg_zero]

/-- The generator is tangent to the level sets of `ψ`: `ξ · ∇ψ = 0` on `T`. -/
theorem WeakQS.inner_xi_gradient {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (h : WeakQS B ξ ψ T) {x : Space} (hx : x ∈ T) : ⟪ξ x, gradient ψ x⟫ = 0 := by
  rw [← neg_neg (gradient ψ x), ← h.cross_eq x hx, inner_neg_right, inner_cross_right_self,
    neg_zero]

/-! ## Exact symmetry is a special case -/

/-- **Invariance gives zero QS error.** If `|B|` is constant along a curve `c` with `c 0 = x`
and `c'(0) = ξ x`, and `|B|` is differentiable at `x`, then `ξ · ∇|B| = 0` at `x`. -/
theorem qsError_eq_zero_of_invariant {B ξ : Space → Space} {x : Space} (c : ℝ → Space)
    (hc0 : c 0 = x) (hc : HasDerivAt c (ξ x) 0) (hd : DifferentiableAt ℝ (fun y => ‖B y‖) x)
    (hinv : ∀ t, ‖B (c t)‖ = ‖B x‖) : qsError B ξ x = 0 := by
  subst hc0
  have h1 := hd.hasFDerivAt.comp_hasDerivAt 0 hc
  have h2 : (fun t => ‖B (c t)‖) = fun _ => ‖B (c 0)‖ := funext hinv
  have h3 : HasDerivAt (fun t => ‖B (c t)‖) 0 0 := h2 ▸ hasDerivAt_const 0 ‖B (c 0)‖
  exact h1.unique h3

/-- The generator of rotations about the `z`-axis, `∂_φ = e_z × x = (-y, x, 0)`. -/
@[expose] def rotGen : Space → Space := fun x => cross (basis 2) x

/-- Coordinates of `rotGen`. -/
theorem rotGen_coords (x : Space) : rotGen x 0 = -x 1 ∧ rotGen x 1 = x 0 ∧ rotGen x 2 = 0 := by
  obtain ⟨h0, h1, h2⟩ := cross_coords (basis 2) x
  refine ⟨?_, ?_, ?_⟩ <;> simp [rotGen, h0, h1, h2]

/-- `rotGen` is the continuous linear map `crossBilinear e_z`. -/
theorem rotGen_eq_clm : rotGen = ⇑(crossBilinear (basis 2)) := rfl

/-- `∂_φ` is divergence free. -/
theorem rotGen_divergence (x : Space) : divergence (fderiv ℝ rotGen x) = 0 := by
  rw [rotGen_eq_clm, ContinuousLinearMap.fderiv, divergence_rotation]

/-- `∂_φ` is differentiable. -/
theorem rotGen_differentiableAt (x : Space) : DifferentiableAt ℝ rotGen x := by
  rw [rotGen_eq_clm]; exact (crossBilinear (basis 2)).differentiableAt

/-- `∂_φ` vanishes exactly on the `z`-axis. -/
theorem rotGen_ne_zero {x : Space} (hx : 0 < x 0 ^ 2 + x 1 ^ 2) : rotGen x ≠ 0 := by
  intro h
  obtain ⟨h0, h1, -⟩ := rotGen_coords x
  rw [h] at h0 h1
  simp only [PiLp.zero_apply] at h0 h1
  have : x 1 = 0 := by linarith
  rw [← h1, this] at hx
  norm_num at hx

/-- Rotation by angle `t` about the `z`-axis:
`R_t x = cos t (x - x_z e_z) + sin t (e_z × x) + x_z e_z`. -/
@[expose] def rotZ (t : ℝ) (x : Space) : Space :=
  Real.cos t • (x - x 2 • basis 2) + Real.sin t • rotGen x + x 2 • basis 2

/-- `R_0 = id`. -/
theorem rotZ_zero (x : Space) : rotZ 0 x = x := by
  simp [rotZ]

/-- `t ↦ R_t x` has velocity `∂_φ` at `t = 0`. -/
theorem rotZ_hasDerivAt (x : Space) : HasDerivAt (fun t => rotZ t x) (rotGen x) 0 := by
  have h := (((Real.hasDerivAt_cos 0).smul_const (x - x 2 • basis 2)).add
    ((Real.hasDerivAt_sin 0).smul_const (rotGen x))).add_const (x 2 • basis 2)
  simpa [rotZ] using h

/-- Coordinates of `R_t x`. -/
theorem rotZ_coords (t : ℝ) (x : Space) :
    rotZ t x 0 = Real.cos t * x 0 - Real.sin t * x 1 ∧
    rotZ t x 1 = Real.cos t * x 1 + Real.sin t * x 0 ∧ rotZ t x 2 = x 2 := by
  obtain ⟨h0, h1, h2⟩ := rotGen_coords x
  refine ⟨?_, ?_, ?_⟩ <;> simp [rotZ, h0, h1, h2]
  ring

/-- Rotation about `z` preserves `x² + y²`. -/
theorem rotZ_radius (t : ℝ) (x : Space) :
    rotZ t x 0 ^ 2 + rotZ t x 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  obtain ⟨h0, h1, -⟩ := rotZ_coords t x
  rw [h0, h1]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.cos_sq_add_sin_sq t

/-- **Axisymmetry gives zero QS error with `ξ = ∂_φ`**: if `|B|` is invariant under all rotations
about the `z`-axis and differentiable at `x`, then `∂_φ · ∇|B| = 0` at `x`. -/
theorem qsError_rotGen_eq_zero_of_axisymmetric {B : Space → Space} {x : Space}
    (hsym : ∀ t y, ‖B (rotZ t y)‖ = ‖B y‖) (hd : DifferentiableAt ℝ (fun y => ‖B y‖) x) :
    qsError B rotGen x = 0 :=
  qsError_eq_zero_of_invariant (fun t => rotZ t x) (rotZ_zero x) (rotZ_hasDerivAt x) hd
    (fun t => hsym t x)

/-! ## The axis lemma -/

/-- If `ξ ≠ 0` and `b × ξ = 0`, then `b` is a multiple of `ξ`. -/
theorem exists_smul_of_cross_eq_zero {b ξ : Space} (hξ : ξ ≠ 0) (h : cross b ξ = 0) :
    ∃ c : ℝ, b = c • ξ := by
  obtain ⟨h0, h1, h2⟩ := cross_coords b ξ
  rw [h] at h0 h1 h2
  simp only [PiLp.zero_apply] at h0 h1 h2
  by_cases a0 : ξ 0 = 0
  · by_cases a1 : ξ 1 = 0
    · have a2 : ξ 2 ≠ 0 := fun a2 => hξ ((space_eq_zero_iff ξ).mpr ⟨a0, a1, a2⟩)
      refine ⟨b 2 / ξ 2, space_ext ?_ ?_ ?_⟩ <;> simp only [PiLp.smul_apply, smul_eq_mul] <;>
        rw [div_mul_eq_mul_div, eq_div_iff a2] <;> linarith
    · refine ⟨b 1 / ξ 1, space_ext ?_ ?_ ?_⟩ <;> simp only [PiLp.smul_apply, smul_eq_mul] <;>
        rw [div_mul_eq_mul_div, eq_div_iff a1] <;> linarith
  · refine ⟨b 0 / ξ 0, space_ext ?_ ?_ ?_⟩ <;> simp only [PiLp.smul_apply, smul_eq_mul] <;>
      rw [div_mul_eq_mul_div, eq_div_iff a0] <;> linarith

/-- **`|B|` is constant along a curve tangent to the generator.** If `γ' = κ ξ(γ)`, `|B|` is
differentiable along `γ` and `ξ · ∇|B| = 0` there, then `|B ∘ γ|` is constant. -/
theorem normB_const_of_tangent_generator {B ξ : Space → Space} (γ : ℝ → Space) (κ : ℝ → ℝ)
    (hγ : ∀ t, HasDerivAt γ (κ t • ξ (γ t)) t)
    (hd : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (γ t))
    (hq : ∀ t, qsError B ξ (γ t) = 0) (s t : ℝ) : ‖B (γ s)‖ = ‖B (γ t)‖ := by
  have hder : ∀ t, HasDerivAt (fun t => ‖B (γ t)‖) 0 t := by
    intro t
    have h := (hd t).hasFDerivAt.comp_hasDerivAt t (hγ t)
    rwa [map_smul, show fderiv ℝ (fun y => ‖B y‖) (γ t) (ξ (γ t)) = 0 from hq t, smul_zero]
      at h
  exact is_const_of_deriv_eq_zero (fun t => (hder t).differentiableAt)
    (fun t => (hder t).deriv) s t

/-- **The axis lemma (N-27 §5.1).** Let `B` be weakly QS on `T` with generator `ξ` and potential
`ψ`. Let `γ` be a field line of `B` up to an arbitrary time change (`γ' = κ B(γ)`), lying in `T`,
with `∇ψ = 0` along `γ` (as on a magnetic axis where `ψ` is a function of a flux label). Then
`|B|` is constant along `γ`. -/
theorem WeakQS.normB_const_of_gradient_eq_zero {B ξ : Space → Space} {ψ : Space → ℝ}
    {T : Set Space} (h : WeakQS B ξ ψ T) (γ : ℝ → Space) (κ : ℝ → ℝ)
    (hγ : ∀ t, HasDerivAt γ (κ t • B (γ t)) t) (hT : ∀ t, γ t ∈ T)
    (hψ : ∀ t, gradient ψ (γ t) = 0) (s t : ℝ) : ‖B (γ s)‖ = ‖B (γ t)‖ := by
  have hpar : ∀ t, ∃ c : ℝ, B (γ t) = c • ξ (γ t) := fun t =>
    exists_smul_of_cross_eq_zero (h.xi_ne _ (hT t)) (by rw [h.cross_eq _ (hT t), hψ t, neg_zero])
  choose c hc using hpar
  refine normB_const_of_tangent_generator γ (fun t => κ t * c t) (fun t => ?_)
    (fun t => h.normB_diff _ (hT t)) (fun t => h.qs _ (hT t)) s t
  rw [mul_smul, ← hc t]
  exact hγ t

/-- A local extremum has zero gradient. -/
theorem gradient_eq_zero_of_isLocalExtr {ψ : Space → ℝ} {x : Space} (h : IsLocalExtr ψ x) :
    gradient ψ x = 0 := by
  simp [gradient, h.fderiv_eq_zero]

/-- **The axis lemma, extremum form.** As `WeakQS.normB_const_of_gradient_eq_zero`, with
`∇ψ = 0` replaced by: `ψ` has a local extremum at each point of `γ`. -/
theorem WeakQS.normB_const_of_isLocalExtr {B ξ : Space → Space} {ψ : Space → ℝ}
    {T : Set Space} (h : WeakQS B ξ ψ T) (γ : ℝ → Space) (κ : ℝ → ℝ)
    (hγ : ∀ t, HasDerivAt γ (κ t • B (γ t)) t) (hT : ∀ t, γ t ∈ T)
    (hψ : ∀ t, IsLocalExtr ψ (γ t)) (s t : ℝ) : ‖B (γ s)‖ = ‖B (γ t)‖ :=
  h.normB_const_of_gradient_eq_zero γ κ hγ hT (fun t => gradient_eq_zero_of_isLocalExtr (hψ t)) s t

/-- **Contrapositive barrier.** If `|B|` takes different values at two points of a field line
`γ` (up to time change), then `B` is not weakly QS on any `T ⊇ γ` with `∇ψ = 0` along `γ`. -/
theorem not_weakQS_of_normB_ne {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (γ : ℝ → Space) (κ : ℝ → ℝ) (hγ : ∀ t, HasDerivAt γ (κ t • B (γ t)) t)
    (hT : ∀ t, γ t ∈ T) (hψ : ∀ t, gradient ψ (γ t) = 0) {s t : ℝ}
    (hne : ‖B (γ s)‖ ≠ ‖B (γ t)‖) : ¬ WeakQS B ξ ψ T :=
  fun h => hne (h.normB_const_of_gradient_eq_zero γ κ hγ hT hψ s t)

/-! ## Sanity triad -/

/-- **Degenerate case**: the uniform field `e_z` is weakly QS on all of space with the
translation generator `e_z` and `ψ = 0`. -/
theorem weakQS_uniform :
    WeakQS (fun _ => basis 2) (fun _ => basis 2) (fun _ => 0) Set.univ where
  normB_diff _ _ := differentiableAt_const _
  xi_diff _ _ := differentiableAt_const _
  psi_diff _ _ := differentiableAt_const _
  xi_ne _ _ h := by
    have := congrArg (fun v : Space => v 2) h
    simp at this
  div_free _ _ := by simp [divergence_apply]
  cross_eq _ _ := by
    rw [gradient_fun_const, neg_zero]
    obtain ⟨h0, h1, h2⟩ := cross_coords (basis 2) (basis 2)
    apply space_ext <;> simp only [h0, h1, h2, PiLp.zero_apply] <;> ring
  qs _ _ := by simp [qsError]

/-- The axisymmetric screw-pinch field `B = e_z × x + e_z = (-y, x, 1)`. -/
@[expose] def screwField : Space → Space := fun x => rotGen x + basis 2

/-- Coordinates of the screw-pinch field. -/
theorem screwField_coords (x : Space) :
    screwField x 0 = -x 1 ∧ screwField x 1 = x 0 ∧ screwField x 2 = 1 := by
  obtain ⟨r0, r1, r2⟩ := rotGen_coords x
  refine ⟨?_, ?_, ?_⟩ <;> simp [screwField, r0, r1, r2]

/-- Its potential `ψ = (x² + y²)/2` (flux surfaces: coaxial cylinders). -/
@[expose] def screwPsi : Space → ℝ := fun x => (x 0 ^ 2 + x 1 ^ 2) / 2

/-- `∇ψ = (x, y, 0)` for the screw pinch. -/
theorem screwPsi_hasFDerivAt (x : Space) :
    HasFDerivAt screwPsi (x 0 • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) +
      x 1 • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)) x := by
  have h0 := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := HasFDerivAt.mul_const (HasFDerivAt.add (h0.pow 2) (h1.pow 2)) (1 / 2 : ℝ)
  convert h using 1
  · funext y; simp [screwPsi]; ring
  · ext v; simp; ring

/-- `∇ψ = (x, y, 0)`. -/
theorem screwPsi_gradient (x : Space) :
    gradient screwPsi x = x 0 • basis 0 + x 1 • basis 1 := by
  apply space_ext <;> rw [← fderiv_apply_basis, (screwPsi_hasFDerivAt x).fderiv] <;> simp

/-- `|B| = √(x² + y² + 1)` for the screw pinch. -/
theorem norm_screwField (x : Space) : ‖screwField x‖ = √(x 0 ^ 2 + x 1 ^ 2 + 1) := by
  obtain ⟨h0, h1, h2⟩ := rotGen_coords x
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, screwField, h0, h1, h2]
  ring

/-- `|B|` of the screw pinch is differentiable everywhere. -/
theorem screwField_norm_differentiableAt (x : Space) :
    DifferentiableAt ℝ (fun y => ‖screwField y‖) x := by
  have he : (fun y => ‖screwField y‖) = fun y : Space =>
      √((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) y ^ 2 +
        (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) y ^ 2 + 1) := by
    funext y; rw [norm_screwField]; rfl
  rw [he]
  refine DifferentiableAt.sqrt (by fun_prop) ?_
  simp only [ne_eq]
  positivity

/-- **Concrete instance**: the axisymmetric screw pinch `B = (-y, x, 1)` is weakly QS on
`{x² + y² > 0}` with generator `∂_φ` and `ψ = (x² + y²)/2`. -/
theorem weakQS_screw :
    WeakQS screwField rotGen screwPsi {x | 0 < x 0 ^ 2 + x 1 ^ 2} where
  normB_diff x _ := screwField_norm_differentiableAt x
  xi_diff x _ := rotGen_differentiableAt x
  psi_diff x _ := (screwPsi_hasFDerivAt x).differentiableAt
  xi_ne _ hx := rotGen_ne_zero hx
  div_free x _ := rotGen_divergence x
  cross_eq x _ := by
    rw [screwPsi_gradient]
    obtain ⟨r0, r1, r2⟩ := rotGen_coords x
    obtain ⟨s0, s1, s2⟩ := screwField_coords x
    obtain ⟨h0, h1, h2⟩ := cross_coords (screwField x) (rotGen x)
    apply space_ext <;> simp [h0, h1, h2, r0, r1, r2, s0, s1, s2]
    ring
  qs x _ := by
    refine qsError_rotGen_eq_zero_of_axisymmetric (fun t y => ?_)
      (screwField_norm_differentiableAt x)
    rw [norm_screwField, norm_screwField, rotZ_radius]

/-- The mirror field `B = (1 + x²) e_x`: its field strength varies along the `x`-axis. -/
@[expose] def mirrorField : Space → Space := fun x => (1 + x 0 ^ 2) • basis 0

/-- The `x`-axis, `t ↦ t e_x`. -/
@[expose] def xAxis : ℝ → Space := fun t => t • basis 0

/-- The `x`-axis is a field line of the mirror field after the time change
`κ = 1/(1 + t²)`. -/
theorem xAxis_fieldLine (t : ℝ) :
    HasDerivAt xAxis ((1 + t ^ 2)⁻¹ • mirrorField (xAxis t)) t := by
  have hm : (1 + t ^ 2)⁻¹ • mirrorField (xAxis t) = basis 0 := by
    have hpos : (1 + t ^ 2) ≠ 0 := by positivity
    simp [mirrorField, xAxis, smul_smul, inv_mul_cancel₀ hpos]
  rw [hm]
  have h := (hasDerivAt_id' t).smul_const (basis 0)
  rw [one_smul] at h
  exact h

/-- **Counterexample**: the mirror field is not weakly QS, for any generator `ξ` and potential
`ψ`, on any set containing the `x`-axis on which `∇ψ = 0`: `|B| = 1` at the origin and `2` at
`e_x`. -/
theorem not_weakQS_mirror {ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (hT : ∀ t, xAxis t ∈ T) (hψ : ∀ t, gradient ψ (xAxis t) = 0) :
    ¬ WeakQS mirrorField ξ ψ T := by
  refine not_weakQS_of_normB_ne xAxis (fun t => (1 + t ^ 2)⁻¹) xAxis_fieldLine hT hψ
    (s := 0) (t := 1) ?_
  simp [mirrorField, xAxis, norm_smul]
  norm_num

end PlasmaLean.Fields
