/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2
public import PlasmaLean.Theory.Fields.WeakQuasisymmetry

/-!
# Neither Landreman family is weakly quasisymmetric near its magnetic axis

Research note: `notes/theory/quasisymmetric-solution.md` (N-27), §5.1, route (iii) of Q-16.

The axis lemma `PlasmaLean.Fields.WeakQS.normB_const_of_gradient_eq_zero` says that a weakly
quasisymmetric field (CDG Definition 1, `WeakQS`) has constant `|B|` along any field line on
which `∇ψ = 0`. On the magnetic axes of Landreman's explicit families (arXiv:2609.26742 v2) the
compiled closed forms `LandremanEquilibrium.field_axis` and `LandremanFamily2.field_axis` give
`|B|` explicitly, and it is not constant when `ε ≠ 0`:

* family 1 (`|ε| < 1`): `|B|² = 1 - ε² + ε² cos² 2ζ` (`family1_axis_normB_sq`), equal to `1`
  at `ζ = 0` and `1 - ε²` at `ζ = π/4`;
* family 2 (`S > 0`, any `ε`, any `λ`): `|B|² = cosh²(ε cos ζ sin ζ)/(4G)`,
  `G = b_c² cos² ζ + a_c² sin² ζ` (`family2_axis_normB_sq`), equal to `1/(4 b_c²)` at `ζ = 0`
  and `1/(4 a_c²)` at `ζ = π/2`, with `b_c² - a_c² = ε`.

## The barrier (exact hypotheses)

`family1_not_weakQS` (for `|ε| < 1`, `ε ≠ 0`) and `family2_not_weakQS` (for `S > 0`, `ε ≠ 0`,
every `λ`): for **every** generator `ξ`, potential `ψ` and set `T` such that

* `T` contains the whole magnetic axis, and
* `∇ψ = 0` at every point of the axis,

the field is not `WeakQS` with `(ξ, ψ)` on `T`. Recall that `WeakQS` requires `ξ ≠ 0` on `T`, in
particular on the axis; generators vanishing on the axis (quasi-poloidal ones, `∝ ∂_θ`) are not
excluded by this argument. No condition on the helicity is needed. The hypothesis `∇ψ = 0` holds
when `ψ` has a local extremum at each axis point (`*_of_isLocalExtr`), in particular for
`ψ = F ∘ ψ_flux` with the family's own flux function `ψ_flux` (minimal, `= 0`, on the axis) and
any monotone or antitone `F` (`family1_not_weakQS_flux`, `family2_not_weakQS_flux`); no
differentiability of `F` is required.

This is a statement about these explicit families only; it says nothing about
quasisymmetry of other fields.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.LandremanNotQS
open PlasmaLean.Fields

/-! ## Family 1 -/

section Family1
open LandremanEquilibrium
variable {ε : ℝ}

/-- `|B|²` on the family-1 axis: `1 - ε² + ε² cos² 2ζ`. -/
theorem family1_axis_normB_sq (hε : |ε| < 1) (ζ : ℝ) :
    ‖LandremanEquilibrium.field (aE ε) (bE ε) (LandremanEquilibrium.axis ε ζ)‖ ^ 2 =
      1 - ε ^ 2 + ε ^ 2 * Real.cos (2 * ζ) ^ 2 := by
  have hs := Real.sin_sq_add_cos_sq ζ
  rw [field_axis hε, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three, axisVel, mul_pow, aE_sq hε, bE_sq hε]
  linear_combination (1 - ε ^ 2) * hs

/-- **`|B|` is not constant on the family-1 axis** for `ε ≠ 0`: `|B|(0) ≠ |B|(π/4)`. -/
theorem family1_axis_normB_ne (hε : |ε| < 1) (h0 : ε ≠ 0) :
    ‖LandremanEquilibrium.field (aE ε) (bE ε) (LandremanEquilibrium.axis ε 0)‖ ≠
      ‖LandremanEquilibrium.field (aE ε) (bE ε) (LandremanEquilibrium.axis ε (Real.pi / 4))‖ := by
  intro h
  have h2 := congrArg (· ^ 2) h
  simp only [family1_axis_normB_sq hε] at h2
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two] at h2
  simp only [mul_zero, Real.cos_zero] at h2
  have : ε ^ 2 = 0 := by linarith
  exact h0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/-- **Family 1 is not weakly quasisymmetric near its axis.** For `|ε| < 1`, `ε ≠ 0`, no
generator `ξ` and potential `ψ` make the field `WeakQS` on a set `T` containing the magnetic
axis with `∇ψ = 0` on the axis. -/
theorem family1_not_weakQS (hε : |ε| < 1) (h0 : ε ≠ 0) {ξ : Space → Space} {ψ : Space → ℝ}
    {T : Set Space} (hT : ∀ ζ, LandremanEquilibrium.axis ε ζ ∈ T)
    (hψ : ∀ ζ, gradient ψ (LandremanEquilibrium.axis ε ζ) = 0) :
    ¬ WeakQS (LandremanEquilibrium.field (aE ε) (bE ε)) ξ ψ T :=
  not_weakQS_of_normB_ne (LandremanEquilibrium.axis ε) (fun _ => 1)
    (fun ζ => by simpa using axis_fieldLine hε ζ) hT hψ (family1_axis_normB_ne hε h0)

/-- Family 1, extremum form: `ψ` has a local extremum at each axis point. -/
theorem family1_not_weakQS_of_isLocalExtr (hε : |ε| < 1) (h0 : ε ≠ 0) {ξ : Space → Space}
    {ψ : Space → ℝ} {T : Set Space} (hT : ∀ ζ, LandremanEquilibrium.axis ε ζ ∈ T)
    (hψ : ∀ ζ, IsLocalExtr ψ (LandremanEquilibrium.axis ε ζ)) :
    ¬ WeakQS (LandremanEquilibrium.field (aE ε) (bE ε)) ξ ψ T :=
  family1_not_weakQS hε h0 hT fun ζ => gradient_eq_zero_of_isLocalExtr (hψ ζ)

/-- The family-1 region `𝒰` is open. -/
theorem U_isOpen (a b : ℝ) : IsOpen (U a b) := by
  refine isOpen_lt continuous_const ?_
  unfold rad sF
  fun_prop

/-- The family-1 flux function has a local minimum (value `0`) at every axis point. -/
theorem family1_psi_isLocalMin (hε : |ε| < 1) (ζ : ℝ) :
    IsLocalMin (psi (aE ε) (bE ε)) (LandremanEquilibrium.axis ε ζ) := by
  filter_upwards [(U_isOpen _ _).mem_nhds (axis_mem hε ζ)] with y hy
  rw [psi_axis hε]
  exact psi_nonneg (aE_pos hε).ne' (bE_pos hε).ne' hy

/-- **Family 1, flux-function potentials.** For `|ε| < 1`, `ε ≠ 0` and any monotone or
antitone `F`, the field is not `WeakQS` with potential `F ∘ ψ_flux` on any `T ⊇` axis. -/
theorem family1_not_weakQS_flux (hε : |ε| < 1) (h0 : ε ≠ 0) {ξ : Space → Space} {F : ℝ → ℝ}
    (hF : Monotone F ∨ Antitone F) {T : Set Space}
    (hT : ∀ ζ, LandremanEquilibrium.axis ε ζ ∈ T) :
    ¬ WeakQS (LandremanEquilibrium.field (aE ε) (bE ε)) ξ (F ∘ psi (aE ε) (bE ε)) T := by
  refine family1_not_weakQS_of_isLocalExtr hε h0 hT fun ζ => ?_
  rcases hF with hF | hF
  · exact Or.inl ((family1_psi_isLocalMin hε ζ).comp_mono hF)
  · exact Or.inr ((family1_psi_isLocalMin hε ζ).comp_antitone hF)

end Family1

/-! ## Family 2 -/

section Family2
open LandremanFamily2
variable {ε S : ℝ}

/-- `|B|²` on the family-2 axis: `cosh²(ε cos ζ sin ζ)/(4G)`. -/
theorem family2_axis_normB_sq (hS : 0 < S) (lam ζ : ℝ) :
    ‖LandremanFamily2.field ε S lam (LandremanFamily2.axis ε S ζ)‖ ^ 2 =
      Real.cosh (ε * Real.cos ζ * Real.sin ζ) ^ 2 / (4 * Gax ε S ζ) := by
  have hG := Gax_pos (ε := ε) hS ζ
  have hv : ‖LandremanFamily2.axisVel ε S ζ‖ ^ 2 = Gax ε S ζ := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, LandremanFamily2.axisVel, Gax, mul_pow]
    ring
  rw [field_axis hS, norm_smul, mul_pow, hv, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- **`|B|` is not constant on the family-2 axis** for `ε ≠ 0`: `|B|(0) ≠ |B|(π/2)`. -/
theorem family2_axis_normB_ne (hS : 0 < S) (h0 : ε ≠ 0) (lam : ℝ) :
    ‖LandremanFamily2.field ε S lam (LandremanFamily2.axis ε S 0)‖ ≠
      ‖LandremanFamily2.field ε S lam (LandremanFamily2.axis ε S (Real.pi / 2))‖ := by
  intro h
  have h2 := congrArg (· ^ 2) h
  simp only [family2_axis_normB_sq hS, Gax, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, zero_mul, Real.cosh_zero] at h2
  have ha := aC_pos (ε := ε) hS
  have hb := bC_pos (ε := ε) hS
  have hab : bC ε S ^ 2 = aC ε S ^ 2 := by
    have h3 : (1 : ℝ) ^ 2 / (4 * (bC ε S ^ 2 * 1 ^ 2 + 0)) =
        1 ^ 2 / (4 * (0 + aC ε S ^ 2 * 1 ^ 2)) := by simpa using h2
    field_simp at h3
    linarith
  exact h0 (by linarith [bC_sq_sub (ε := ε) hS])

/-- **Family 2 is not weakly quasisymmetric near its axis.** For `S > 0`, `ε ≠ 0` and every
`λ`, no generator `ξ` and potential `ψ` make the field `WeakQS` on a set `T` containing the
magnetic axis with `∇ψ = 0` on the axis. -/
theorem family2_not_weakQS (hS : 0 < S) (h0 : ε ≠ 0) (lam : ℝ) {ξ : Space → Space}
    {ψ : Space → ℝ} {T : Set Space} (hT : ∀ ζ, LandremanFamily2.axis ε S ζ ∈ T)
    (hψ : ∀ ζ, gradient ψ (LandremanFamily2.axis ε S ζ) = 0) :
    ¬ WeakQS (LandremanFamily2.field ε S lam) ξ ψ T :=
  not_weakQS_of_normB_ne (LandremanFamily2.axis ε S)
    (fun ζ => 2 * Gax ε S ζ / Real.cosh (ε * Real.cos ζ * Real.sin ζ)) (axis_tangent hS lam) hT hψ
    (family2_axis_normB_ne hS h0 lam)

/-- Family 2, extremum form: `ψ` has a local extremum at each axis point. -/
theorem family2_not_weakQS_of_isLocalExtr (hS : 0 < S) (h0 : ε ≠ 0) (lam : ℝ)
    {ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (hT : ∀ ζ, LandremanFamily2.axis ε S ζ ∈ T)
    (hψ : ∀ ζ, IsLocalExtr ψ (LandremanFamily2.axis ε S ζ)) :
    ¬ WeakQS (LandremanFamily2.field ε S lam) ξ ψ T :=
  family2_not_weakQS hS h0 lam hT fun ζ => gradient_eq_zero_of_isLocalExtr (hψ ζ)

/-- The family-2 flux function has a global, hence local, minimum (value `0`) on the axis. -/
theorem family2_psi_isLocalMin (hS : 0 < S) (lam ζ : ℝ) :
    IsLocalMin (LandremanFamily2.psi ε S lam) (LandremanFamily2.axis ε S ζ) :=
  Filter.Eventually.of_forall fun y => by
    rw [LandremanFamily2.psi_axis hS]; exact LandremanFamily2.psi_nonneg ε S lam y

/-- **Family 2, flux-function potentials.** For `S > 0`, `ε ≠ 0`, every `λ` and any monotone
or antitone `F`, the field is not `WeakQS` with potential `F ∘ ψ_flux` on any `T ⊇` axis. -/
theorem family2_not_weakQS_flux (hS : 0 < S) (h0 : ε ≠ 0) (lam : ℝ) {ξ : Space → Space}
    {F : ℝ → ℝ} (hF : Monotone F ∨ Antitone F) {T : Set Space}
    (hT : ∀ ζ, LandremanFamily2.axis ε S ζ ∈ T) :
    ¬ WeakQS (LandremanFamily2.field ε S lam) ξ (F ∘ LandremanFamily2.psi ε S lam) T := by
  refine family2_not_weakQS_of_isLocalExtr hS h0 lam hT fun ζ => ?_
  rcases hF with hF | hF
  · exact Or.inl ((family2_psi_isLocalMin (ε := ε) hS lam ζ).comp_mono hF)
  · exact Or.inr
      ((family2_psi_isLocalMin (ε := ε) hS lam ζ).comp_antitone hF)

end Family2

end PlasmaLean.Design.LandremanNotQS
