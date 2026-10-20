/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Theory.Fields.Maxwell
public import PlasmaLean.Theory.Fields.FieldVariation
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smoothness of the filament field away from the coil

The Biot–Savart line integral `x ↦ ∫ t in a..b, K(x - c t) × c'(t)` is `C^∞` on any
open set that avoids the (compact) source curve `c([a, b])`.

Main results.
* `hasFDerivAt_intervalIntegral_comp_sub`: differentiation under the integral sign
  for the general "convolution along a curve" integral
  `F(x) = ∫ t in a..b, A t (Φ (x - c t))`, where `Φ` is `C¹` on an open set `V`,
  `c` and `A` are continuous on `[a, b]`, and `x - c t ∈ V` for all `t`. The
  derivative is the integral of the same form with `Φ` replaced by `DΦ` and `A t`
  replaced by `D ↦ A t ∘ D`, so the argument iterates.
* `contDiffOn_intervalIntegral_comp_sub`: if `Φ` is `C^∞` on `V`, then `F` is
  `C^∞` on every open `U` with `U - c([a, b]) ⊆ V`.
* `inverseCube_contDiffOn`: the radial kernel `r ↦ r / ‖r‖³` is `C^∞` off `0`.
* `filamentField_contDiffOn`: the filament field is `C^∞` on any open region
  avoiding the curve (continuous curve, continuous tangent `deriv c` on `[a, b]`).
* `filamentField_contDiffOn_two`: the `C²` specialisation. It discharges the `C²`
  hypothesis of `Sanity.filamentField_vacuumField`; the resulting hypothesis-free
  corollary `Sanity.filamentField_vacuumField'` lives in `Sanity/FilamentVacuum`.

Model. The integrand uses the actual derivative `deriv c`; only its continuity on
the closed parameter interval is required. Uniformity in the parameter comes from
compactness of `[a, b]` (a common distance `δ` from the curve on a neighbourhood).
-/

public section
noncomputable section

namespace PlasmaLean.Fields
open Set MeasureTheory Filter Metric
open scoped Topology Interval ContDiff

universe u

section General

variable {E H G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Differentiation under the integral along a curve.** If `Φ` is `C¹` on an open
set `V`, `c` and `A` are continuous on `[a, b]` and `x - c t ∈ V` for every
`t ∈ [a, b]`, then `y ↦ ∫ t in a..b, A t (Φ (y - c t))` has derivative
`∫ t in a..b, A t ∘ DΦ(x - c t)` at `x`. -/
theorem hasFDerivAt_intervalIntegral_comp_sub (Φ : E → H) {V : Set E} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ 1 Φ V) {c : ℝ → E} {a b : ℝ} (hc : ContinuousOn c (uIcc a b))
    {A : ℝ → H →L[ℝ] G} (hA : ContinuousOn A (uIcc a b)) {x : E}
    (hx : ∀ t ∈ uIcc a b, x - c t ∈ V) :
    HasFDerivAt (fun y => ∫ t in a..b, A t (Φ (y - c t)))
      (∫ t in a..b, (A t).comp (fderiv ℝ Φ (x - c t))) x := by
  set S := (fun t => x - c t) '' uIcc a b with hS
  have hScpt : IsCompact S := isCompact_uIcc.image_of_continuousOn (continuousOn_const.sub hc)
  have hSV : S ⊆ V := by rintro _ ⟨t, ht, rfl⟩; exact hx t ht
  obtain ⟨δ, hδ, hδV⟩ := hScpt.exists_cthickening_subset_open hV hSV
  have hK : IsCompact (cthickening δ S) := hScpt.cthickening
  have hDΦ : ContinuousOn (fderiv ℝ Φ) V := hΦ.continuousOn_fderiv_of_isOpen hV le_rfl
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hDΦ.mono hδV)
  obtain ⟨MA, hMA⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA
  have near (z : E) (hz : z ∈ ball x δ) (t : ℝ) (ht : t ∈ uIcc a b) :
      z - c t ∈ cthickening δ S := by
    apply mem_cthickening_of_dist_le _ (x - c t) _ _ (mem_image_of_mem (fun t => x - c t) ht)
    rw [dist_sub_right]
    exact (mem_ball.mp hz).le
  have nearV (z : E) (hz : z ∈ ball x δ) (t : ℝ) (ht : t ∈ uIcc a b) : z - c t ∈ V :=
    hδV (near z hz t ht)
  have hcontF (z : E) (hz : z ∈ ball x δ) :
      ContinuousOn (fun t => A t (Φ (z - c t))) (uIcc a b) :=
    hA.clm_apply (hΦ.continuousOn.comp (continuousOn_const.sub hc) (fun t ht => nearV z hz t ht))
  have hxb : x ∈ ball x δ := mem_ball_self hδ
  have hcontF' : ContinuousOn (fun t => (A t).comp (fderiv ℝ Φ (x - c t))) (uIcc a b) :=
    hA.clm_comp (hDΦ.comp (continuousOn_const.sub hc) (fun t ht => hx t ht))
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun z t => A t (Φ (z - c t))) (F' := fun z t => (A t).comp (fderiv ℝ Φ (z - c t)))
    (bound := fun _ => MA * M) (μ := volume) (a := a) (b := b)
    (ball_mem_nhds x hδ)
    (Filter.mem_of_superset (ball_mem_nhds x hδ)
      (fun z hz => ((hcontF z hz).intervalIntegrable).aestronglyMeasurable_restrict_uIoc))
    ((hcontF x hxb).intervalIntegrable)
    (hcontF'.intervalIntegrable.aestronglyMeasurable_restrict_uIoc)
    (ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht z hz => by
      have ht' := Set.uIoc_subset_uIcc ht
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul (hMA t ht') (hM _ (near z hz t ht')) (norm_nonneg _)
        ((norm_nonneg _).trans (hMA t ht'))))
    intervalIntegrable_const
    (ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht z hz => by
      have ht' := Set.uIoc_subset_uIcc ht
      have hd : HasFDerivAt Φ (fderiv ℝ Φ (z - c t)) (z - c t) :=
        ((hΦ.differentiableOn one_ne_zero _ (nearV z hz t ht')).differentiableAt
          (hV.mem_nhds (nearV z hz t ht'))).hasFDerivAt
      have h2 := (A t).hasFDerivAt.comp z (hd.comp z ((hasFDerivAt_id z).sub_const (c t)))
      convert h2 using 1 <;> (ext; simp)))
  exact h

/-- **Smoothness of integrals along a curve.** If `Φ` is `C^∞` on an open set `V`,
`c` and `A` are continuous on `[a, b]`, and `U` is an open set with
`x - c t ∈ V` for all `x ∈ U`, `t ∈ [a, b]`, then
`x ↦ ∫ t in a..b, A t (Φ (x - c t))` is `C^n` on `U` for every finite `n`. -/
theorem contDiffOn_nat_intervalIntegral_comp_sub (n : ℕ) :
    ∀ {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup G]
      [NormedSpace ℝ G] (Φ : E → H) {V : Set E}, IsOpen V → ContDiffOn ℝ ∞ Φ V →
      ∀ {c : ℝ → E} {a b : ℝ}, ContinuousOn c (uIcc a b) →
      ∀ {A : ℝ → H →L[ℝ] G}, ContinuousOn A (uIcc a b) →
      ∀ {U : Set E}, IsOpen U → (∀ x ∈ U, ∀ t ∈ uIcc a b, x - c t ∈ V) →
      ContDiffOn ℝ n (fun x => ∫ t in a..b, A t (Φ (x - c t))) U := by
  induction n with
  | zero =>
    intro H G _ _ _ _ Φ V hV hΦ c a b hc A hA U hU hUV
    simp only [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    exact (hasFDerivAt_intervalIntegral_comp_sub Φ hV (hΦ.of_le (by simp)) hc hA
      (hUV x hx)).continuousAt.continuousWithinAt
  | succ n ih =>
    intro H G _ _ _ _ Φ V hV hΦ c a b hc A hA U hU hUV
    have hd (x : E) (hx : x ∈ U) := hasFDerivAt_intervalIntegral_comp_sub Φ hV
      (hΦ.of_le (by simp)) hc hA (hUV x hx)
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hA' : ContinuousOn (fun t => ContinuousLinearMap.compL ℝ E H G (A t)) (uIcc a b) :=
      (ContinuousLinearMap.compL ℝ E H G).continuous.comp_continuousOn hA
    have key := ih (fderiv ℝ Φ) hV (hΦ.fderiv_of_isOpen hV (by simp)) hc hA' hU hUV
    refine key.congr (fun x hx => ?_)
    rw [(hd x hx).fderiv]
    rfl

/-- `C^∞` version of `contDiffOn_nat_intervalIntegral_comp_sub`. -/
theorem contDiffOn_intervalIntegral_comp_sub (Φ : E → H) {V : Set E} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ V) {c : ℝ → E} {a b : ℝ} (hc : ContinuousOn c (uIcc a b))
    {A : ℝ → H →L[ℝ] G} (hA : ContinuousOn A (uIcc a b)) {U : Set E} (hU : IsOpen U)
    (hUV : ∀ x ∈ U, ∀ t ∈ uIcc a b, x - c t ∈ V) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in a..b, A t (Φ (x - c t))) U :=
  contDiffOn_infty.mpr fun n =>
    contDiffOn_nat_intervalIntegral_comp_sub n Φ hV hΦ hc hA hU hUV

end General

/-- The radial Biot–Savart kernel `r ↦ r / ‖r‖³` is `C^∞` away from the origin. -/
theorem inverseCube_contDiffOn : ContDiffOn ℝ ∞ inverseCube {r : Space | r ≠ 0} := by
  intro r hr
  exact ((((contDiffAt_norm ℝ hr).pow 3).inv
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hr))).smul contDiffAt_id).contDiffWithinAt

/-- **The filament field is `C^∞` away from the coil.** For a curve `c` continuous on
`[a, b]` with continuous tangent `deriv c` there, the Biot–Savart field is `C^∞` on
every open set `Ω` that avoids `c([a, b])`. -/
theorem filamentField_contDiffOn (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) {Ω : Set Space}
    (hΩ : IsOpen Ω) (hc : ContinuousOn c (uIcc a b)) (ht : ContinuousOn (deriv c) (uIcc a b))
    (sep : ∀ x ∈ Ω, ∀ t ∈ uIcc a b, x - c t ≠ 0) :
    ContDiffOn ℝ ∞ (filamentField μ₀ I c a b) Ω := by
  have hA : ContinuousOn (fun t => crossBilinear (deriv c t)) (uIcc a b) :=
    crossBilinear.continuous.comp_continuousOn ht
  have h := contDiffOn_intervalIntegral_comp_sub inverseCube (isOpen_ne (x := (0 : Space)))
    inverseCube_contDiffOn hc hA hΩ sep
  have heq : filamentField μ₀ I c a b =
      fun x => (μ₀ * I / (4 * Real.pi)) •
        ∫ t in a..b, crossBilinear (deriv c t) (inverseCube (x - c t)) := by
    funext x
    simp only [filamentField, filamentKernel_eq_cross_inverseCube, crossBilinear_apply]
  rw [heq]
  exact h.const_smul _

/-- `C²` specialisation of `filamentField_contDiffOn`. -/
theorem filamentField_contDiffOn_two (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) {Ω : Set Space}
    (hΩ : IsOpen Ω) (hc : ContinuousOn c (uIcc a b)) (ht : ContinuousOn (deriv c) (uIcc a b))
    (sep : ∀ x ∈ Ω, ∀ t ∈ uIcc a b, x - c t ≠ 0) :
    ContDiffOn ℝ 2 (filamentField μ₀ I c a b) Ω :=
  (filamentField_contDiffOn μ₀ I c a b hΩ hc ht sep).of_le (by simp)

end PlasmaLean.Fields
