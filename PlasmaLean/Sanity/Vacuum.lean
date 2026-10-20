/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Theory.Fields.Maxwell
public import PlasmaLean.Theory.Fields.Subharmonic

/-!
# Sanity checks for the vacuum-field kernel

Checks for `Kernel/Vacuum`:
* the kernel operators `divOp`/`curlOp` agree with `Fields.divergence`/`Fields.curl`
  of `Theory/Fields/Maxwell` (the kernel does not import the theory layer, so the
  agreement is proved here);
* degenerate and special instances: the zero field, constant fields, the
  hyperbolic field `(x, y, -2z)` (gradient of the harmonic polynomial
  `(x² + y²)/2 - z²`);
* closed filament fields away from the coil are instances, GIVEN `C²` regularity
  on the region (the library proves only the first derivative of the
  Biot–Savart integral, so `C²` is an explicit hypothesis here);
* a rejected fixture: the rigid-rotation field `(-y, x, 0)` has curl `(0, 0, 2)`
  and is not a vacuum field on any nonempty region.
-/

open scoped RealInnerProductSpace Laplacian

public section
noncomputable section

namespace PlasmaLean.Sanity
open PlasmaLean.Vacuum PlasmaLean.Fields

/-! ### Agreement with the theory-layer operators -/

/-- The kernel divergence agrees with `Fields.divergence`. -/
theorem divOp_eq_divergence (L : Space →L[ℝ] Space) : divOp L = divergence L := by
  rw [divOp_apply, divergence_apply]

/-- The kernel curl agrees with `Fields.curl`. -/
theorem curlOp_eq_curl (L : Space →L[ℝ] Space) : curlOp L = curl L := by
  obtain ⟨h0, h1, h2⟩ := curl_coords L
  apply space_ext <;> simp [curlOp, h0, h1, h2]

/-- Cross-check of conventions: the field `B = x` has kernel divergence `3`. -/
theorem divOp_id : divOp (ContinuousLinearMap.id ℝ Euclid3) = 3 := by
  rw [divOp_eq_divergence]
  exact divergence_id

/-! ### Accepted fixtures -/

/-- Degenerate case: the zero field is a vacuum field on every open region. -/
theorem zero_vacuum {Ω : Set Euclid3} (hΩ : IsOpen Ω) : VacuumField Ω (fun _ => 0) := by
  simpa using vacuumField_affine hΩ 0 0 (by simp [divOp]) (by ext k; fin_cases k <;> simp [curlOp])

/-- A uniform (constant) field is a vacuum field on every open region. -/
theorem const_vacuum {Ω : Set Euclid3} (hΩ : IsOpen Ω) (B₀ : Euclid3) :
    VacuumField Ω (fun _ => B₀) := by
  simpa using vacuumField_affine hΩ B₀ 0 (by simp [divOp])
    (by ext k; fin_cases k <;> simp [curlOp])

/-- A closed filament field is a vacuum field on any open region `Ω` that avoids
the coil, provided the field is `C²` on `Ω` (supplied hypothesis; the library
currently proves only first-order differentiability of the Biot–Savart integral).
The divergence and curl conditions come from `filamentField_vacuum_maxwell`. -/
theorem filamentField_vacuumField (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) {Ω : Set Space}
    (hΩ : IsOpen Ω) (hc : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ c t)
    (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ x ∈ Ω, ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) (closed : c a = c b)
    (hC2 : ContDiffOn ℝ 2 (filamentField μ₀ I c a b) Ω) :
    VacuumField Ω (filamentField μ₀ I c a b) := by
  refine ⟨hΩ, hC2, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, divOp_eq_divergence]
    exact (filamentField_vacuum_maxwell μ₀ I c a b x hc ht (sep x hx) closed).1
  · rw [fieldCurl, curlOp_eq_curl]
    exact (filamentField_vacuum_maxwell μ₀ I c a b x hc ht (sep x hx) closed).2

/-- The harmonic polynomial `p = (x² + y²)/2 - z²`, written as `⟪y, H y⟫ / 2` with
`H` the hyperbolic field. -/
@[expose] def hyperbolicPotential (y : Euclid3) : ℝ := (1 / 2 : ℝ) * ⟪y, hyperbolicField y⟫

/-- Explicit form `p = (x² + y²)/2 - z²`. -/
theorem hyperbolicPotential_apply (y : Euclid3) :
    hyperbolicPotential y = (y 0 ^ 2 + y 1 ^ 2) / 2 - y 2 ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := hyperbolicField_coords y
  simp only [hyperbolicPotential, PiLp.inner_apply, Fin.sum_univ_three, h0, h1, h2,
    RCLike.inner_apply, conj_trivial]
  ring

/-- The hyperbolic field is a gradient: `Dp(y) v = ⟪B(y), v⟫` for `B = hyperbolicField`. -/
theorem fderiv_hyperbolicPotential (y v : Euclid3) :
    fderiv ℝ hyperbolicPotential y v = ⟪hyperbolicField y, v⟫ := by
  have hid : DifferentiableAt ℝ (fun t : Euclid3 => t) y := differentiableAt_id
  have hd : DifferentiableAt ℝ (fun t : Euclid3 => ⟪t, hyperbolicField t⟫) y :=
    hid.inner ℝ hyperbolicField.differentiableAt
  have h := fderiv_inner_apply ℝ hid (hyperbolicField.differentiableAt (x := y)) v
  rw [show hyperbolicPotential = fun t => (1 / 2 : ℝ) * ⟪t, hyperbolicField t⟫ from rfl,
    fderiv_const_mul hd, smul_apply, h, hyperbolicField.fderiv, fderiv_fun_id]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  obtain ⟨a0, a1, a2⟩ := hyperbolicField_coords y
  obtain ⟨b0, b1, b2⟩ := hyperbolicField_coords v
  rw [a0, a1, a2, b0, b1, b2]
  ring

/-- The potential is harmonic: `Δp = 0`. -/
theorem laplacian_hyperbolicPotential (y : Euclid3) : Δ hyperbolicPotential y = 0 := by
  have h : fderiv ℝ hyperbolicPotential = fun y => (innerSL ℝ).comp hyperbolicField y := by
    funext y
    ext v
    rw [fderiv_hyperbolicPotential]
    simp [innerSL_apply_apply]
  rw [laplacian_eq_sum_fderiv_fderiv, h,
    ((innerSL ℝ : Euclid3 →L[ℝ] Euclid3 →L[ℝ] ℝ).comp hyperbolicField).fderiv]
  have hc : ∀ j : Fin 3, (innerSL ℝ).comp hyperbolicField (coordVec j) (coordVec j) =
      hyperbolicField (coordVec j) j := fun j => by
    simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]
  simp only [hc, Fin.sum_univ_three]
  simp [hyperbolicField]
  norm_num

/-- The gradient of the harmonic polynomial `(x² + y²)/2 - z²` is a vacuum field. -/
theorem hyperbolic_gradient_vacuum : VacuumField Set.univ (fun y => hyperbolicField y) :=
  hyperbolicField_vacuum

/-! ### Rejected fixture: a field with nonzero curl -/

/-- The rigid-rotation field `B = e_z × x`. -/
@[expose] def rotationField : Euclid3 →L[ℝ] Euclid3 := crossBilinear (basis 2)

/-- Coordinates of the rotation field: `(-y, x, 0)`. -/
theorem rotationField_coords (y : Euclid3) :
    rotationField y 0 = -y 1 ∧ rotationField y 1 = y 0 ∧ rotationField y 2 = 0 := by
  obtain ⟨h0, h1, h2⟩ := cross_coords (basis 2) y
  simp only [rotationField, crossBilinear_apply, h0, h1, h2]
  simp

/-- The rotation field has curl `(0, 0, 2) = 2 e_z` everywhere. -/
theorem fieldCurl_rotationField (x : Euclid3) :
    fieldCurl (fun y => rotationField y) x = (2 : ℝ) • basis 2 := by
  rw [fieldCurl, rotationField.fderiv, curlOp_eq_curl]
  exact curl_rotation _

/-- The rotation field `(-y, x, 0)` is NOT a vacuum field on any nonempty region. -/
theorem rotationField_not_vacuum {Ω : Set Euclid3} (hne : Ω.Nonempty) :
    ¬ VacuumField Ω (fun y => rotationField y) := by
  intro h
  obtain ⟨x, hx⟩ := hne
  have h1 := h.curl_eq_zero x hx
  rw [fieldCurl_rotationField] at h1
  have h2 := congrArg (fun v : Euclid3 => v 2) h1
  simp at h2

/-! ### Theory sanity: the corrected min/max direction -/

/-- `|B|²` of a vacuum field is subharmonic; on the hyperbolic field
`Δ|B|² = 2 ∑ᵢⱼ (∂ⱼBᵢ)² = 2(1 + 1 + 4) = 12`. -/
theorem laplacian_normSq_hyperbolic (x : Euclid3) :
    Δ (normSqField (fun y => hyperbolicField y)) x = 12 := by
  rw [laplacian_normSqField hyperbolicField_vacuum (Set.mem_univ x), hyperbolicField.fderiv]
  simp [Fin.sum_univ_three, hyperbolicField]
  norm_num

end PlasmaLean.Sanity
