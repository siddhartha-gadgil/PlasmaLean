/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FieldDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Source-free Maxwell identities for the filament field

Away from the source, the magnetostatic field of a filament current is
divergence free, and for a CLOSED filament it is also curl free. These are the
vacuum Maxwell equations `∇ · B = 0` and `∇ × B = 0` in the region with no
current, proved here for the actual Fréchet derivative of the continuous
Biot–Savart integral (not a discretization).

Conventions. A spatial derivative is a continuous linear operator `L = DB(x)`,
so `L eᵢ = ∂ᵢ B`. The divergence is `∑ᵢ (L eᵢ)ᵢ`. The curl has components
`(curl L)ₖ = (L e_{k+1})_{k+2} - (L e_{k+2})_{k+1}` (indices in `Fin 3`), i.e.
`(∂_y B_z - ∂_z B_y, ∂_z B_x - ∂_x B_z, ∂_x B_y - ∂_y B_x)`.

Proof outline. With `r = x - c t` and `M = D(r/|r|³)`, `M v = v/|r|³ - 3⟪r,v⟫ r/|r|⁵`
is symmetric with zero trace. Hence `v ↦ a × M v` has zero divergence and its
curl equals `-M a`. For `a = c'(t)` this is the source-parameter derivative of
`inverseCube (x - c t)`, so the integrated curl telescopes to zero when
`c a = c b`. Open-filament segments are NOT curl free; closure is essential.
Finite-conductor fields and current inside the winding pack are not treated.
-/

open scoped RealInnerProductSpace
public section
noncomputable section
namespace PlasmaLean.Fields
open WithLp MeasureTheory

/-- Coordinate basis vector of physical space. -/
abbrev basis (i : Fin 3) : Space := EuclideanSpace.single i (1 : ℝ)

/-- Divergence as a continuous linear functional on spatial derivative operators. -/
@[expose] def divergenceCLM : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ Space (basis i))

/-- Divergence of a derivative operator: `∑ᵢ (L eᵢ)ᵢ`. -/
@[expose] def divergence (L : Space →L[ℝ] Space) : ℝ := divergenceCLM L

/-- Explicit coordinate formula for the divergence. -/
theorem divergence_apply (L : Space →L[ℝ] Space) :
    divergence L = L (basis 0) 0 + L (basis 1) 1 + L (basis 2) 2 := by
  simp [divergence, divergenceCLM, Fin.sum_univ_three]

/-- The `k`-th curl component as a continuous linear functional. -/
@[expose] def curlComponent (k : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (k + 2)).comp (ContinuousLinearMap.apply ℝ Space (basis (k + 1))) -
    (EuclideanSpace.proj (k + 1)).comp (ContinuousLinearMap.apply ℝ Space (basis (k + 2)))

/-- Curl as a continuous linear map on spatial derivative operators. -/
@[expose] def curlCLM : (Space →L[ℝ] Space) →L[ℝ] Space :=
  ∑ k : Fin 3, (curlComponent k).smulRight (basis k)

/-- Curl of a derivative operator. -/
@[expose] def curl (L : Space →L[ℝ] Space) : Space := curlCLM L

/-- The coordinates of the curl are the curl components. -/
theorem curl_apply (L : Space →L[ℝ] Space) (k : Fin 3) :
    curl L k = curlComponent k L := by
  fin_cases k <;>
    simp [curl, curlCLM, Fin.sum_univ_three]

/-- Explicit coordinate formula for the curl. -/
theorem curl_coords (L : Space →L[ℝ] Space) :
    curl L 0 = L (basis 1) 2 - L (basis 2) 1 ∧
    curl L 1 = L (basis 2) 0 - L (basis 0) 2 ∧
    curl L 2 = L (basis 0) 1 - L (basis 1) 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [curl_apply] <;> simp [curlComponent]

/-- A vector vanishes iff its three coordinates do. -/
theorem space_eq_zero_iff (v : Space) : v = 0 ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;> simpa

/-- Extensionality for physical vectors through their three coordinates. -/
theorem space_ext {v w : Space} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) :
    v = w := by
  rw [← sub_eq_zero, space_eq_zero_iff]
  simp [h0, h1, h2]

/-- Coordinates of the Euclidean cross product. -/
theorem cross_coords (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧
    cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross, cross_apply]

/-! ### Sanity checks of the differential-operator conventions -/

/-- Sanity check: the identity operator (the field `B = x`) has divergence 3. -/
theorem divergence_id : divergence (ContinuousLinearMap.id ℝ Space) = 3 := by
  rw [divergence_apply]
  simp
  norm_num

/-- Sanity check: the identity operator (a gradient field) has zero curl. -/
theorem curl_id : curl (ContinuousLinearMap.id ℝ Space) = 0 := by
  obtain ⟨h0, h1, h2⟩ := curl_coords (ContinuousLinearMap.id ℝ Space)
  rw [space_eq_zero_iff]
  simp [h0, h1, h2]

/-- Sanity check: a rigid rotation field `B = ω × x` has zero divergence. -/
theorem divergence_rotation (ω : Space) : divergence (crossBilinear ω) = 0 := by
  rw [divergence_apply]
  simp only [crossBilinear_apply]
  obtain ⟨a0, -, -⟩ := cross_coords ω (basis 0)
  obtain ⟨-, a1, -⟩ := cross_coords ω (basis 1)
  obtain ⟨-, -, a2⟩ := cross_coords ω (basis 2)
  rw [a0, a1, a2]
  simp

/-- Sanity check: a rigid rotation field `B = ω × x` has curl `2ω`. -/
theorem curl_rotation (ω : Space) : curl (crossBilinear ω) = (2 : ℝ) • ω := by
  obtain ⟨h0, h1, h2⟩ := curl_coords (crossBilinear ω)
  simp only [crossBilinear_apply] at h0 h1 h2
  apply space_ext
  · rw [h0, (cross_coords _ _).2.2, (cross_coords _ _).2.1]
    simp; ring
  · rw [h1, (cross_coords _ _).1, (cross_coords _ _).2.2]
    simp; ring
  · rw [h2, (cross_coords _ _).1, (cross_coords _ _).2.1]
    simp; ring

/-! ### The kernel derivative is symmetric and trace free -/

/-- Derivative of the Euclidean norm at a nonzero vector: `v ↦ ⟪r, v⟫ / ‖r‖`. -/
theorem fderiv_norm_apply {r : Space} (hr : r ≠ 0) (v : Space) :
    fderiv ℝ (fun x : Space => ‖x‖) r v = ⟪r, v⟫ / ‖r‖ := by
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have h1 := (norm_differentiable hr).hasFDerivAt.pow 2
  have h2 := (hasStrictFDerivAt_norm_sq r).hasFDerivAt
  have h := congrArg (fun L => L v) (h1.unique h2)
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    nsmul_eq_mul] at h
  field_simp
  push_cast at h
  linarith

/-- Explicit action of the inverse-cube kernel derivative:
`M v = v/|r|³ - 3⟪r,v⟫ r/|r|⁵`. -/
theorem fderiv_inverseCube_apply {r : Space} (hr : r ≠ 0) (v : Space) :
    fderiv ℝ inverseCube r v = (‖r‖ ^ 3)⁻¹ • v - (3 * ⟪r, v⟫ / ‖r‖ ^ 5) • r := by
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  rw [(inverseCube_derivative hr).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    fderiv_norm_apply hr, sub_eq_add_neg, ← neg_smul]
  congr 2
  field_simp

/-- Sanity check: the kernel derivative is symmetric, `⟪M u, v⟫ = ⟪u, M v⟫`. -/
theorem fderiv_inverseCube_symm {r : Space} (hr : r ≠ 0) (u v : Space) :
    ⟪fderiv ℝ inverseCube r u, v⟫ = ⟪u, fderiv ℝ inverseCube r v⟫ := by
  simp only [fderiv_inverseCube_apply hr, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, real_inner_comm u r]
  ring

/-- Sanity check: the radial kernel is divergence free away from the origin. -/
theorem divergence_inverseCube {r : Space} (hr : r ≠ 0) :
    divergence (fderiv ℝ inverseCube r) = 0 := by
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hsq := EuclideanSpace.real_norm_sq_eq r
  rw [Fin.sum_univ_three] at hsq
  rw [divergence_apply]
  simp only [fderiv_inverseCube_apply hr, EuclideanSpace.inner_single_right]
  simp
  field_simp
  linear_combination 3 * hsq

/-- Pointwise divergence-free property of the Biot–Savart integrand: for any
source tangent `a`, the operator `v ↦ a × M v` has zero divergence. -/
theorem divergence_cross_inverseCube (a : Space) {r : Space} (hr : r ≠ 0) :
    divergence ((crossBilinear a).comp (fderiv ℝ inverseCube r)) = 0 := by
  rw [divergence_apply]
  simp only [ContinuousLinearMap.comp_apply, crossBilinear_apply, fderiv_inverseCube_apply hr,
    EuclideanSpace.inner_single_right]
  simp only [(cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2]
  simp
  ring

/-- Pointwise curl of the Biot–Savart integrand: `curl (v ↦ a × M v) = -M a`. -/
theorem curl_cross_inverseCube (a : Space) {r : Space} (hr : r ≠ 0) :
    curl ((crossBilinear a).comp (fderiv ℝ inverseCube r)) = -(fderiv ℝ inverseCube r a) := by
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hsq := EuclideanSpace.real_norm_sq_eq r
  rw [Fin.sum_univ_three] at hsq
  obtain ⟨h0, h1, h2⟩ := curl_coords ((crossBilinear a).comp (fderiv ℝ inverseCube r))
  have hin : ⟪r, a⟫ = r 0 * a 0 + r 1 * a 1 + r 2 * a 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]; ring
  refine space_ext ?_ ?_ ?_
  · simp only [h0, ContinuousLinearMap.comp_apply, crossBilinear_apply,
      fderiv_inverseCube_apply hr, EuclideanSpace.inner_single_right,
      (cross_coords _ _).2.1, (cross_coords _ _).2.2, hin]
    simp
    field_simp
    linear_combination (3 : ℝ) * a 0 * hsq
  · simp only [h1, ContinuousLinearMap.comp_apply, crossBilinear_apply,
      fderiv_inverseCube_apply hr, EuclideanSpace.inner_single_right, (cross_coords _ _).1,
      (cross_coords _ _).2.2, hin]
    simp
    field_simp
    linear_combination (3 : ℝ) * a 1 * hsq
  · simp only [h2, ContinuousLinearMap.comp_apply, crossBilinear_apply,
      fderiv_inverseCube_apply hr, EuclideanSpace.inner_single_right, (cross_coords _ _).1,
      (cross_coords _ _).2.1, hin]
    simp
    field_simp
    linear_combination (3 : ℝ) * a 2 * hsq

/-- Explicit pointwise form: the divergence of the filament integrand derivative vanishes. -/
theorem divergence_kernelDerivative (c : ℝ → Space) (t : ℝ) (x : Space) (sep : x - c t ≠ 0) :
    divergence (kernelDerivative c t x) = 0 :=
  divergence_cross_inverseCube _ sep

/-- Explicit pointwise form: the curl of the filament integrand derivative is
`-M c'(t)`, the derivative of `t ↦ inverseCube (x - c t)` along the source. -/
theorem curl_kernelDerivative (c : ℝ → Space) (t : ℝ) (x : Space) (sep : x - c t ≠ 0) :
    curl (kernelDerivative c t x) = fderiv ℝ inverseCube (x - c t) (-(deriv c t)) := by
  rw [map_neg]
  exact curl_cross_inverseCube _ sep

/-- Moving the source along the curve moves the radial kernel: the source-parameter
derivative of `inverseCube (x - c t)` is the curl of the integrand derivative. -/
theorem hasDerivAt_inverseCube_source (c : ℝ → Space) (t : ℝ) (x : Space)
    (hc : DifferentiableAt ℝ c t) (sep : x - c t ≠ 0) :
    HasDerivAt (fun s => inverseCube (x - c s)) (curl (kernelDerivative c t x)) t := by
  rw [curl_kernelDerivative c t x sep]
  have h := (inverseCube_derivative sep).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).sub hc.hasDerivAt)
  simpa [Function.comp_def] using h

/-! ### Source-free Maxwell identities for the filament field -/

/-- Compactness supplies uniform separation and speed bounds from pointwise
hypotheses on the closed parameter interval. -/
private theorem uniform_bounds (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ContinuousOn c (Set.uIcc a b)) (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) :
    ∃ d V : ℝ, 0 < d ∧ 0 ≤ V ∧ (∀ t ∈ Set.uIcc a b, d ≤ ‖x - c t‖) ∧
      (∀ t ∈ Set.uIcc a b, ‖deriv c t‖ ≤ V) := by
  have hK : IsCompact (Set.uIcc a b) := isCompact_uIcc
  obtain ⟨t₀, ht₀, hmin⟩ := hK.exists_isMinOn Set.nonempty_uIcc
    ((continuousOn_const.sub hc).norm)
  obtain ⟨V, hV⟩ := hK.exists_bound_of_continuousOn ht
  refine ⟨‖x - c t₀‖, max V 0, norm_pos_iff.mpr (sep t₀ ht₀), le_max_right _ _,
    fun t htm => hmin htm, fun t htm => (hV t htm).trans (le_max_left _ _)⟩

/-- **Gauss law for magnetism.** The filament field is divergence free at every
point off the source curve. Only continuity of the curve and its tangent on the
closed parameter interval is assumed; the curve need not be closed. -/
theorem filamentField_divergence (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ContinuousOn c (Set.uIcc a b)) (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) :
    divergence (fderiv ℝ (filamentField μ₀ I c a b) x) = 0 := by
  obtain ⟨d, V, hd, hV, hsep, hspeed⟩ := uniform_bounds c a b x hc ht sep
  rw [(filamentField_derivative μ₀ I c a b x hc ht hd hV hsep hspeed).fderiv, divergence,
    map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm _
      (kernelDerivative_continuousOn c x _ hc ht sep).intervalIntegrable]
  rw [intervalIntegral.integral_congr
    (f := fun t => divergenceCLM (kernelDerivative c t x)) (g := fun _ => (0 : ℝ))
    (fun t htm => divergence_kernelDerivative c t x (sep t htm))]
  simp

/-- **Ampère's law in vacuum.** The field of a CLOSED filament (`c a = c b`) is curl
free at every point off the source curve. Differentiability of the curve is
required at every point of the closed parameter interval, including the endpoints
(automatic for a smooth periodic parametrization). -/
theorem filamentField_curl (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ c t)
    (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) (closed : c a = c b) :
    curl (fderiv ℝ (filamentField μ₀ I c a b) x) = 0 := by
  have hcont : ContinuousOn c (Set.uIcc a b) :=
    fun t htm => (hc t htm).continuousAt.continuousWithinAt
  obtain ⟨d, V, hd, hV, hsep, hspeed⟩ := uniform_bounds c a b x hcont ht sep
  rw [(filamentField_derivative μ₀ I c a b x hcont ht hd hV hsep hspeed).fderiv, curl,
    map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm _
      (kernelDerivative_continuousOn c x _ hcont ht sep).intervalIntegrable]
  have hint : IntervalIntegrable (fun t => curlCLM (kernelDerivative c t x)) volume a b :=
    (curlCLM.continuous.comp_continuousOn
      (kernelDerivative_continuousOn c x _ hcont ht sep)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f' := fun t => curlCLM (kernelDerivative c t x))
    (fun t htm => hasDerivAt_inverseCube_source c t x (hc t htm) (sep t htm)) hint, closed]
  simp

/-- Both source-free Maxwell identities hold together for a closed filament. -/
theorem filamentField_vacuum_maxwell (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ c t)
    (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) (closed : c a = c b) :
    divergence (fderiv ℝ (filamentField μ₀ I c a b) x) = 0 ∧
      curl (fderiv ℝ (filamentField μ₀ I c a b) x) = 0 :=
  ⟨filamentField_divergence μ₀ I c a b x
      (fun t htm => (hc t htm).continuousAt.continuousWithinAt) ht sep,
    filamentField_curl μ₀ I c a b x hc ht sep closed⟩

/-- Sanity check: the curl of an open filament segment equals the endpoint term
`(μ₀ I / 4π) (K(x - c b) - K(x - c a))`; closure is exactly what removes it. -/
theorem filamentField_curl_open (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ c t)
    (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) :
    curl (fderiv ℝ (filamentField μ₀ I c a b) x) =
      (μ₀ * I / (4 * Real.pi)) • (inverseCube (x - c b) - inverseCube (x - c a)) := by
  have hcont : ContinuousOn c (Set.uIcc a b) :=
    fun t htm => (hc t htm).continuousAt.continuousWithinAt
  obtain ⟨d, V, hd, hV, hsep, hspeed⟩ := uniform_bounds c a b x hcont ht sep
  rw [(filamentField_derivative μ₀ I c a b x hcont ht hd hV hsep hspeed).fderiv, curl,
    map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm _
      (kernelDerivative_continuousOn c x _ hcont ht sep).intervalIntegrable]
  have hint : IntervalIntegrable (fun t => curlCLM (kernelDerivative c t x)) volume a b :=
    (curlCLM.continuous.comp_continuousOn
      (kernelDerivative_continuousOn c x _ hcont ht sep)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f' := fun t => curlCLM (kernelDerivative c t x))
    (fun t htm => hasDerivAt_inverseCube_source c t x (hc t htm) (sep t htm)) hint]

/-- Sanity check: with zero current the field derivative vanishes identically, so
both identities hold trivially; this is consistent with the general theorem. -/
theorem filamentField_zero_current_fderiv (μ₀ : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space) :
    fderiv ℝ (filamentField μ₀ 0 c a b) x = 0 := by
  have : filamentField μ₀ 0 c a b = fun _ => 0 := funext (filamentField_zero_current μ₀ c a b)
  rw [this]
  exact fderiv_const_apply 0

end PlasmaLean.Fields
