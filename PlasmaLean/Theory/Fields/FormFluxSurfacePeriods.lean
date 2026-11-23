/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormConvexRegion
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The de Rham classes of a flux surface: the poloidal and toroidal periods

The stellarator contract describes an invariant torus by a doubly `2π`-periodic map
`K (θ, φ) = cylPoint (R θ φ) φ (z θ φ)` (`Contract.FieldTorus`). This file studies the 1-form
`B♭` restricted to such a surface, as the pulled-back form on the parameter plane `ℝ²`,

  `β̃ (θ, φ) (δθ, δφ) = ⟪B (K (θ, φ)), DK (θ, φ) (δθ, δφ)⟫`   (`torusForm`),

and its two periods `P_θ (φ) = ∫_0^{2π} β̃ (θ, φ) (1, 0) dθ` (`poloidalPeriod`) and
`P_φ (θ) = ∫_0^{2π} β̃ (θ, φ) (0, 1) dφ` (`toroidalPeriod`).

Hypotheses. The surface data are `PeriodicC2Torus R z`: `R` and `z` are `C²` on the plane and
`2π`-periodic in both angles (a `FieldTorus` with `C²` profiles is one,
`FieldTorus.periodicC2Torus`; neither `R > 0` nor the flow clause is used). The field `B` is
`C¹` and curl-free on an open set `U` that contains the whole image of `K`.

Results.
* `fderiv_torusForm_symm`, `exists_torusPotential`: `β̃` is closed on the plane, hence exact
  there (Mathlib's Poincaré lemma on a convex set): there is `χ` with `dχ = β̃`.
* `poloidalPeriod_eq_of_curl_eq_zero`, `toroidalPeriod_eq_of_curl_eq_zero`: `P_θ` does not
  depend on `φ` and `P_φ` does not depend on `θ`.
* `torusPotential_add_θ`, `torusPotential_add_φ`: every potential is quasi-periodic,
  `χ (θ + 2π, φ) = χ (θ, φ) + P_θ` and `χ (θ, φ + 2π) = χ (θ, φ) + P_φ`.
* `exists_periodic_potential_of_curl_eq_zero` and `periods_eq_of_periodic_potential`: the
  class statement. `β̃ - (P_θ/2π) dθ - (P_φ/2π) dφ` is the differential of a doubly periodic
  function, and conversely if `β̃ = a dθ + b dφ + dg` with `g` doubly periodic then
  `P_θ = 2π a` and `P_φ = 2π b`. So the class of `B♭` on the surface is
  `(P_θ/2π) [dθ] + (P_φ/2π) [dφ]`.
* `periods_eq_zero_of_gradient`: a field that is a gradient along the surface has both periods
  zero.
* `poloidalPeriod_eq_poloidalCirculation`: `P_θ (φ₀)` is the contract's
  `poloidalCirculation B R z φ₀` (no hypothesis on `B`). Hence
  `poloidalCirculation_eq_of_curl_eq_zero` and its `FieldTorus`, `VacuumField` and
  `loopCurrent` forms: the circulation that the contract measures at one toroidal angle does
  not depend on that angle (audit finding AV-M9c).
* `VacuumField.poloidalPeriod_eq_zero_of_meridianHalfSpace`: the poloidal period vanishes for
  a field that is a vacuum field on a meridian half-space.

What is not proved. The surface is a parametrised torus, not an embedded submanifold: `K` need
not be injective or an immersion. All statements are on the parameter plane, the universal
cover of the torus; "exact on the torus" is expressed as "the differential of a doubly periodic
function on the plane". Embedded tori and the descent to the torus
`AddCircle (2π) × AddCircle (2π)` are in `Theory/Fields/FormFluxSurfaceEmbedded`; the class in
TauCeti's de Rham cohomology (`torusTimeForm`) is not written. The field must be curl-free on
an open set containing the image of the whole plane, not only near one loop.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open Real
open scoped RealInnerProductSpace

/-! ## The torus map and the pulled-back form -/

/-- The **torus map** `(θ, φ) ↦ cylPoint (R θ φ) φ (z θ φ)` of the contract, as a map on the
parameter plane. -/
noncomputable def torusMap (R z : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Space :=
  cylPoint (R p.1 p.2) p.2 (z p.1 p.2)

/-- The **pull-back of `B♭` to the parameter plane**:
`β̃ p v = ⟪B (K p), DK p v⟫` for the torus map `K`. -/
noncomputable def torusForm (B : Space → Space) (R z : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ :=
  (innerSL ℝ (B (torusMap R z p))).comp (fderiv ℝ (torusMap R z) p)

/-- The **poloidal period** `∫_0^{2π} β̃ (θ, φ) (1, 0) dθ`: the circulation of `B` around the
loop of constant toroidal parameter `φ`. -/
noncomputable def poloidalPeriod (B : Space → Space) (R z : ℝ → ℝ → ℝ) (φ : ℝ) : ℝ :=
  ∫ θ in 0..2 * π, torusForm B R z (θ, φ) (1, 0)

/-- The **toroidal period** `∫_0^{2π} β̃ (θ, φ) (0, 1) dφ`: the circulation of `B` around the
loop of constant poloidal parameter `θ`. -/
noncomputable def toroidalPeriod (B : Space → Space) (R z : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ φ in 0..2 * π, torusForm B R z (θ, φ) (0, 1)

/-- **A doubly periodic `C²` parametrised torus**: `R` and `z` are `C²` on the plane and
`2π`-periodic in each angle. Nothing is assumed about injectivity, the rank of the map, or the
sign of `R`. -/
structure PeriodicC2Torus (R z : ℝ → ℝ → ℝ) : Prop where
  /-- `R` is `C²`. -/
  contDiff_R : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2)
  /-- `z` is `C²`. -/
  contDiff_z : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2)
  /-- `R` is `2π`-periodic in `θ`. -/
  per_θ_R : ∀ θ φ, R (θ + 2 * π) φ = R θ φ
  /-- `z` is `2π`-periodic in `θ`. -/
  per_θ_z : ∀ θ φ, z (θ + 2 * π) φ = z θ φ
  /-- `R` is `2π`-periodic in `φ`. -/
  per_φ_R : ∀ θ φ, R θ (φ + 2 * π) = R θ φ
  /-- `z` is `2π`-periodic in `φ`. -/
  per_φ_z : ∀ θ φ, z θ (φ + 2 * π) = z θ φ

/-- A `FieldTorus` of the contract with `C²` profiles is a doubly periodic `C²` torus. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.periodicC2Torus {B : Space → Space}
    {R z : ℝ → ℝ → ℝ} {ι : ℝ} (hT : FieldTorus B R z ι)
    (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2)) : PeriodicC2Torus R z :=
  ⟨hR, hz, hT.per_θ_R, hT.per_θ_z, hT.per_φ_R, hT.per_φ_z⟩

section Basic

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ}

/-- The poloidal loop of the contract is the torus map on a line of constant `φ`. -/
theorem torusMap_eq_poloidalLoop (R z : ℝ → ℝ → ℝ) (θ φ : ℝ) :
    torusMap R z (θ, φ) = poloidalLoop R z φ θ := rfl

/-- The torus map of a `C²` torus is `C²`. -/
theorem PeriodicC2Torus.contDiff_torusMap (h : PeriodicC2Torus R z) :
    ContDiff ℝ 2 (torusMap R z) := by
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · simpa [torusMap, cylPoint] using h.contDiff_R.mul (contDiff_cos.comp contDiff_snd)
  · simpa [torusMap, cylPoint] using h.contDiff_R.mul (contDiff_sin.comp contDiff_snd)
  · simpa [torusMap, cylPoint] using h.contDiff_z

/-- The torus map is `2π`-periodic in `θ`. -/
theorem PeriodicC2Torus.torusMap_add_θ (h : PeriodicC2Torus R z) (p : ℝ × ℝ) :
    torusMap R z (p + (2 * π, 0)) = torusMap R z p := by
  simp [torusMap, h.per_θ_R, h.per_θ_z]

/-- The torus map is `2π`-periodic in `φ`. -/
theorem PeriodicC2Torus.torusMap_add_φ (h : PeriodicC2Torus R z) (p : ℝ × ℝ) :
    torusMap R z (p + (0, 2 * π)) = torusMap R z p := by
  simp [torusMap, cylPoint, h.per_φ_R, h.per_φ_z]

/-- The pulled-back form is `2π`-periodic in `θ`. -/
theorem PeriodicC2Torus.torusForm_add_θ (h : PeriodicC2Torus R z) (B : Space → Space)
    (p : ℝ × ℝ) : torusForm B R z (p + (2 * π, 0)) = torusForm B R z p := by
  have hf : (fun q => torusMap R z (q + (2 * π, 0))) = torusMap R z :=
    funext h.torusMap_add_θ
  rw [torusForm, torusForm, h.torusMap_add_θ, ← fderiv_comp_add_right, hf]

/-- The pulled-back form is `2π`-periodic in `φ`. -/
theorem PeriodicC2Torus.torusForm_add_φ (h : PeriodicC2Torus R z) (B : Space → Space)
    (p : ℝ × ℝ) : torusForm B R z (p + (0, 2 * π)) = torusForm B R z p := by
  have hf : (fun q => torusMap R z (q + (0, 2 * π))) = torusMap R z :=
    funext h.torusMap_add_φ
  rw [torusForm, torusForm, h.torusMap_add_φ, ← fderiv_comp_add_right, hf]

/-- The pulled-back form is continuous when `B` is continuous at the points of the surface. -/
theorem PeriodicC2Torus.continuous_torusForm (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p)) : Continuous (torusForm B R z) := by
  have hK := h.contDiff_torusMap
  refine continuous_iff_continuousAt.2 fun p => ?_
  have h1 : ContinuousAt (fun q => innerSL ℝ (B (torusMap R z q))) p :=
    (innerSL ℝ).continuous.continuousAt.comp ((hBc p).comp hK.continuous.continuousAt)
  have h2 : ContinuousAt (fderiv ℝ (torusMap R z)) p :=
    (hK.continuous_fderiv (by norm_num)).continuousAt
  exact h1.clm_comp h2

/-- The value of the pulled-back form on `∂_θ` is `⟪B, ∂_θ K⟫`. -/
theorem PeriodicC2Torus.torusForm_apply_θ (h : PeriodicC2Torus R z) (B : Space → Space)
    (θ φ : ℝ) : torusForm B R z (θ, φ) (1, 0) =
      ⟪B (torusMap R z (θ, φ)), deriv (fun t => torusMap R z (t, φ)) θ⟫ := by
  have hK : HasFDerivAt (torusMap R z) (fderiv ℝ (torusMap R z) (θ, φ)) (θ, φ) :=
    (h.contDiff_torusMap.differentiable (by norm_num) (θ, φ)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  have hc : HasDerivAt (fun t => torusMap R z (t, φ))
      (fderiv ℝ (torusMap R z) (θ, φ) (1, 0)) θ :=
    HasFDerivAt.comp_hasDerivAt (l := torusMap R z) θ hK h1
  rw [hc.deriv]
  rfl

/-- The value of the pulled-back form on `∂_φ` is `⟪B, ∂_φ K⟫`. -/
theorem PeriodicC2Torus.torusForm_apply_φ (h : PeriodicC2Torus R z) (B : Space → Space)
    (θ φ : ℝ) : torusForm B R z (θ, φ) (0, 1) =
      ⟪B (torusMap R z (θ, φ)), deriv (fun t => torusMap R z (θ, t)) φ⟫ := by
  have hK : HasFDerivAt (torusMap R z) (fderiv ℝ (torusMap R z) (θ, φ)) (θ, φ) :=
    (h.contDiff_torusMap.differentiable (by norm_num) (θ, φ)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (θ, t)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  have hc : HasDerivAt (fun t => torusMap R z (θ, t))
      (fderiv ℝ (torusMap R z) (θ, φ) (0, 1)) φ :=
    HasFDerivAt.comp_hasDerivAt (l := torusMap R z) φ hK h1
  rw [hc.deriv]
  rfl

/-! ## The link with the contract's poloidal circulation -/

/-- **The poloidal period is the contract's poloidal circulation**: the integral of the
pulled-back form over `θ ∈ [0, 2π]` at the toroidal parameter `φ₀` equals
`poloidalCirculation B R z φ₀`, which integrates over `[-π, π]`. No hypothesis on `B`. -/
theorem PeriodicC2Torus.poloidalPeriod_eq_poloidalCirculation (h : PeriodicC2Torus R z)
    (B : Space → Space) (φ₀ : ℝ) :
    poloidalPeriod B R z φ₀ = poloidalCirculation B R z φ₀ := by
  have hper : Function.Periodic (fun θ => torusForm B R z (θ, φ₀) (1, 0)) (2 * π) := fun θ => by
    have := h.torusForm_add_θ B (θ, φ₀)
    simp only [Prod.mk_add_mk, add_zero] at this
    simp only [this]
  have hs := hper.intervalIntegral_add_eq 0 (-π)
  have e1 : -π + 2 * π = π := by ring
  rw [zero_add, e1] at hs
  rw [poloidalPeriod, hs, poloidalCirculation, lineIntegral]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  exact h.torusForm_apply_θ B θ φ₀

end Basic

/-! ## Closedness of the pulled-back form -/

/-- A curl-free derivative operator is symmetric for the inner product:
`⟪L u, v⟫ = ⟪L v, u⟫`. -/
theorem inner_apply_symm_of_curlOp_eq_zero {L : Space →L[ℝ] Space} (hL : curlOp L = 0)
    (u v : Space) : ⟪L u, v⟫ = ⟪L v, u⟫ := by
  have hs := (curlOp_eq_zero_iff L).1 hL
  have key : ∀ w : Space,
      L w = w 0 • L (coordVec 0) + w 1 • L (coordVec 1) + w 2 • L (coordVec 2) := fun w => by
    have hw : w = w 0 • coordVec 0 + w 1 • coordVec 1 + w 2 • coordVec 2 := by
      ext i
      fin_cases i <;> simp [coordVec]
    conv_lhs => rw [hw]
    simp only [map_add, map_smul]
  rw [key u, key v]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, RCLike.inner_apply, conj_trivial]
  linear_combination (v 0 * u 1 - u 0 * v 1) * hs 0 1 + (v 0 * u 2 - u 0 * v 2) * hs 0 2
    + (v 1 * u 2 - u 1 * v 2) * hs 1 2

section Closed

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {U : Set Space}

/-- The pulled-back form is differentiable on the plane, for a `C²` torus and a field that is
`C¹` on an open set containing the surface. -/
theorem PeriodicC2Torus.differentiable_torusForm (h : PeriodicC2Torus R z) (hUo : IsOpen U)
    (hB : ContDiffOn ℝ 1 B U) (hU : ∀ p, torusMap R z p ∈ U) :
    Differentiable ℝ (torusForm B R z) := fun p => by
  have hK := h.contDiff_torusMap
  have hK1 : DifferentiableAt ℝ (torusMap R z) p := hK.differentiable (by norm_num) p
  have hBd : DifferentiableAt ℝ B (torusMap R z p) :=
    (hB.contDiffAt (hUo.mem_nhds (hU p))).differentiableAt one_ne_zero
  have hDK : DifferentiableAt ℝ (fderiv ℝ (torusMap R z)) p :=
    (hK.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p
  have h1 : DifferentiableAt ℝ (fun q => innerSL ℝ (B (torusMap R z q))) p :=
    (innerSL ℝ).differentiableAt.comp p (hBd.comp p hK1)
  exact h1.clm_comp hDK

/-- The derivative of the pulled-back form:
`Dβ̃ p x y = ⟪B (K p), D²K p x y⟫ + ⟪DB (K p) (DK p x), DK p y⟫`. -/
theorem PeriodicC2Torus.fderiv_torusForm_apply (h : PeriodicC2Torus R z) (hUo : IsOpen U)
    (hB : ContDiffOn ℝ 1 B U) (hU : ∀ p, torusMap R z p ∈ U) (p x y : ℝ × ℝ) :
    fderiv ℝ (torusForm B R z) p x y =
      ⟪B (torusMap R z p), fderiv ℝ (fderiv ℝ (torusMap R z)) p x y⟫ +
        ⟪fderiv ℝ B (torusMap R z p) (fderiv ℝ (torusMap R z) p x),
          fderiv ℝ (torusMap R z) p y⟫ := by
  have hK := h.contDiff_torusMap
  have hK1 : DifferentiableAt ℝ (torusMap R z) p := hK.differentiable (by norm_num) p
  have hBd : DifferentiableAt ℝ B (torusMap R z p) :=
    (hB.contDiffAt (hUo.mem_nhds (hU p))).differentiableAt one_ne_zero
  have hDK : DifferentiableAt ℝ (fderiv ℝ (torusMap R z)) p :=
    (hK.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p
  have h1 : HasFDerivAt (fun q => B (torusMap R z q))
      ((fderiv ℝ B (torusMap R z p)).comp (fderiv ℝ (torusMap R z) p)) p :=
    hBd.hasFDerivAt.comp p hK1.hasFDerivAt
  have h2 := hDK.hasFDerivAt.clm_apply (hasFDerivAt_const y p)
  have h3 := h1.inner ℝ h2
  have h4 : fderiv ℝ (torusForm B R z) p x y
      = fderiv ℝ (fun q => torusForm B R z q y) p x := by
    rw [fderiv_clm_apply (h.differentiable_torusForm hUo hB hU p) (differentiableAt_const y)]
    simp
  rw [h4]
  have h5 : (fun q => torusForm B R z q y)
      = fun q => ⟪B (torusMap R z q), fderiv ℝ (torusMap R z) q y⟫ := rfl
  rw [h5, h3.fderiv]
  simp [fderivInnerCLM_apply]

/-- **The pulled-back form is closed**: its derivative is symmetric, for a `C²` torus and a
field that is `C¹` and curl-free on an open set containing the surface. -/
theorem PeriodicC2Torus.fderiv_torusForm_symm (h : PeriodicC2Torus R z) (hUo : IsOpen U)
    (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (p x y : ℝ × ℝ) :
    fderiv ℝ (torusForm B R z) p x y = fderiv ℝ (torusForm B R z) p y x := by
  have hsymm : IsSymmSndFDerivAt ℝ (torusMap R z) p :=
    h.contDiff_torusMap.contDiffAt.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField])
  rw [h.fderiv_torusForm_apply hUo hB hU, h.fderiv_torusForm_apply hUo hB hU, hsymm.eq x y,
    inner_apply_symm_of_curlOp_eq_zero (hcurl _ (hU p))]

/-- **The pulled-back form is exact on the plane** (Poincaré lemma): there is a potential `χ`
with `dχ = β̃`, for a `C²` torus and a field that is `C¹` and curl-free on an open set
containing the surface. -/
theorem PeriodicC2Torus.exists_torusPotential (h : PeriodicC2Torus R z) (hUo : IsOpen U)
    (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) :
    ∃ χ : ℝ × ℝ → ℝ, ∀ p, HasFDerivAt χ (torusForm B R z p) p := by
  obtain ⟨χ, hχ⟩ := convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_univ
    (h.differentiable_torusForm hUo hB hU).differentiableOn
    (fun p _ x y => h.fderiv_torusForm_symm hUo hB hcurl hU p x y)
  exact ⟨χ, fun p => hχ p (Set.mem_univ p)⟩

end Closed

/-! ## Periods and potentials -/

section Potential

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {χ : ℝ × ℝ → ℝ}

/-- A potential of a translation-invariant form changes by a constant under the translation. -/
theorem potential_add_sub_const {ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ} (hχ : ∀ p, HasFDerivAt χ (ω p) p)
    {v : ℝ × ℝ} (hv : ∀ p, ω (p + v) = ω p) (p q : ℝ × ℝ) :
    χ (p + v) - χ p = χ (q + v) - χ q := by
  have hd : ∀ p, HasFDerivAt (fun p => χ (p + v) - χ p) (0 : ℝ × ℝ →L[ℝ] ℝ) p := fun p => by
    have h1 : HasFDerivAt (fun p => χ (p + v)) (ω (p + v)) p :=
      (hasFDerivAt_comp_add_right v).2 (hχ (p + v))
    have h2 := h1.sub (hχ p)
    rw [hv p, sub_self] at h2
    exact h2
  exact is_const_of_fderiv_eq_zero (fun p => (hd p).differentiableAt) (fun p => (hd p).fderiv)
    p q

/-- Along a line of constant `φ`, the integral of the form is the difference of the potential
(fundamental theorem of calculus). -/
theorem PeriodicC2Torus.integral_torusForm_θ (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (a b φ : ℝ) :
    ∫ θ in a..b, torusForm B R z (θ, φ) (1, 0) = χ (b, φ) - χ (a, φ) := by
  have hc : Continuous fun θ : ℝ => torusForm B R z (θ, φ) (1, 0) :=
    ((h.continuous_torusForm hBc).comp (by fun_prop : Continuous fun θ : ℝ => (θ, φ))).clm_apply
      continuous_const
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => χ (θ, φ))
    (fun θ _ => ?_) (hc.intervalIntegrable _ _)
  have h1 : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  exact (hχ (θ, φ)).comp_hasDerivAt θ h1

/-- Along a line of constant `θ`, the integral of the form is the difference of the potential
(fundamental theorem of calculus). -/
theorem PeriodicC2Torus.integral_torusForm_φ (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (a b θ : ℝ) :
    ∫ φ in a..b, torusForm B R z (θ, φ) (0, 1) = χ (θ, b) - χ (θ, a) := by
  have hc : Continuous fun φ : ℝ => torusForm B R z (θ, φ) (0, 1) :=
    ((h.continuous_torusForm hBc).comp (by fun_prop : Continuous fun φ : ℝ => (θ, φ))).clm_apply
      continuous_const
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun φ => χ (θ, φ))
    (fun φ _ => ?_) (hc.intervalIntegrable _ _)
  have h1 : HasDerivAt (fun t : ℝ => (θ, t)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  exact (hχ (θ, φ)).comp_hasDerivAt φ h1

/-- **Quasi-periodicity of the potential in `θ`**: `χ (θ + 2π, φ) = χ (θ, φ) + P_θ (φ₀)`, for
every `θ`, `φ` and every toroidal parameter `φ₀` at which the poloidal period is taken. -/
theorem PeriodicC2Torus.torusPotential_add_θ (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (θ φ φ₀ : ℝ) :
    χ (θ + 2 * π, φ) = χ (θ, φ) + poloidalPeriod B R z φ₀ := by
  have h1 := potential_add_sub_const hχ (h.torusForm_add_θ B) (θ, φ) (0, φ₀)
  have h2 := h.integral_torusForm_θ hBc hχ 0 (2 * π) φ₀
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h1
  rw [poloidalPeriod, h2]
  linarith

/-- **Quasi-periodicity of the potential in `φ`**: `χ (θ, φ + 2π) = χ (θ, φ) + P_φ (θ₀)`, for
every `θ`, `φ` and every poloidal parameter `θ₀` at which the toroidal period is taken. -/
theorem PeriodicC2Torus.torusPotential_add_φ (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (θ φ θ₀ : ℝ) :
    χ (θ, φ + 2 * π) = χ (θ, φ) + toroidalPeriod B R z θ₀ := by
  have h1 := potential_add_sub_const hχ (h.torusForm_add_φ B) (θ, φ) (θ₀, 0)
  have h2 := h.integral_torusForm_φ hBc hχ 0 (2 * π) θ₀
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h1
  rw [toroidalPeriod, h2]
  linarith

/-- If the pulled-back form has a potential, the poloidal period does not depend on `φ`. -/
theorem PeriodicC2Torus.poloidalPeriod_eq_of_potential (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (φ φ' : ℝ) :
    poloidalPeriod B R z φ = poloidalPeriod B R z φ' := by
  have h1 := h.torusPotential_add_θ hBc hχ 0 0 φ
  have h2 := h.torusPotential_add_θ hBc hχ 0 0 φ'
  linarith

/-- If the pulled-back form has a potential, the toroidal period does not depend on `θ`. -/
theorem PeriodicC2Torus.toroidalPeriod_eq_of_potential (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (θ θ' : ℝ) :
    toroidalPeriod B R z θ = toroidalPeriod B R z θ' := by
  have h1 := h.torusPotential_add_φ hBc hχ 0 0 θ
  have h2 := h.torusPotential_add_φ hBc hχ 0 0 θ'
  linarith

/-- **The class of the pulled-back form, from a potential.** With `P_θ`, `P_φ` the two periods
(taken at any `φ₀`, `θ₀`), the form `β̃ - (P_θ/2π) dθ - (P_φ/2π) dφ` is the differential of a
doubly `2π`-periodic function on the plane. -/
theorem PeriodicC2Torus.exists_periodic_potential (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p))
    (hχ : ∀ p, HasFDerivAt χ (torusForm B R z p) p) (θ₀ φ₀ : ℝ) :
    ∃ g : ℝ × ℝ → ℝ, (∀ p, g (p + (2 * π, 0)) = g p) ∧ (∀ p, g (p + (0, 2 * π)) = g p) ∧
      ∀ p, HasFDerivAt g (torusForm B R z p
        - (poloidalPeriod B R z φ₀ / (2 * π)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (toroidalPeriod B R z θ₀ / (2 * π)) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hπ : (2 * π) ≠ 0 := by positivity
  refine ⟨fun p => χ p - poloidalPeriod B R z φ₀ / (2 * π) * p.1
    - toroidalPeriod B R z θ₀ / (2 * π) * p.2, fun p => ?_, fun p => ?_, fun p => ?_⟩
  · have := h.torusPotential_add_θ hBc hχ p.1 p.2 φ₀
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    rw [show p + (2 * π, 0) = (p.1 + 2 * π, p.2) by ext <;> simp, this]
    field_simp
    ring
  · have := h.torusPotential_add_φ hBc hχ p.1 p.2 θ₀
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    rw [show p + (0, 2 * π) = (p.1, p.2 + 2 * π) by ext <;> simp, this]
    field_simp
    ring
  · exact ((hχ p).sub (hasFDerivAt_fst.const_mul _)).sub (hasFDerivAt_snd.const_mul _)

/-- **Uniqueness of the class.** If `β̃ = a dθ + b dφ + dg` on the plane with `g` doubly
`2π`-periodic, then the poloidal period is `2π a` (at every `φ`) and the toroidal period is
`2π b` (at every `θ`). In particular `a dθ + b dφ` is the differential of a doubly periodic
function only for `a = b = 0` (take `B = 0`). -/
theorem PeriodicC2Torus.periods_eq_of_periodic_potential (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p)) {a b : ℝ} {g : ℝ × ℝ → ℝ}
    (hgθ : ∀ p, g (p + (2 * π, 0)) = g p) (hgφ : ∀ p, g (p + (0, 2 * π)) = g p)
    (hg : ∀ p, HasFDerivAt g (torusForm B R z p - a • ContinuousLinearMap.fst ℝ ℝ ℝ
      - b • ContinuousLinearMap.snd ℝ ℝ ℝ) p) (θ φ : ℝ) :
    poloidalPeriod B R z φ = 2 * π * a ∧ toroidalPeriod B R z θ = 2 * π * b := by
  have hχ : ∀ p, HasFDerivAt (fun p : ℝ × ℝ => g p + a * p.1 + b * p.2) (torusForm B R z p) p :=
    fun p => by
      have := ((hg p).add (hasFDerivAt_fst.const_mul a)).add (hasFDerivAt_snd.const_mul b)
      convert this using 1
      abel
  have h1 := h.torusPotential_add_θ hBc hχ 0 φ φ
  have h2 := h.torusPotential_add_φ hBc hχ θ 0 θ
  have h3 := hgθ (0, φ)
  have h4 := hgφ (θ, 0)
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h1 h2 h3 h4
  rw [h3] at h1
  rw [h4] at h2
  constructor <;> linarith

/-- **A gradient has no periods.** If `B` is the gradient of a function `Φ` at every point of
the surface, both periods vanish. -/
theorem PeriodicC2Torus.periods_eq_zero_of_gradient (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p)) {Φ : Space → ℝ}
    (hΦ : ∀ p, HasFDerivAt Φ (innerSL ℝ (B (torusMap R z p))) (torusMap R z p)) (θ φ : ℝ) :
    poloidalPeriod B R z φ = 0 ∧ toroidalPeriod B R z θ = 0 := by
  have hχ : ∀ p, HasFDerivAt (fun p => Φ (torusMap R z p)) (torusForm B R z p) p := fun p =>
    (hΦ p).comp p (h.contDiff_torusMap.differentiable (by norm_num) p).hasFDerivAt
  have h1 := h.torusPotential_add_θ hBc hχ 0 φ φ
  have h2 := h.torusPotential_add_φ hBc hχ θ 0 θ
  have h3 := h.torusMap_add_θ (0, φ)
  have h4 := h.torusMap_add_φ (θ, 0)
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h1 h2 h3 h4
  rw [h3] at h1
  rw [h4] at h2
  constructor <;> linarith

end Potential

/-! ## Curl-free fields: the periods are constants of the surface -/

section CurlFree

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {U : Set Space}

/-- A field that is `C¹` on an open set containing the surface is continuous at its points. -/
theorem continuousAt_of_contDiffOn_torus (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U)
    (hU : ∀ p, torusMap R z p ∈ U) (p : ℝ × ℝ) : ContinuousAt B (torusMap R z p) :=
  hB.continuousOn.continuousAt (hUo.mem_nhds (hU p))

/-- **The poloidal period does not depend on the toroidal parameter**, for a `C²` doubly
periodic torus and a field that is `C¹` and curl-free on an open set containing the surface. -/
theorem PeriodicC2Torus.poloidalPeriod_eq_of_curl_eq_zero (h : PeriodicC2Torus R z)
    (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (φ φ' : ℝ) :
    poloidalPeriod B R z φ = poloidalPeriod B R z φ' := by
  obtain ⟨χ, hχ⟩ := h.exists_torusPotential hUo hB hcurl hU
  exact h.poloidalPeriod_eq_of_potential (continuousAt_of_contDiffOn_torus hUo hB hU) hχ φ φ'

/-- **The toroidal period does not depend on the poloidal parameter**, for a `C²` doubly
periodic torus and a field that is `C¹` and curl-free on an open set containing the surface. -/
theorem PeriodicC2Torus.toroidalPeriod_eq_of_curl_eq_zero (h : PeriodicC2Torus R z)
    (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (θ θ' : ℝ) :
    toroidalPeriod B R z θ = toroidalPeriod B R z θ' := by
  obtain ⟨χ, hχ⟩ := h.exists_torusPotential hUo hB hcurl hU
  exact h.toroidalPeriod_eq_of_potential (continuousAt_of_contDiffOn_torus hUo hB hU) hχ θ θ'

/-- **The de Rham class of `B♭` on the flux surface, on the cover.** For a `C²` doubly periodic
torus and a field that is `C¹` and curl-free on an open set containing the surface, the form
`β̃ - (P_θ/2π) dθ - (P_φ/2π) dφ` is the differential of a doubly `2π`-periodic function on the
plane. The periods may be taken at any `φ₀`, `θ₀`. -/
theorem PeriodicC2Torus.exists_periodic_potential_of_curl_eq_zero (h : PeriodicC2Torus R z)
    (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (θ₀ φ₀ : ℝ) :
    ∃ g : ℝ × ℝ → ℝ, (∀ p, g (p + (2 * π, 0)) = g p) ∧ (∀ p, g (p + (0, 2 * π)) = g p) ∧
      ∀ p, HasFDerivAt g (torusForm B R z p
        - (poloidalPeriod B R z φ₀ / (2 * π)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (toroidalPeriod B R z θ₀ / (2 * π)) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  obtain ⟨χ, hχ⟩ := h.exists_torusPotential hUo hB hcurl hU
  exact h.exists_periodic_potential (continuousAt_of_contDiffOn_torus hUo hB hU) hχ θ₀ φ₀

/-- **The poloidal circulation of the contract does not depend on the toroidal angle.** For a
`C²` doubly periodic torus and a field that is `C¹` and curl-free on an open set containing the
surface, `poloidalCirculation B R z φ₀ = poloidalCirculation B R z φ₁` for all `φ₀`, `φ₁`. -/
theorem PeriodicC2Torus.poloidalCirculation_eq_of_curl_eq_zero (h : PeriodicC2Torus R z)
    (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (φ₀ φ₁ : ℝ) :
    poloidalCirculation B R z φ₀ = poloidalCirculation B R z φ₁ := by
  rw [← h.poloidalPeriod_eq_poloidalCirculation, ← h.poloidalPeriod_eq_poloidalCirculation]
  exact h.poloidalPeriod_eq_of_curl_eq_zero hUo hB hcurl hU φ₀ φ₁

/-- **The loop current of the contract does not depend on the toroidal angle**, under the
hypotheses of `PeriodicC2Torus.poloidalCirculation_eq_of_curl_eq_zero`. -/
theorem PeriodicC2Torus.loopCurrent_eq_of_curl_eq_zero (h : PeriodicC2Torus R z)
    (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (μ₀ φ₀ φ₁ : ℝ) :
    loopCurrent μ₀ B R z φ₀ = loopCurrent μ₀ B R z φ₁ := by
  rw [loopCurrent, loopCurrent, h.poloidalCirculation_eq_of_curl_eq_zero hUo hB hcurl hU φ₀ φ₁]

/-- **Contract corollary (audit AV-M9c).** For a `FieldTorus` with `C²` profiles, in an open
region containing the torus on which `B` is `C¹` and curl-free, the poloidal circulation
`poloidalCirculation B R z φ₀` is the same at every toroidal angle `φ₀`. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.poloidalCirculation_eq_of_curl_eq_zero {ι : ℝ}
    (hT : FieldTorus B R z ι) (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2)) (hUo : IsOpen U)
    (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ θ φ, cylPoint (R θ φ) φ (z θ φ) ∈ U) (φ₀ φ₁ : ℝ) :
    poloidalCirculation B R z φ₀ = poloidalCirculation B R z φ₁ :=
  (hT.periodicC2Torus hR hz).poloidalCirculation_eq_of_curl_eq_zero hUo hB hcurl
    (fun p => hU p.1 p.2) φ₀ φ₁

/-- **Contract corollary: the net current of a `FieldTorus` is the same at every toroidal
angle**, in an open region containing the torus on which `B` is `C¹` and curl-free. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.loopCurrent_eq_of_curl_eq_zero {ι : ℝ}
    (hT : FieldTorus B R z ι) (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2)) (hUo : IsOpen U)
    (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ θ φ, cylPoint (R θ φ) φ (z θ φ) ∈ U) (μ₀ φ₀ φ₁ : ℝ) :
    loopCurrent μ₀ B R z φ₀ = loopCurrent μ₀ B R z φ₁ :=
  (hT.periodicC2Torus hR hz).loopCurrent_eq_of_curl_eq_zero hUo hB hcurl
    (fun p => hU p.1 p.2) μ₀ φ₀ φ₁

/-- **A vacuum field has a poloidal circulation that does not depend on the toroidal angle**,
on a `C²` doubly periodic torus contained in the vacuum region. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.poloidalCirculation_eq (hv : VacuumField U B)
    (h : PeriodicC2Torus R z) (hU : ∀ p, torusMap R z p ∈ U) (φ₀ φ₁ : ℝ) :
    poloidalCirculation B R z φ₀ = poloidalCirculation B R z φ₁ :=
  h.poloidalCirculation_eq_of_curl_eq_zero hv.isOpen (hv.contDiffOn.of_le (by norm_num))
    hv.curl_eq_zero hU φ₀ φ₁

/-- **The poloidal period vanishes for a field that is a vacuum field on a meridian
half-space.** Let `B` be a vacuum field on a region `U` that contains a `C²` doubly periodic
torus and the whole meridian half-space of one toroidal angle `φ₀`, at which `R > 0`. Then the
poloidal period is `0` at every toroidal parameter `φ`: only the toroidal period can carry a
current. (The hypothesis on the half-space excludes coil fields; see
`VacuumField.loopCurrent_eq_zero_of_meridianHalfSpace`.) -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.poloidalPeriod_eq_zero_of_meridianHalfSpace
    (hv : VacuumField U B) (h : PeriodicC2Torus R z) (hU : ∀ p, torusMap R z p ∈ U) {φ₀ : ℝ}
    (hΩ : (meridianHalfSpace φ₀ : Set Space) ⊆ U) (hR : ∀ θ, 0 < R θ φ₀) (φ : ℝ) :
    poloidalPeriod B R z φ = 0 := by
  rw [h.poloidalPeriod_eq_of_curl_eq_zero hv.isOpen (hv.contDiffOn.of_le (by norm_num))
    hv.curl_eq_zero hU φ φ₀, h.poloidalPeriod_eq_poloidalCirculation]
  have hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀) :=
    (h.contDiff_torusMap.of_le (by norm_num)).comp
      (by fun_prop : ContDiff ℝ 1 fun θ : ℝ => (θ, φ₀))
  have hclosed : poloidalLoop R z φ₀ (-π) = poloidalLoop R z φ₀ π := by
    have := h.torusMap_add_θ (-π, φ₀)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [show -π + 2 * π = π by ring] at this
    exact this.symm
  exact (hv.restrict_meridianHalfSpace hΩ).poloidalCirculation_eq_zero_of_convex
    (convex_meridianHalfSpace φ₀) (fun θ _ => poloidalLoop_mem_meridianHalfSpace (hR θ))
    hγ.contDiffOn hclosed

end CurlFree

end PlasmaLean.Forms
