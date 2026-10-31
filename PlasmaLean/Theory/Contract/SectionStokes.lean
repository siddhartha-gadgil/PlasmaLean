/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Stokes' theorem for regular coordinate sections

Clause C1 (`Theory/Contract/StellaratorContract`) measures the net toroidal current by Ampère's
law, as the circulation `μ₀⁻¹ ∮ B · dl` around the poloidal loop (`loopCurrent`). The auxiliary
section flux `netToroidalCurrent μ₀ B X ζ₀ k₀` (flux of `J = (∇ × B)/μ₀` through the section
`ζ = ζ₀`, `0 ≤ k ≤ k₀`, `-π ≤ χ ≤ π` of a coordinate map `X`) agrees with it for **regular**
sections. This module proves that (Stokes' theorem on the parameter rectangle).

* `netToroidalCurrent_eq_lineIntegral_div`: if `X` is `C²` and `B` is `C¹` at every point of the
  closed section, the seams match (`X(k, π, ζ₀) = X(k, −π, ζ₀)` for all `k`) and the inner edge
  `k = 0` is a single point, then
  `netToroidalCurrent μ₀ B X ζ₀ k₀ = μ₀⁻¹ ∫_{-π}^{π} ⟪B(γ χ), γ'(χ)⟫ dχ` with
  `γ χ = X(k₀, χ, ζ₀)` the outer edge.
* `netToroidalCurrent_eq_loopCurrent`: the same with the outer edge equal to the poloidal loop of
  a torus, so the section flux is the C1 quantity `loopCurrent`.

Proof: the pulled-back one-form `a_k = ⟪B ∘ X, ∂_k X⟫`, `a_χ = ⟪B ∘ X, ∂_χ X⟫` satisfies
`∂_k a_χ − ∂_χ a_k = (∇ × B) · (∂_k X × ∂_χ X)` (`inner_sub_inner_eq_tripleFlux`, symmetry of the
second derivative of `X`), and the divergence theorem on the rectangle
(`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`) turns its integral into the boundary
terms; the two seams cancel, the inner edge contributes `0` and the outer edge is the
circulation.

The pinched section of `Sanity/AuditRefreshContract` violates the seam condition, which is why
its zero flux says nothing about the circulation.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Contract

open Real Set MeasureTheory WithLp PlasmaLean.Fields

/-! ## Algebra -/

/-- The flux density in coordinates. -/
theorem tripleFlux_eq (V a b : Space) : tripleFlux V a b =
    V 0 * (a 1 * b 2 - a 2 * b 1) + V 1 * (a 2 * b 0 - a 0 * b 2) +
      V 2 * (a 0 * b 1 - a 1 * b 0) := by
  simp [tripleFlux, cross_apply, dotProduct, Fin.sum_univ_three]

/-- The flux density is linear in the vector. -/
theorem tripleFlux_smul (c : ℝ) (V a b : Space) :
    tripleFlux (c • V) a b = c * tripleFlux V a b := by
  rw [tripleFlux_eq, tripleFlux_eq]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The inner product in coordinates. -/
theorem inner_coords3 (v w : Space) : ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- A vector is the sum of its coordinates times the basis vectors. -/
theorem eq_sum_basis (a : Space) : a = a 0 • basis 0 + a 1 • basis 1 + a 2 • basis 2 := by
  ext i
  fin_cases i <;> simp [basis]

/-- **Antisymmetric part of a derivative is the curl**: `⟪L a, b⟫ − ⟪L b, a⟫ = curl L · (a × b)`. -/
theorem inner_sub_inner_eq_tripleFlux (L : Space →L[ℝ] Space) (a b : Space) :
    ⟪L a, b⟫ - ⟪L b, a⟫ = tripleFlux (curl L) a b := by
  have hLa : L a = a 0 • L (basis 0) + a 1 • L (basis 1) + a 2 • L (basis 2) := by
    conv_lhs => rw [eq_sum_basis a]
    simp only [map_add, map_smul]
  have hLb : L b = b 0 • L (basis 0) + b 1 • L (basis 1) + b 2 • L (basis 2) := by
    conv_lhs => rw [eq_sum_basis b]
    simp only [map_add, map_smul]
  obtain ⟨h0, h1, h2⟩ := curl_coords L
  rw [hLa, hLb, inner_coords3, inner_coords3, tripleFlux_eq, h0, h1, h2]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ## The plane `ζ = ζ₀` and partial derivatives -/

/-- The plane `ζ = ζ₀` of coordinate space, `(k, χ) ↦ (k, χ, ζ₀)`. -/
@[expose] def planeMap (ζ₀ : ℝ) (p : ℝ × ℝ) : Space := coordPt p.1 p.2 ζ₀

/-- The derivative of `planeMap`, `(a, b) ↦ a e₀ + b e₁`. -/
@[expose] def planeDeriv : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (basis 0) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (basis 1)

/-- `planeDeriv (1, 0) = e₀`. -/
@[simp] theorem planeDeriv_one_zero : planeDeriv (1, 0) = basis 0 := by simp [planeDeriv]

/-- `planeDeriv (0, 1) = e₁`. -/
@[simp] theorem planeDeriv_zero_one : planeDeriv (0, 1) = basis 1 := by simp [planeDeriv]

/-- The derivative of the plane map. -/
theorem hasFDerivAt_planeMap (ζ₀ : ℝ) (p : ℝ × ℝ) : HasFDerivAt (planeMap ζ₀) planeDeriv p := by
  have h : planeMap ζ₀ = fun q => planeDeriv q + coordPt 0 0 ζ₀ := by
    funext q
    ext i
    fin_cases i <;> simp [planeMap, planeDeriv, coordPt, basis]
  rw [h]
  exact planeDeriv.hasFDerivAt.add_const _

/-- The plane map is continuous. -/
theorem continuous_planeMap (ζ₀ : ℝ) : Continuous (planeMap ζ₀) :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_planeMap ζ₀ p).continuousAt

/-- The `k`-partial derivative: `DX(k, χ, ζ) e₀ = ∂_k X(k, χ, ζ)`. -/
theorem fderiv_basis0 {X : Space → Space} {k χ ζ : ℝ}
    (hX : DifferentiableAt ℝ X (coordPt k χ ζ)) :
    fderiv ℝ X (coordPt k χ ζ) (basis 0) = deriv (fun t => X (coordPt t χ ζ)) k := by
  have hc : HasDerivAt (fun t => coordPt t χ ζ) (basis 0) k := by
    have h := hasDerivAt_space3 (hasDerivAt_id' k) (hasDerivAt_const k χ) (hasDerivAt_const k ζ)
    have hb : basis 0 = (toLp 2 ![1, 0, 0] : Space) := by
      ext i; fin_cases i <;> simp [basis]
    rw [hb]
    exact h
  exact (hX.hasFDerivAt.comp_hasDerivAt k hc).deriv.symm

/-- The `χ`-partial derivative: `DX(k, χ, ζ) e₁ = ∂_χ X(k, χ, ζ)`. -/
theorem fderiv_basis1 {X : Space → Space} {k χ ζ : ℝ}
    (hX : DifferentiableAt ℝ X (coordPt k χ ζ)) :
    fderiv ℝ X (coordPt k χ ζ) (basis 1) = deriv (fun t => X (coordPt k t ζ)) χ := by
  have hc : HasDerivAt (fun t => coordPt k t ζ) (basis 1) χ := by
    have h := hasDerivAt_space3 (hasDerivAt_const χ k) (hasDerivAt_id' χ) (hasDerivAt_const χ ζ)
    have hb : basis 1 = (toLp 2 ![0, 1, 0] : Space) := by
      ext i; fin_cases i <;> simp [basis]
    rw [hb]
    exact h
  exact (hX.hasFDerivAt.comp_hasDerivAt χ hc).deriv.symm

/-! ## The pulled-back one-form -/

/-- A component `q ↦ ⟪B(X(q, ζ₀)), DX(q, ζ₀) w⟫` of the pull-back of `B♭` to the plane. -/
@[expose] def pullComp (B X : Space → Space) (ζ₀ : ℝ) (w : Space) (q : ℝ × ℝ) : ℝ :=
  ⟪B (X (planeMap ζ₀ q)), fderiv ℝ X (planeMap ζ₀ q) w⟫

/-- Derivative of a component of the pulled-back one-form. -/
theorem hasFDerivAt_pullComp {B X : Space → Space} {ζ₀ : ℝ} (w : Space) {p : ℝ × ℝ}
    (hX : ContDiffAt ℝ 2 X (planeMap ζ₀ p)) (hB : DifferentiableAt ℝ B (X (planeMap ζ₀ p))) :
    HasFDerivAt (pullComp B X ζ₀ w) (fderiv ℝ (pullComp B X ζ₀ w) p) p ∧
      ∀ v, fderiv ℝ (pullComp B X ζ₀ w) p v =
        ⟪fderiv ℝ B (X (planeMap ζ₀ p)) (fderiv ℝ X (planeMap ζ₀ p) (planeDeriv v)),
          fderiv ℝ X (planeMap ζ₀ p) w⟫ +
        ⟪B (X (planeMap ζ₀ p)),
          fderiv ℝ (fderiv ℝ X) (planeMap ζ₀ p) (planeDeriv v) w⟫ := by
  have hc := hasFDerivAt_planeMap ζ₀ p
  have hXd : DifferentiableAt ℝ X (planeMap ζ₀ p) := hX.differentiableAt (by norm_num)
  have hDd : DifferentiableAt ℝ (fderiv ℝ X) (planeMap ζ₀ p) :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := hB.hasFDerivAt.comp p (hXd.hasFDerivAt.comp p hc)
  have h2 := (hDd.hasFDerivAt.comp p hc).clm_apply (hasFDerivAt_const w p)
  have h := h1.inner ℝ h2
  refine ⟨h.differentiableAt.hasFDerivAt, fun v => ?_⟩
  rw [show pullComp B X ζ₀ w = fun q => ⟪(B ∘ X ∘ planeMap ζ₀) q,
    ((fderiv ℝ X ∘ planeMap ζ₀) q) w⟫ from rfl, h.fderiv]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.flip_apply,
    fderivInnerCLM_apply]
  exact add_comm _ _

/-! ## Stokes' theorem -/

section Stokes
variable {μ₀ : ℝ} {B X : Space → Space} {ζ₀ k₀ : ℝ}

/-- The integrand `(∇ × B) · (∂_k X × ∂_χ X)` on the plane. -/
@[expose] def curlFlux (B X : Space → Space) (ζ₀ : ℝ) (q : ℝ × ℝ) : ℝ :=
  tripleFlux (curl (fderiv ℝ B (X (planeMap ζ₀ q))))
    (fderiv ℝ X (planeMap ζ₀ q) (basis 0)) (fderiv ℝ X (planeMap ζ₀ q) (basis 1))

/-- The divergence of the pulled-back one-form is the curl flux. -/
theorem div_pullComp_eq {p : ℝ × ℝ} (hX : ContDiffAt ℝ 2 X (planeMap ζ₀ p))
    (hB : DifferentiableAt ℝ B (X (planeMap ζ₀ p))) :
    fderiv ℝ (pullComp B X ζ₀ (basis 1)) p (1, 0) +
        (-fderiv ℝ (pullComp B X ζ₀ (basis 0)) p) (0, 1) = curlFlux B X ζ₀ p := by
  rw [(hasFDerivAt_pullComp (basis 1) hX hB).2, neg_apply,
    (hasFDerivAt_pullComp (basis 0) hX hB).2, planeDeriv_one_zero, planeDeriv_zero_one,
    curlFlux, ← inner_sub_inner_eq_tripleFlux,
    (hX.isSymmSndFDerivAt (by simp)).eq (basis 0) (basis 1)]
  ring

/-- The curl flux is continuous where `X` is `C²` and `B` is `C¹`. -/
theorem continuousAt_curlFlux {p : ℝ × ℝ} (hX : ContDiffAt ℝ 2 X (planeMap ζ₀ p))
    (hB : ContDiffAt ℝ 1 B (X (planeMap ζ₀ p))) : ContinuousAt (curlFlux B X ζ₀) p := by
  have hc : ContinuousAt (planeMap ζ₀) p := (continuous_planeMap ζ₀).continuousAt
  have hXc : ContinuousAt (fun q => X (planeMap ζ₀ q)) p :=
    (hX.differentiableAt (by norm_num)).continuousAt.comp hc
  have hD : ContinuousAt (fun q => fderiv ℝ X (planeMap ζ₀ q)) p :=
    (hX.continuousAt_fderiv (by norm_num)).comp hc
  have hDB : ContinuousAt (fun q => fderiv ℝ B (X (planeMap ζ₀ q))) p :=
    ContinuousAt.comp (g := fderiv ℝ B) (hB.continuousAt_fderiv (by norm_num)) hXc
  have hcurl : ContinuousAt (fun q => curl (fderiv ℝ B (X (planeMap ζ₀ q)))) p :=
    curlCLM.continuous.continuousAt.comp hDB
  have hcoord : ∀ (F : ℝ × ℝ → Space), ContinuousAt F p → ∀ i : Fin 3,
      ContinuousAt (fun q => F q i) p := fun F hF i =>
    ((PiLp.continuous_apply 2 _ i).continuousAt).comp hF
  have ha : ContinuousAt (fun q => fderiv ℝ X (planeMap ζ₀ q) (basis 0)) p :=
    hD.clm_apply continuousAt_const
  have hb : ContinuousAt (fun q => fderiv ℝ X (planeMap ζ₀ q) (basis 1)) p :=
    hD.clm_apply continuousAt_const
  have e : curlFlux B X ζ₀ = fun q => tripleFlux (curl (fderiv ℝ B (X (planeMap ζ₀ q))))
      (fderiv ℝ X (planeMap ζ₀ q) (basis 0)) (fderiv ℝ X (planeMap ζ₀ q) (basis 1)) := rfl
  rw [e]
  simp only [tripleFlux_eq]
  have := hcoord _ hcurl
  have := hcoord _ ha
  have := hcoord _ hb
  fun_prop

/-- **Stokes' theorem for a regular section.** Let the section `ζ = ζ₀`, `0 ≤ k ≤ k₀`,
`-π ≤ χ ≤ π` of `X` be regular: `X` is `C²` and `B` is `C¹` at every point of it, the seams
`χ = ±π` match for every `k`, and the inner edge `k = 0` is a single point. Then the section
flux of the Ampère current equals `μ₀⁻¹` times the circulation of `B` around the outer edge
`γ χ = X(k₀, χ, ζ₀)`. -/
theorem netToroidalCurrent_eq_lineIntegral_div (hk₀ : 0 ≤ k₀)
    (hX : ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, ContDiffAt ℝ 2 X (coordPt k χ ζ₀))
    (hB : ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, ContDiffAt ℝ 1 B (X (coordPt k χ ζ₀)))
    (hseam : ∀ k, X (coordPt k π ζ₀) = X (coordPt k (-π) ζ₀))
    (haxis : ∀ χ, X (coordPt 0 χ ζ₀) = X (coordPt 0 0 ζ₀)) :
    netToroidalCurrent μ₀ B X ζ₀ k₀ =
      lineIntegral B (fun χ => X (coordPt k₀ χ ζ₀)) (-π) π / μ₀ := by
  have hpi : -π ≤ π := by linarith [pi_pos]
  set Rect := uIcc 0 k₀ ×ˢ uIcc (-π) π with hRect
  have hmem : ∀ q ∈ Rect, q.1 ∈ Icc 0 k₀ ∧ q.2 ∈ Icc (-π) π := fun q hq => by
    rw [hRect, uIcc_of_le hk₀, uIcc_of_le hpi] at hq
    exact hq
  have hXq : ∀ q ∈ Rect, ContDiffAt ℝ 2 X (planeMap ζ₀ q) := fun q hq =>
    hX _ (hmem q hq).1 _ (hmem q hq).2
  have hBq : ∀ q ∈ Rect, ContDiffAt ℝ 1 B (X (planeMap ζ₀ q)) := fun q hq =>
    hB _ (hmem q hq).1 _ (hmem q hq).2
  have hBd : ∀ q ∈ Rect, DifferentiableAt ℝ B (X (planeMap ζ₀ q)) := fun q hq =>
    (hBq q hq).differentiableAt (by norm_num)
  have hint : ∀ q ∈ Ioo (min 0 k₀) (max 0 k₀) ×ˢ Ioo (min (-π) π) (max (-π) π), q ∈ Rect :=
    fun q hq => ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩
  -- the divergence theorem
  have hdiv := integral2_divergence_prod_of_hasFDerivAt (pullComp B X ζ₀ (basis 1))
    (fun q => -pullComp B X ζ₀ (basis 0) q) (fun q => fderiv ℝ (pullComp B X ζ₀ (basis 1)) q)
    (fun q => -fderiv ℝ (pullComp B X ζ₀ (basis 0)) q) 0 (-π) k₀ π
    (fun q hq => ((hasFDerivAt_pullComp _ (hXq q hq) (hBd q hq)).1.continuousAt).continuousWithinAt)
    (fun q hq =>
      ((hasFDerivAt_pullComp _ (hXq q hq) (hBd q hq)).1.continuousAt.neg).continuousWithinAt)
    (fun q hq => (hasFDerivAt_pullComp _ (hXq q (hint q hq)) (hBd q (hint q hq))).1)
    (fun q hq => (hasFDerivAt_pullComp _ (hXq q (hint q hq)) (hBd q (hint q hq))).1.neg)
    (by
      refine IntegrableOn.congr_fun (f := curlFlux B X ζ₀) ?_ (fun q hq =>
        (div_pullComp_eq (hXq q hq) (hBd q hq)).symm) (measurableSet_uIcc.prod measurableSet_uIcc)
      exact ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
        fun q hq => (continuousAt_curlFlux (hXq q hq) (hBq q hq)).continuousWithinAt)
  -- the interior integrand is the curl flux
  have hL : (∫ k in (0 : ℝ)..k₀, ∫ χ in (-π)..π,
      fderiv ℝ (pullComp B X ζ₀ (basis 1)) (k, χ) (1, 0) +
        (-fderiv ℝ (pullComp B X ζ₀ (basis 0)) (k, χ)) (0, 1)) =
      ∫ k in (0 : ℝ)..k₀, ∫ χ in (-π)..π, curlFlux B X ζ₀ (k, χ) := by
    refine intervalIntegral.integral_congr fun k hk => ?_
    refine intervalIntegral.integral_congr fun χ hχ => ?_
    exact div_pullComp_eq (hXq (k, χ) ⟨hk, hχ⟩) (hBd (k, χ) ⟨hk, hχ⟩)
  -- the seams cancel
  have hS : (∫ k in (0 : ℝ)..k₀, -pullComp B X ζ₀ (basis 0) (k, π)) =
      ∫ k in (0 : ℝ)..k₀, -pullComp B X ζ₀ (basis 0) (k, -π) := by
    refine intervalIntegral.integral_congr fun k hk => ?_
    have hk' := (hmem (k, π) ⟨hk, by rw [uIcc_of_le hpi]; exact ⟨hpi, le_rfl⟩⟩).1
    have d1 := (hX k hk' π ⟨hpi, le_rfl⟩).differentiableAt (by norm_num)
    have d2 := (hX k hk' (-π) ⟨le_rfl, hpi⟩).differentiableAt (by norm_num)
    simp only [pullComp, planeMap]
    rw [fderiv_basis0 d1, fderiv_basis0 d2, hseam k]
    congr 3
    funext t
    exact hseam t
  -- the inner edge contributes nothing
  have hA : (∫ χ in (-π)..π, pullComp B X ζ₀ (basis 1) (0, χ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun χ hχ => ?_]
    · simp
    rw [uIcc_of_le hpi] at hχ
    have d := (hX 0 ⟨le_rfl, hk₀⟩ χ hχ).differentiableAt (by norm_num)
    simp only [pullComp, planeMap]
    rw [fderiv_basis1 d, show (fun t => X (coordPt 0 t ζ₀)) = fun _ => X (coordPt 0 0 ζ₀) from
      funext haxis, deriv_const, inner_zero_right]
  -- the outer edge is the circulation
  have hO : (∫ χ in (-π)..π, pullComp B X ζ₀ (basis 1) (k₀, χ)) =
      lineIntegral B (fun χ => X (coordPt k₀ χ ζ₀)) (-π) π := by
    refine intervalIntegral.integral_congr fun χ hχ => ?_
    rw [uIcc_of_le hpi] at hχ
    have d := (hX k₀ ⟨hk₀, le_rfl⟩ χ hχ).differentiableAt (by norm_num)
    simp only [pullComp, planeMap]
    rw [fderiv_basis1 d]
  rw [hL, hS, sub_self, zero_add, hA, sub_zero, hO] at hdiv
  have hN : netToroidalCurrent μ₀ B X ζ₀ k₀ =
      μ₀⁻¹ * ∫ k in (0 : ℝ)..k₀, ∫ χ in (-π)..π, curlFlux B X ζ₀ (k, χ) := by
    rw [netToroidalCurrent, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun k _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun χ _ => ?_
    simp only [curlFlux, planeMap, ampereCurrent, tripleFlux_smul]
  rw [hN, hdiv, div_eq_inv_mul]

/-- **The section flux of a regular section spanning the poloidal loop is the C1 loop current**:
under the regularity hypotheses of `netToroidalCurrent_eq_lineIntegral_div`, if the outer edge
of the section is the poloidal loop of the torus `(R, z)` at `φ₀`, then
`netToroidalCurrent μ₀ B X ζ₀ k₀ = loopCurrent μ₀ B R z φ₀`. -/
theorem netToroidalCurrent_eq_loopCurrent {R z : ℝ → ℝ → ℝ} {φ₀ : ℝ} (hk₀ : 0 ≤ k₀)
    (hX : ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, ContDiffAt ℝ 2 X (coordPt k χ ζ₀))
    (hB : ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, ContDiffAt ℝ 1 B (X (coordPt k χ ζ₀)))
    (hseam : ∀ k, X (coordPt k π ζ₀) = X (coordPt k (-π) ζ₀))
    (haxis : ∀ χ, X (coordPt 0 χ ζ₀) = X (coordPt 0 0 ζ₀))
    (hloop : ∀ χ, X (coordPt k₀ χ ζ₀) = poloidalLoop R z φ₀ χ) :
    netToroidalCurrent μ₀ B X ζ₀ k₀ = loopCurrent μ₀ B R z φ₀ := by
  rw [netToroidalCurrent_eq_lineIntegral_div hk₀ hX hB hseam haxis, loopCurrent,
    poloidalCirculation, show (fun χ => X (coordPt k₀ χ ζ₀)) = poloidalLoop R z φ₀ from
      funext hloop]

end Stokes

/-! ## Sanity check -/

/-- **Sanity (Stokes, concrete)**: for the uniform-current field `B = e_z × x` (`μ₀ J = 2 e_z`)
and the polar section `X(k, χ, ζ) = (k cos χ, k sin χ, ζ)` of the disc of radius `k₀` in the
plane `z = ζ₀`, both sides of Stokes' theorem equal `2π k₀²/μ₀`. -/
theorem stokes_rotation_disc (μ₀ ζ₀ k₀ : ℝ) (hk₀ : 0 ≤ k₀) :
    netToroidalCurrent μ₀ (crossBilinear (basis 2))
      (fun p => toLp 2 ![p 0 * cos (p 1), p 0 * sin (p 1), p 2]) ζ₀ k₀ =
      lineIntegral (crossBilinear (basis 2))
        (fun χ => toLp 2 ![k₀ * cos χ, k₀ * sin χ, ζ₀]) (-π) π / μ₀ := by
  have hX : ∀ q : Space, ContDiffAt ℝ 2
      (fun p : Space => (toLp 2 ![p 0 * cos (p 1), p 0 * sin (p 1), p 2] : Space)) q := by
    intro q
    refine (contDiffAt_piLp 2).2 fun i => ?_
    fin_cases i
    · change ContDiffAt ℝ 2 (fun p : Space => p 0 * cos (p 1)) q; fun_prop
    · change ContDiffAt ℝ 2 (fun p : Space => p 0 * sin (p 1)) q; fun_prop
    · change ContDiffAt ℝ 2 (fun p : Space => p 2) q; fun_prop
  refine netToroidalCurrent_eq_lineIntegral_div hk₀ (fun k _ χ _ => hX _)
    (fun k _ χ _ => (crossBilinear (basis 2)).contDiff.contDiffAt) (fun k => ?_) (fun χ => ?_)
  · simp [coordPt]
  · simp [coordPt]

end PlasmaLean.Contract
