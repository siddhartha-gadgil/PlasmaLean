/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Rotated
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Landreman family 2: the flux coordinates `(k, χ, ζ) ↦ x` as a change of variables

For Landreman's family 2 (arXiv:2609.26742 v2, §3) with `ε = 1/4`, `S = 4` and any `λ > 0`,
the paper's coordinates (3.12)–(3.18) are the map `coordMap λ (k, χ, ζ) = surfPt` of
`LandremanFamily2Surface` (the flux label is `ψ = k²/2`). This module proves:

* `hasFDerivAt_coordMap`: the actual Fréchet derivative is the matrix `jacMatrix`, whose first
  row involves the (abstract) derivative `fderiv ℝ sigP p` of `σ(k, χ, ζ)`;
* `zk_mul_sub`: the implicit-function identity `z_k σ_χ - z_χ σ_k = k/(λ cos λz · T)`, obtained by
  differentiating `Re v ∘ x = k cos χ`, `σ ∘ x = σ`, `ν ∘ x = (ε/2) sin 2ζ` (uniqueness of
  Fréchet derivatives);
* `coordDeriv_det`: `det Dx = k · JacR` (the area element `JacR = G/(λ h T cos λz)` of
  `LandremanFamily2Rotated`, paper (3.18)); in the flux label itself (`coordMapPsi`,
  `(ψ, χ, ζ) ↦ x` with `k = √(2ψ)`) the determinant is exactly `JacR` (`coordDerivPsi_det`);
* `injOn_coordMap`, `image_coordMap`: on the box `k ∈ (0, k₀]`, `χ, ζ ∈ (-π, π]`
  (`k₀ < 19/20`) the map is injective, with explicit inverse `coordInv` (`Complex.arg`), and its
  image is the shell `0 < ψ ≤ k₀²/2` of the region `R` (`|σ - S| < π/2`, `|λz| < π/2`, the
  branch containing the magnetic axis);
* `volume_axisPart`: the magnetic axis `ψ = 0` of `R` is a Lebesgue null set, so the plasma
  `{x ∈ R | ψ(x) ≤ k₀²/2}` is the image up to a null set (`plasma_ae_eq_shell`).

Everything is proved from the definitions; no step uses the paper's formulas as hypotheses.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2Coords

open Real Set MeasureTheory WithLp Filter Topology
open PlasmaLean.Fields PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Surface PlasmaLean.Design.LandremanFamily2Rotated
open PlasmaLean.Design.LandremanEquilibrium (pr hasFDerivAt_pr)

/-! ## The coordinate map -/

/-- `σ(k, χ, ζ)` at the coordinate point `p = (k, χ, ζ)`. -/
@[expose] def sigP (p : Space) : ℝ :=
  sigc (1 / 4) 4 (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2))

/-- `z(k, χ) = -arcsin(k sin χ)/λ`. -/
@[expose] def zP (lam : ℝ) (p : Space) : ℝ := -Real.arcsin (p 0 * Real.sin (p 1)) / lam

/-- **The coordinate map** `p = (k, χ, ζ) ↦ surfPt` (paper (3.12)–(3.15); flux label
`ψ = k²/2`). -/
@[expose] def coordMap (lam : ℝ) (p : Space) : Space := surfPt (1 / 4) 4 lam (p 0) (p 1) (p 2)

/-- `cos λz = √(1 - k² sin² χ)` at the coordinate point. -/
@[expose] def ccP (p : Space) : ℝ := cc (p 0) (Real.sin (p 1))

/-- `T = √(cosh² ν - k²)` at the coordinate point. -/
@[expose] def TP (p : Space) : ℝ := Tc (1 / 4) (p 0) (Real.sin (2 * p 2))

/-- The Jacobian factor `JacR` at the coordinate point. -/
@[expose] def JacP (lam : ℝ) (p : Space) : ℝ :=
  JacR lam (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) (Real.cos (2 * p 2))

/-- `d a_c/dσ = σ/(h a_c)`. -/
@[expose] def daC (σ : ℝ) : ℝ := σ / (hC (1 / 4) σ * aC (1 / 4) σ)

/-- `d b_c/dσ = σ/(h b_c)`. -/
@[expose] def dbC (σ : ℝ) : ℝ := σ / (hC (1 / 4) σ * bC (1 / 4) σ)

/-- `∂_k z = -sin χ/(λ cos λz)`. -/
@[expose] def zk (lam : ℝ) (p : Space) : ℝ := -Real.sin (p 1) / (lam * ccP p)

/-- `∂_χ z = -k cos χ/(λ cos λz)`. -/
@[expose] def zchi (lam : ℝ) (p : Space) : ℝ := -(p 0 * Real.cos (p 1)) / (lam * ccP p)

/-- The Jacobian matrix `∂x_i/∂(k, χ, ζ)_j` (the `σ`-derivatives enter through
`L = fderiv ℝ sigP p`). -/
@[expose] def jacMatrix (lam : ℝ) (p : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![daC (sigP p) * Real.cos (p 2) * fderiv ℝ sigP p (basis 0),
      daC (sigP p) * Real.cos (p 2) * fderiv ℝ sigP p (basis 1),
      daC (sigP p) * Real.cos (p 2) * fderiv ℝ sigP p (basis 2) -
        aC (1 / 4) (sigP p) * Real.sin (p 2);
    dbC (sigP p) * Real.sin (p 2) * fderiv ℝ sigP p (basis 0),
      dbC (sigP p) * Real.sin (p 2) * fderiv ℝ sigP p (basis 1),
      dbC (sigP p) * Real.sin (p 2) * fderiv ℝ sigP p (basis 2) +
        bC (1 / 4) (sigP p) * Real.cos (p 2);
    zk lam p, zchi lam p, 0]

/-- The derivative of the coordinate map as a continuous linear map (`jacMatrix`). -/
@[expose] def coordDeriv (lam : ℝ) (p : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (jacMatrix lam p))

/-- Components of the derivative: `(Dx · v)_i = Σ_j J_ij v_j`. -/
theorem coordDeriv_apply (lam : ℝ) (p v : Space) (i : Fin 3) :
    coordDeriv lam p v i = ∑ j, jacMatrix lam p i j * v j := by
  simp [coordDeriv, Matrix.mulVec, dotProduct]

/-- The coordinate point in components. -/
theorem coordMap_eq (lam : ℝ) (p : Space) :
    coordMap lam p = toLp 2 ![aC (1 / 4) (sigP p) * Real.cos (p 2),
      bC (1 / 4) (sigP p) * Real.sin (p 2), zP lam p] := rfl

/-- First component of the coordinate point. -/
@[simp] theorem coordMap_0 (lam : ℝ) (p : Space) :
    coordMap lam p 0 = aC (1 / 4) (sigP p) * Real.cos (p 2) := by simp [coordMap_eq]
/-- Second component of the coordinate point. -/
@[simp] theorem coordMap_1 (lam : ℝ) (p : Space) :
    coordMap lam p 1 = bC (1 / 4) (sigP p) * Real.sin (p 2) := by simp [coordMap_eq]
/-- Third component of the coordinate point. -/
@[simp] theorem coordMap_2 (lam : ℝ) (p : Space) : coordMap lam p 2 = zP lam p := by
  simp [coordMap_eq]

/-! ## Differentiability -/

/-- The parameter range `0 < k ≤ 19/20` on which the closed forms are smooth. -/
@[expose] def Good (p : Space) : Prop := 0 < p 0 ∧ p 0 ≤ 19 / 20

section Deriv
variable {lam : ℝ} {p : Space}

/-- `k² < 1` on the good range. -/
theorem Good.k_sq (hp : Good p) : p 0 ^ 2 < 1 := k_sq_lt_one hp.1 hp.2

/-- `|sin(σ - S)| < 1` on the good range (since `cos(σ - S) = cA > 0`). -/
theorem Good.sA_sq (hp : Good p) :
    sA (1 / 4) (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) ^ 2 < 1 := by
  have h := sA_sq_add_cA_sq (ε := 1 / 4) (s2 := Real.sin (2 * p 2)) (Real.sin_sq_add_cos_sq (p 1))
    hp.k_sq
  have := cA_pos_angles (χ := p 1) (ζ := p 2) hp.1 hp.2
  nlinarith

/-- `σ` is differentiable on the good range. -/
theorem differentiableAt_sigP (hp : Good p) : DifferentiableAt ℝ sigP p := by
  have hk := hp.k_sq
  have h0 : DifferentiableAt ℝ (fun q : Space => q 0) p := (hasFDerivAt_pr p 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun q : Space => q 1) p := (hasFDerivAt_pr p 1).differentiableAt
  have h2 : DifferentiableAt ℝ (fun q : Space => q 2) p := (hasFDerivAt_pr p 2).differentiableAt
  have hs1 : DifferentiableAt ℝ (fun q : Space => Real.sin (q 1)) p := h1.sin
  have hc1 : DifferentiableAt ℝ (fun q : Space => Real.cos (q 1)) p := h1.cos
  have hs2 : DifferentiableAt ℝ (fun q : Space => Real.sin (2 * q 2)) p :=
    (h2.const_mul 2).sin
  have hY : DifferentiableAt ℝ (fun q : Space => Yc (q 0) (Real.sin (q 1))) p := h0.mul hs1
  have hX : DifferentiableAt ℝ (fun q : Space => Xc (q 0) (Real.cos (q 1))) p := h0.mul hc1
  have hch : DifferentiableAt ℝ (fun q : Space => chc (1 / 4) (Real.sin (2 * q 2))) p :=
    (hs2.const_mul _).cosh
  have hsh : DifferentiableAt ℝ (fun q : Space => shc (1 / 4) (Real.sin (2 * q 2))) p :=
    (hs2.const_mul _).sinh
  have hcc : DifferentiableAt ℝ (fun q : Space => cc (q 0) (Real.sin (q 1))) p := by
    refine ((hY.pow 2).const_sub 1).sqrt ?_
    have := cc_sq (k := p 0) (Real.sin_sq_add_cos_sq (p 1)) hk
    have := cc_pos (k := p 0) (Real.sin_sq_add_cos_sq (p 1)) hk
    exact (by nlinarith : (0 : ℝ) < 1 - Yc (p 0) (Real.sin (p 1)) ^ 2).ne'
  have hT : DifferentiableAt ℝ (fun q : Space => Tc (1 / 4) (q 0) (Real.sin (2 * q 2))) p := by
    refine ((hch.pow 2).sub (h0.pow 2)).sqrt ?_
    have := one_le_chc (ε := 1 / 4) (s2 := Real.sin (2 * p 2))
    exact (by nlinarith : (0 : ℝ) < chc (1 / 4) (Real.sin (2 * p 2)) ^ 2 - p 0 ^ 2).ne'
  have hT0 : DifferentiableAt ℝ
      (fun q : Space => T0c (1 / 4) (q 0) (Real.sin (q 1)) (Real.sin (2 * q 2))) p :=
    (hch.pow 2).sub (hY.pow 2)
  have hA : DifferentiableAt ℝ
      (fun q : Space => sA (1 / 4) (q 0) (Real.sin (q 1)) (Real.cos (q 1))
        (Real.sin (2 * q 2))) p := by
    simp only [sA, div_eq_mul_inv]
    exact (((hcc.mul hch).mul hX).add ((hY.mul hsh).mul hT)).mul (hT0.inv
      (T0_pos (Real.sin_sq_add_cos_sq (p 1)) hk).ne')
  have hsA := hp.sA_sq
  have hne1 : sA (1 / 4) (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) ≠ -1 := by
    intro h; rw [h] at hsA; norm_num at hsA
  have hne2 : sA (1 / 4) (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) ≠ 1 := by
    intro h; rw [h] at hsA; norm_num at hsA
  exact ((Real.differentiableAt_arcsin.2 ⟨hne1, hne2⟩).comp p hA).const_add 4

/-- Derivative of `a_c(σ)` for `σ > 0`. -/
theorem hasDerivAt_aC {σ : ℝ} (hσ : 0 < σ) : HasDerivAt (aC (1 / 4)) (daC σ) σ := by
  have hh := hC_gt (ε := 1 / 4) hσ
  have ha := aC_pos (ε := 1 / 4) hσ
  have hH : HasDerivAt (hC (1 / 4)) (4 * σ / hC (1 / 4) σ) σ := by
    have h1 : HasDerivAt (fun s : ℝ => 4 * s ^ 2 + (1 / 4) ^ 2) (4 * (2 * σ)) σ := by
      simpa using ((hasDerivAt_pow 2 σ).const_mul 4).add_const ((1 / 4 : ℝ) ^ 2)
    have h2 := h1.sqrt (by positivity)
    refine h2.congr_deriv ?_
    have : hC (1 / 4) σ = √(4 * σ ^ 2 + (1 / 4) ^ 2) := rfl
    rw [← this]; field_simp
  have h3 : HasDerivAt (fun s => (hC (1 / 4) s - 1 / 4) / 2) (4 * σ / hC (1 / 4) σ / 2) σ :=
    (hH.sub_const _).div_const 2
  have h4 := h3.sqrt (by
    have : |(1 / 4 : ℝ)| = 1 / 4 := abs_of_pos (by norm_num)
    rw [this] at hh; linarith)
  refine h4.congr_deriv ?_
  have : aC (1 / 4) σ = √((hC (1 / 4) σ - 1 / 4) / 2) := rfl
  rw [← this, daC]
  have := (lt_of_le_of_lt (abs_nonneg _) hh).ne'
  field_simp
  norm_num

/-- Derivative of `b_c(σ)` for `σ > 0`. -/
theorem hasDerivAt_bC {σ : ℝ} (hσ : 0 < σ) : HasDerivAt (bC (1 / 4)) (dbC σ) σ := by
  have hh := hC_gt (ε := 1 / 4) hσ
  have hb := bC_pos (ε := 1 / 4) hσ
  have hH : HasDerivAt (hC (1 / 4)) (4 * σ / hC (1 / 4) σ) σ := by
    have h1 : HasDerivAt (fun s : ℝ => 4 * s ^ 2 + (1 / 4) ^ 2) (4 * (2 * σ)) σ := by
      simpa using ((hasDerivAt_pow 2 σ).const_mul 4).add_const ((1 / 4 : ℝ) ^ 2)
    have h2 := h1.sqrt (by positivity)
    refine h2.congr_deriv ?_
    have : hC (1 / 4) σ = √(4 * σ ^ 2 + (1 / 4) ^ 2) := rfl
    rw [← this]; field_simp
  have h3 : HasDerivAt (fun s => (hC (1 / 4) s + 1 / 4) / 2) (4 * σ / hC (1 / 4) σ / 2) σ :=
    (hH.add_const _).div_const 2
  have h4 := h3.sqrt (by
    have : |(1 / 4 : ℝ)| = 1 / 4 := abs_of_pos (by norm_num)
    rw [this] at hh; linarith)
  refine h4.congr_deriv ?_
  have : bC (1 / 4) σ = √((hC (1 / 4) σ + 1 / 4) / 2) := rfl
  rw [← this, dbC]
  have := (lt_of_le_of_lt (abs_nonneg _) hh).ne'
  field_simp
  norm_num

/-- `σ > 0` everywhere. -/
theorem sigP_pos (p : Space) : 0 < sigP p := sigma_pos (by norm_num)

/-- `cos λz > 0` for `k² < 1`. -/
theorem ccP_pos (hp : p 0 ^ 2 < 1) : 0 < ccP p := cc_pos (Real.sin_sq_add_cos_sq (p 1)) hp

/-- `∂ z/∂(k, χ)`: the derivative of `z(k, χ) = -arcsin(k sin χ)/λ`. -/
theorem hasFDerivAt_zP (hp : p 0 ^ 2 < 1) :
    HasFDerivAt (zP lam) (zk lam p • pr 0 + zchi lam p • pr 1) p := by
  have hcc := ccP_pos hp
  have hu : HasFDerivAt (fun q : Space => q 0 * Real.sin (q 1))
      (p 0 • (Real.cos (p 1) • pr 1) + Real.sin (p 1) • pr 0) p :=
    (hasFDerivAt_pr p 0).mul (hasFDerivAt_pr p 1).sin
  have hlt : (p 0 * Real.sin (p 1)) ^ 2 < 1 := by
    have := Yc_sq_le (k := p 0) (Real.sin_sq_add_cos_sq (p 1)); unfold Yc at this; linarith
  have hne1 : p 0 * Real.sin (p 1) ≠ -1 := by intro h; rw [h] at hlt; norm_num at hlt
  have hne2 : p 0 * Real.sin (p 1) ≠ 1 := by intro h; rw [h] at hlt; norm_num at hlt
  have ha := ((Real.hasDerivAt_arcsin hne1 hne2).comp_hasFDerivAt p hu).const_mul (-lam⁻¹)
  have hf : zP lam = fun q : Space => -lam⁻¹ * Real.arcsin (q 0 * Real.sin (q 1)) := by
    funext q; simp only [zP]; ring
  rw [hf]
  refine ha.congr_fderiv ?_
  have hsq : √(1 - (p 0 * Real.sin (p 1)) ^ 2) = ccP p := rfl
  rw [hsq]
  by_cases hl : lam = 0
  · subst hl; ext v; simp [zk, zchi]
  ext v
  simp [zk, zchi]
  field_simp
  ring

/-- `σ` has Fréchet derivative `fderiv ℝ sigP p` on the good range. -/
theorem hasFDerivAt_sigP (hp : Good p) : HasFDerivAt sigP (fderiv ℝ sigP p) p :=
  (differentiableAt_sigP hp).hasFDerivAt

/-- **The coordinate map is differentiable**, with derivative `coordDeriv` (the matrix
`jacMatrix`), on the good range `0 < k ≤ 19/20`. -/
theorem hasFDerivAt_coordMap (hp : Good p) : HasFDerivAt (coordMap lam) (coordDeriv lam p) p := by
  have hs := hasFDerivAt_sigP hp
  have hσ := sigP_pos p
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  fin_cases i
  · have h := ((hasDerivAt_aC hσ).comp_hasFDerivAt p hs).mul (hasFDerivAt_pr p 2).cos
    refine (h.congr_fderiv ?_)
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, PiLp.proj_apply]
    rw [coordDeriv_apply]
    simp only [one_div, Fin.isValue, add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, neg_mul,
      mul_neg, jacMatrix, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Fin.sum_univ_three, Matrix.cons_val_one, Matrix.cons_val]
    rw [clm_coords (fderiv ℝ sigP p) v]
    ring
  · have h := ((hasDerivAt_bC hσ).comp_hasFDerivAt p hs).mul (hasFDerivAt_pr p 2).sin
    refine (h.congr_fderiv ?_)
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, PiLp.proj_apply]
    rw [coordDeriv_apply]
    simp only [one_div, Fin.isValue, add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul,
      jacMatrix, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val_zero, Fin.sum_univ_three, Matrix.cons_val]
    rw [clm_coords (fderiv ℝ sigP p) v]
    ring
  · refine ((hasFDerivAt_zP (lam := lam) hp.k_sq).congr_fderiv ?_)
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, PiLp.proj_apply]
    rw [coordDeriv_apply]
    simp [Fin.sum_univ_three, jacMatrix]

end Deriv

/-! ## The implicit-function identity and the Jacobian determinant -/

section Implicit
variable {lam : ℝ} {p : Space}

/-- `σ ∘ x = σ(k, χ, ζ)`. -/
theorem sg_coordMap (lam : ℝ) (q : Space) : sg (1 / 4) (coordMap lam q) = sigP q :=
  sg_surfPt (by norm_num)

/-- `ν ∘ x = (ε/2) sin 2ζ`. -/
theorem nu_coordMap (lam : ℝ) (q : Space) :
    nu (1 / 4) (coordMap lam q) = nuc (1 / 4) (Real.sin (2 * q 2)) :=
  nu_surfPt (by norm_num)

/-- The coordinate point lies in the smooth region `𝒰`. -/
theorem coordMap_mem_U (lam : ℝ) (q : Space) : coordMap lam q ∈ U (1 / 4) :=
  surfPt_mem_U_of (by norm_num)

/-- The atoms `Re u = T`, `Re v = k cos χ` at the coordinate point (good range, `λ ≠ 0`). -/
theorem atoms_coordMap (hl : lam ≠ 0) (hp : Good p) :
    uR (1 / 4) 4 lam (coordMap lam p) = TP p ∧
      vR (1 / 4) 4 lam (coordMap lam p) = p 0 * Real.cos (p 1) := by
  have h := atoms_surfPt (ε := 1 / 4) (S := 4) (lam := lam) (k := p 0) (χ := p 1) (ζ := p 2) hl
    (by norm_num) hp.k_sq (cA_pos_angles hp.1 hp.2)
  exact ⟨h.1, h.2.2.1⟩

/-- Consistency of derivatives: `dσ ∘ Dx = Dσ(k, χ, ζ)`. -/
theorem dsg_comp (hp : Good p) :
    (dsg (1 / 4) (coordMap lam p)).comp (coordDeriv lam p) = fderiv ℝ sigP p := by
  have h := (hasFDerivAt_sg (1 / 4) (coordMap_mem_U lam p)).comp p (hasFDerivAt_coordMap hp)
  have e : sg (1 / 4) ∘ coordMap lam = sigP := funext fun q => sg_coordMap lam q
  rw [e] at h
  exact h.unique (hasFDerivAt_sigP hp)

/-- `dν ∘ Dx` vanishes on `∂_k`, `∂_χ` (since `ν ∘ x` depends only on `ζ`). -/
theorem dnu_comp_basis (hp : Good p) (j : Fin 3) (hj : j ≠ 2) :
    dnu (1 / 4) (coordMap lam p) (coordDeriv lam p (basis j)) = 0 := by
  have h := (hasFDerivAt_nu (1 / 4) (coordMap_mem_U lam p)).comp p (hasFDerivAt_coordMap hp)
  have e : nu (1 / 4) ∘ coordMap lam = fun q => 1 / 4 / 2 * Real.sin (2 * q 2) :=
    funext fun q => by rw [Function.comp_apply, nu_coordMap, nuc]
  rw [e] at h
  have h2 := (((hasFDerivAt_pr p 2).const_mul 2).sin).const_mul (1 / 4 / 2 : ℝ)
  have hu := h.unique h2
  have := congrArg (fun T => T (basis j)) hu
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [this]
  fin_cases j <;> simp_all [pr]

/-- The two implicit equations `λ Im v ∂z + T ∂σ = ∂(k cos χ)` along `∂_k`, `∂_χ`. -/
theorem implicit_eqs (hl : lam ≠ 0) (hp : Good p) (hp' : p 0 < 19 / 20) :
    lam * vI (1 / 4) 4 lam (coordMap lam p) * zk lam p + TP p * fderiv ℝ sigP p (basis 0) =
        Real.cos (p 1) ∧
      lam * vI (1 / 4) 4 lam (coordMap lam p) * zchi lam p +
        TP p * fderiv ℝ sigP p (basis 1) = -(p 0 * Real.sin (p 1)) := by
  have h := (hasFDerivAt_vR (1 / 4) 4 lam (coordMap_mem_U lam p)).comp p (hasFDerivAt_coordMap hp)
  have hev : vR (1 / 4) 4 lam ∘ coordMap lam =ᶠ[𝓝 p] fun q => q 0 * Real.cos (q 1) := by
    have ho : IsOpen {q : Space | 0 < q 0 ∧ q 0 < 19 / 20} :=
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const)
    filter_upwards [ho.mem_nhds ⟨hp.1, hp'⟩] with q hq
    exact (atoms_coordMap hl ⟨hq.1, hq.2.le⟩).2
  have h2 := (hasFDerivAt_pr p 0).mul (hasFDerivAt_pr p 1).cos
  have hu := (h.congr_of_eventuallyEq hev.symm).unique h2
  have hds := dsg_comp (lam := lam) hp
  have hT := (atoms_coordMap hl hp).1
  have e0 := congrArg (fun T => T (basis 0)) hu
  have e1 := congrArg (fun T => T (basis 1)) hu
  have hd0 := congrArg (fun T => T (basis 0)) hds
  have hd1 := congrArg (fun T => T (basis 1)) hds
  have hn0 := dnu_comp_basis (lam := lam) hp 0 (by simp)
  have hn1 := dnu_comp_basis (lam := lam) hp 1 (by simp)
  have hz0 : coordDeriv lam p (basis 0) 2 = zk lam p := by
    rw [coordDeriv_apply]; simp [jacMatrix]
  have hz1 : coordDeriv lam p (basis 1) 2 = zchi lam p := by
    rw [coordDeriv_apply]; simp [jacMatrix]
  simp only [ContinuousLinearMap.comp_apply] at e0 e1 hd0 hd1
  simp only [dvR, add_apply, sub_apply,
    smul_apply, smul_eq_mul, hn0, hn1, hd0, hd1, pr, PiLp.proj_apply,
    hz0, hz1, hT, mul_zero, sub_zero] at e0 e1
  constructor
  · rw [e0]; simp
  · rw [e1]; simp

/-- **The implicit-function identity** `z_k σ_χ - z_χ σ_k = k/(λ cos λz · T)`. -/
theorem zk_mul_sub (hl : lam ≠ 0) (hp : Good p) (hp' : p 0 < 19 / 20) :
    zk lam p * fderiv ℝ sigP p (basis 1) - zchi lam p * fderiv ℝ sigP p (basis 0) =
      p 0 / (lam * ccP p * TP p) := by
  obtain ⟨e0, e1⟩ := implicit_eqs hl hp hp'
  have hT := T_pos (ε := 1 / 4) (s2 := Real.sin (2 * p 2)) hp.k_sq
  have hc := ccP_pos hp.k_sq
  have hTP : TP p = Tc (1 / 4) (p 0) (Real.sin (2 * p 2)) := rfl
  rw [← hTP] at hT
  have hsc := Real.sin_sq_add_cos_sq (p 1)
  have key : TP p * (zk lam p * fderiv ℝ sigP p (basis 1) - zchi lam p * fderiv ℝ sigP p (basis 0))
      = p 0 / (lam * ccP p) := by
    have h3 : zk lam p * (-(p 0 * Real.sin (p 1))) - zchi lam p * Real.cos (p 1) =
        p 0 / (lam * ccP p) := by
      unfold zk zchi; field_simp; linear_combination (p 0) * hsc
    linear_combination zk lam p * e1 - zchi lam p * e0 + h3
  rw [eq_div_iff (by positivity)]
  have k2 : TP p * (zk lam p * fderiv ℝ sigP p (basis 1) - zchi lam p * fderiv ℝ sigP p (basis 0))
      * (lam * ccP p) = p 0 := by
    rw [key]; field_simp
  linear_combination k2

/-- `a_c' b_c cos² ζ + b_c' a_c sin² ζ = G/h`. -/
theorem daC_comb (σ ζ : ℝ) (hσ : 0 < σ) :
    daC σ * Real.cos ζ * (bC (1 / 4) σ * Real.cos ζ) +
      dbC σ * Real.sin ζ * (aC (1 / 4) σ * Real.sin ζ) =
      (hC (1 / 4) σ + 1 / 4 * Real.cos (2 * ζ)) / 2 / hC (1 / 4) σ := by
  have ha := aC_pos (ε := 1 / 4) hσ
  have hb := bC_pos (ε := 1 / 4) hσ
  have hh : 0 < hC (1 / 4) σ := lt_of_le_of_lt (abs_nonneg _) (hC_gt hσ)
  have hab := aC_mul_bC (ε := 1 / 4) hσ
  have ha2 := aC_sq (ε := 1 / 4) hσ
  have hb2 := bC_sq (ε := 1 / 4) hσ
  have e1 : daC σ = bC (1 / 4) σ / hC (1 / 4) σ := by
    unfold daC; rw [div_eq_div_iff (by positivity) hh.ne']; linear_combination (-hC (1 / 4) σ) * hab
  have e2 : dbC σ = aC (1 / 4) σ / hC (1 / 4) σ := by
    unfold dbC; rw [div_eq_div_iff (by positivity) hh.ne']; linear_combination (-hC (1 / 4) σ) * hab
  have hsc := Real.sin_sq_add_cos_sq ζ
  rw [e1, e2, show bC (1 / 4) σ / hC (1 / 4) σ * Real.cos ζ * (bC (1 / 4) σ * Real.cos ζ) +
    aC (1 / 4) σ / hC (1 / 4) σ * Real.sin ζ * (aC (1 / 4) σ * Real.sin ζ) =
    (bC (1 / 4) σ ^ 2 * Real.cos ζ ^ 2 + aC (1 / 4) σ ^ 2 * Real.sin ζ ^ 2) / hC (1 / 4) σ by ring,
    ha2, hb2, Real.cos_two_mul]
  congr 1
  linear_combination (hC (1 / 4) σ / 2 - 1 / 8) * hsc

/-- The `3 × 3` determinant expansion of `jacMatrix`. -/
theorem det_alg (a b c s L0 L1 L2 z0 z1 A B : ℝ) :
    Matrix.det !![a * c * L0, a * c * L1, a * c * L2 - A * s;
      b * s * L0, b * s * L1, b * s * L2 + B * c; z0, z1, 0] =
      (z0 * L1 - z1 * L0) * (a * c * (B * c) + b * s * (A * s)) := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- **Jacobian determinant**: `det Dx = k · JacR`, i.e. `dV = k JacR dk dχ dζ = JacR dψ dχ dζ`
(paper (3.18)), on the good range `0 < k < 19/20` (`λ > 0`). -/
theorem coordDeriv_det (hl : 0 < lam) (hp : Good p) (hp' : p 0 < 19 / 20) :
    (coordDeriv lam p).det = p 0 * JacP lam p := by
  rw [ContinuousLinearMap.det, coordDeriv, LinearMap.coe_toContinuousLinearMap,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, jacMatrix, det_alg,
    zk_mul_sub hl.ne' hp hp', daC_comb _ _ (sigP_pos p)]
  have hT := T_pos (ε := 1 / 4) (s2 := Real.sin (2 * p 2)) hp.k_sq
  have hc := ccP_pos hp.k_sq
  have hh : 0 < hC (1 / 4) (sigP p) := lt_of_le_of_lt (abs_nonneg _) (hC_gt (sigP_pos p))
  have hTP : TP p = Tc (1 / 4) (p 0) (Real.sin (2 * p 2)) := rfl
  rw [← hTP] at hT
  unfold JacP JacR Gc
  change _ = p 0 * ((hC (1 / 4) (sigP p) + 1 / 4 * Real.cos (2 * p 2)) / 2 /
    (lam * hC (1 / 4) (sigP p) * TP p * ccP p))
  field_simp

/-- The Jacobian is positive on the good range. -/
theorem JacP_pos (hl : 0 < lam) (hp : Good p) : 0 < JacP lam p := by
  unfold JacP JacR
  have := G_pos (ε := 1 / 4) (S := 4) (k := p 0) (s1 := Real.sin (p 1)) (c1 := Real.cos (p 1))
    (s2 := Real.sin (2 * p 2)) (by norm_num) (Real.abs_cos_le_one (2 * p 2))
  have := hc_pos (ε := 1 / 4) (k := p 0) (s1 := Real.sin (p 1)) (c1 := Real.cos (p 1))
    (s2 := Real.sin (2 * p 2)) (by norm_num : (2 : ℝ) ≤ 4)
  have := T_pos (ε := 1 / 4) (s2 := Real.sin (2 * p 2)) hp.k_sq
  have := ccP_pos hp.k_sq
  unfold ccP at this
  positivity

end Implicit

/-! ## Injectivity and image -/

/-- The coordinate box `k ∈ (0, k₀]`, `χ ∈ (-π, π]`, `ζ ∈ (-π, π]`. -/
@[expose] def coordDom (k₀ : ℝ) : Set Space :=
  {p | p 0 ∈ Ioc 0 k₀ ∧ p 1 ∈ Ioc (-π) π ∧ p 2 ∈ Ioc (-π) π}

/-- **The plasma** `{x ∈ R | ψ(x) ≤ k₀²/2}`: the region `R` (`𝒰`, `|σ - S| < π/2`,
`|λz| < π/2`) of `LandremanFamily2`, cut at the flux surface `ψ = k₀²/2`. -/
@[expose] def plasma (lam k₀ : ℝ) : Set Space :=
  {x | x ∈ R (1 / 4) 4 lam ∧ psi (1 / 4) 4 lam x ≤ k₀ ^ 2 / 2}

/-- The plasma shell `0 < ψ ≤ k₀²/2` of `R` (the plasma minus the magnetic axis). -/
@[expose] def shell (lam k₀ : ℝ) : Set Space :=
  {x | x ∈ R (1 / 4) 4 lam ∧ 0 < psi (1 / 4) 4 lam x ∧ psi (1 / 4) 4 lam x ≤ k₀ ^ 2 / 2}

/-- The magnetic axis of `R`: `ψ = 0`. -/
@[expose] def axisPart (lam : ℝ) : Set Space := {x | x ∈ R (1 / 4) 4 lam ∧ psi (1 / 4) 4 lam x = 0}

/-- Inverse map, first coordinate: `k = √(2ψ)`. -/
@[expose] def kOf (lam : ℝ) (x : Space) : ℝ := √(2 * psi (1 / 4) 4 lam x)

/-- Inverse map, poloidal angle: `χ = arg(Re v - i sin λz)` (so `k cos χ = Re v = λ B_z`,
`k sin χ = -sin λz`). -/
@[expose] def chiOf (lam : ℝ) (x : Space) : ℝ :=
  Complex.arg (((vR (1 / 4) 4 lam x : ℝ) : ℂ) + ((-sz lam x : ℝ) : ℂ) * Complex.I)

/-- Inverse map, toroidal angle: `ζ = arg(x/a_c(σ) + i y/b_c(σ))`. -/
@[expose] def zetaOf (x : Space) : ℝ :=
  Complex.arg (((x 0 / aC (1 / 4) (sg (1 / 4) x) : ℝ) : ℂ) +
    ((x 1 / bC (1 / 4) (sg (1 / 4) x) : ℝ) : ℂ) * Complex.I)

/-- The explicit inverse `x ↦ (k, χ, ζ)` of the coordinate map. -/
@[expose] def coordInv (lam : ℝ) (x : Space) : Space := toLp 2 ![kOf lam x, chiOf lam x, zetaOf x]

/-- First component of the inverse map. -/
@[simp] theorem coordInv_0 (lam : ℝ) (x : Space) : coordInv lam x 0 = kOf lam x := by
  simp [coordInv]
/-- Second component of the inverse map. -/
@[simp] theorem coordInv_1 (lam : ℝ) (x : Space) : coordInv lam x 1 = chiOf lam x := by
  simp [coordInv]
/-- Third component of the inverse map. -/
@[simp] theorem coordInv_2 (lam : ℝ) (x : Space) : coordInv lam x 2 = zetaOf x := by
  simp [coordInv]

section Image
variable {lam k₀ : ℝ}

/-- Points of the box are in the good range when `k₀ ≤ 19/20`. -/
theorem good_of_mem (hk₀ : k₀ ≤ 19 / 20) {p : Space} (hp : p ∈ coordDom k₀) : Good p :=
  ⟨hp.1.1, hp.1.2.trans hk₀⟩

/-- `coordInv` is a left inverse of `coordMap` on the box. -/
theorem coordInv_coordMap (hl : 0 < lam) (hk₀ : k₀ ≤ 19 / 20) {p : Space}
    (hp : p ∈ coordDom k₀) : coordInv lam (coordMap lam p) = p := by
  have hg := good_of_mem hk₀ hp
  obtain ⟨⟨h0, -⟩, hχ, hζ⟩ := hp
  ext i
  fin_cases i
  · change kOf lam (coordMap lam p) = p 0
    rw [kOf, coordMap, psi_surfPt hl.ne' hg.1 hg.2]
    rw [show 2 * (p 0 ^ 2 / 2) = p 0 ^ 2 by ring, Real.sqrt_sq h0.le]
  · change chiOf lam (coordMap lam p) = p 1
    have hv := (atoms_coordMap hl.ne' hg).2
    have hs : sz lam (coordMap lam p) = -(p 0 * Real.sin (p 1)) :=
      sz_surfPt hl.ne' hg.k_sq
    rw [chiOf, hv, hs, neg_neg]
    have e : (((p 0 * Real.cos (p 1) : ℝ) : ℂ) + ((p 0 * Real.sin (p 1) : ℝ) : ℂ) * Complex.I) =
        ((p 0 : ℝ) : ℂ) * (Complex.cos (p 1) + Complex.sin (p 1) * Complex.I) := by
      apply Complex.ext <;> simp
    rw [e, Complex.arg_mul_cos_add_sin_mul_I h0 hχ]
  · change zetaOf (coordMap lam p) = p 2
    have hσ := sigP_pos p
    have ha := (aC_pos (ε := 1 / 4) hσ).ne'
    have hb := (bC_pos (ε := 1 / 4) hσ).ne'
    rw [zetaOf, sg_coordMap, coordMap_0, coordMap_1, mul_div_cancel_left₀ _ ha,
      mul_div_cancel_left₀ _ hb]
    have e : (((Real.cos (p 2) : ℝ) : ℂ) + ((Real.sin (p 2) : ℝ) : ℂ) * Complex.I) =
        Complex.cos (p 2) + Complex.sin (p 2) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e, Complex.arg_cos_add_sin_mul_I hζ]

/-- `|arcsin u| < π/2` for `u² < 1`. -/
theorem abs_arcsin_lt {u : ℝ} (hu : u ^ 2 < 1) : |Real.arcsin u| < π / 2 := by
  have h1 : -1 < u := by nlinarith
  have h2 : u < 1 := by nlinarith
  rw [abs_lt]
  exact ⟨Real.neg_pi_div_two_lt_arcsin.2 h1, Real.arcsin_lt_pi_div_two.2 h2⟩

/-- The box is mapped into the shell. -/
theorem coordMap_mem_shell (hl : 0 < lam) (hk₀ : k₀ ≤ 19 / 20) {p : Space}
    (hp : p ∈ coordDom k₀) : coordMap lam p ∈ shell lam k₀ := by
  have hg := good_of_mem hk₀ hp
  have hψ : psi (1 / 4) 4 lam (coordMap lam p) = p 0 ^ 2 / 2 := psi_surfPt hl.ne' hg.1 hg.2
  refine ⟨⟨coordMap_mem_U lam p, ?_, ?_⟩, ?_, ?_⟩
  · rw [sg_coordMap, sigP, sigc, add_sub_cancel_left]
    exact abs_arcsin_lt hg.sA_sq
  · rw [coordMap_2, zP, mul_div_cancel₀ _ hl.ne', abs_neg]
    refine abs_arcsin_lt ?_
    have := Yc_sq_le (k := p 0) (Real.sin_sq_add_cos_sq (p 1)); unfold Yc at this
    nlinarith [hg.k_sq]
  · rw [hψ]; have := hg.1; positivity
  · rw [hψ]; have := hp.1.2; have := hg.1
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ this.le hp.1.2 2) (by norm_num)

/-- `coordInv` maps the shell into the box. -/
theorem coordInv_mem (hk₀ : 0 ≤ k₀) {x : Space} (hx : x ∈ shell lam k₀) :
    coordInv lam x ∈ coordDom k₀ := by
  refine ⟨⟨?_, ?_⟩, ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩⟩
  · rw [coordInv_0, kOf]; exact Real.sqrt_pos.2 (by linarith [hx.2.1])
  · rw [coordInv_0, kOf, ← Real.sqrt_sq hk₀]
    exact Real.sqrt_le_sqrt (by linarith [hx.2.2])

/-- The ellipse identity `x² b_c(σ)² + y² a_c(σ)² = σ²`, i.e. `(x, y)` lies on the axis
ellipse of parameter `σ = σ(x)` (paper (3.9)–(3.11)). -/
theorem ellipse {x : Space} (hU : x ∈ U (1 / 4)) :
    (x 0 / aC (1 / 4) (sg (1 / 4) x)) ^ 2 + (x 1 / bC (1 / 4) (sg (1 / 4) x)) ^ 2 = 1 := by
  have hσ := sg_pos hU
  have hs2 := sg_sq hU
  have ha := aC_pos (ε := 1 / 4) hσ
  have hb := bC_pos (ε := 1 / 4) hσ
  have hab := aC_mul_bC (ε := 1 / 4) hσ
  have ha2 := aC_sq (ε := 1 / 4) hσ
  have hb2 := bC_sq (ε := 1 / 4) hσ
  have hr := r2_pos hU
  have hMo : 0 ≤ Mo (1 / 4) x := Real.sqrt_nonneg _
  have hMs := Mo_sq (1 / 4) x
  set σ := sg (1 / 4) x
  have hh : 0 ≤ hC (1 / 4) σ := Real.sqrt_nonneg _
  have hh2 : hC (1 / 4) σ ^ 2 = 4 * σ ^ 2 + (1 / 4) ^ 2 := Real.sq_sqrt (by positivity)
  -- `r² h = |Z| + r⁴`
  have key : r2 x * hC (1 / 4) σ = Mo (1 / 4) x + r2 x ^ 2 := by
    have e : (r2 x * hC (1 / 4) σ) ^ 2 = (Mo (1 / 4) x + r2 x ^ 2) ^ 2 := by
      rw [mul_pow, hh2, hs2]
      have hZr : Zr (1 / 4) x = r2 x ^ 2 + 1 / 4 * (x 0 ^ 2 - x 1 ^ 2) := rfl
      have hZi : Zi (1 / 4) x = 2 * (1 / 4) * x 0 * x 1 := rfl
      have hr2 : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
      rw [hZr, hZi] at hMs
      rw [hZr]
      linear_combination (-1 : ℝ) * hMs + ((r2 x + x 0 ^ 2 + x 1 ^ 2) / 16) * hr2
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp e
  have hZr : Zr (1 / 4) x = r2 x ^ 2 + 1 / 4 * (x 0 ^ 2 - x 1 ^ 2) := rfl
  have hr2 : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  have num : x 0 ^ 2 * bC (1 / 4) σ ^ 2 + x 1 ^ 2 * aC (1 / 4) σ ^ 2 = σ ^ 2 := by
    rw [ha2, hb2, hs2]
    linear_combination (1 / 2 : ℝ) * key - (1 / 2 : ℝ) * hZr - (hC (1 / 4) σ / 2) * hr2
  have e : (x 0 / aC (1 / 4) σ) ^ 2 + (x 1 / bC (1 / 4) σ) ^ 2 =
      (x 0 ^ 2 * bC (1 / 4) σ ^ 2 + x 1 ^ 2 * aC (1 / 4) σ ^ 2) / (aC (1 / 4) σ * bC (1 / 4) σ) ^ 2
      := by field_simp
  rw [e, num, hab, div_self (pow_ne_zero 2 hσ.ne')]

/-- `Re u > 0` on `R` inside `ψ ≤ (19/20)²/2` (from `(Re u)² = cosh² ν - 2ψ ≥ 39/400` and
`Re u ≥ -|sin λz sin(σ - S) sinh ν| ≥ -251/2000`). -/
theorem uR_pos_of {x : Space} (hR : x ∈ R (1 / 4) 4 lam)
    (hψ : psi (1 / 4) 4 lam x ≤ (19 / 20) ^ 2 / 2) : 0 < uR (1 / 4) 4 lam x := by
  obtain ⟨hcz, hcx, -, hch1, -, hsh⟩ := R_facts hR
  have hsq := uR_sq_add (1 / 4) 4 lam x
  rw [psi_eq_XY] at hψ
  have hu2 : 39 / 400 ≤ uR (1 / 4) 4 lam x ^ 2 := by nlinarith
  have hlow : -(251 / 2000) ≤ uR (1 / 4) 4 lam x := by
    unfold uR
    have h1 : 0 < cz lam x * Real.cos (sg (1 / 4) x - 4) * Real.cosh (nu (1 / 4) x) := by
      have := Real.cosh_pos (nu (1 / 4) x); positivity
    have h2 : |sz lam x * Real.sin (sg (1 / 4) x - 4) * Real.sinh (nu (1 / 4) x)| ≤ 251 / 2000 := by
      rw [abs_mul, abs_mul]
      have e1 : |sz lam x| ≤ 1 := Real.abs_sin_le_one _
      have e2 : |Real.sin (sg (1 / 4) x - 4)| ≤ 1 := Real.abs_sin_le_one _
      calc |sz lam x| * |Real.sin (sg (1 / 4) x - 4)| * |Real.sinh (nu (1 / 4) x)|
          ≤ 1 * 1 * (251 / 2000) := by gcongr
        _ = 251 / 2000 := by norm_num
    linarith [le_abs_self (sz lam x * Real.sin (sg (1 / 4) x - 4) * Real.sinh (nu (1 / 4) x))]
  by_contra h
  push Not at h
  nlinarith

/-- `coordInv` is a right inverse of `coordMap` on the shell. -/
theorem coordMap_coordInv (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ ≤ 19 / 20) {x : Space}
    (hx : x ∈ shell lam k₀) : coordMap lam (coordInv lam x) = x := by
  obtain ⟨hR, hψ0, hψ1⟩ := hx
  obtain ⟨hU, hξ, hz⟩ := id hR
  obtain ⟨hcz, -, -, -, -, -⟩ := R_facts hR
  have hσ := sg_pos hU
  have hcs := Real.cos_sq_add_sin_sq (lam * x 2)
  have hch := Real.cosh_sq_sub_sinh_sq (nu (1 / 4) x)
  have hψle : psi (1 / 4) 4 lam x ≤ (19 / 20) ^ 2 / 2 :=
    hψ1.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ hk0 hk₀ 2) (by norm_num))
  have huR := uR_pos_of hR hψle
  set σ := sg (1 / 4) x with hσdef
  have ha := aC_pos (ε := 1 / 4) hσ
  have hb := bC_pos (ε := 1 / 4) hσ
  have hab := aC_mul_bC (ε := 1 / 4) hσ
  -- the toroidal angle
  have hn1 :
      ‖(((x 0 / aC (1 / 4) σ : ℝ) : ℂ) + ((x 1 / bC (1 / 4) σ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_add_mul_I, ellipse hU, Real.sqrt_one]
  have hcζ : Real.cos (zetaOf x) = x 0 / aC (1 / 4) σ := by
    have := Complex.norm_mul_cos_arg
      (((x 0 / aC (1 / 4) σ : ℝ) : ℂ) + ((x 1 / bC (1 / 4) σ : ℝ) : ℂ) * Complex.I)
    rw [hn1, one_mul] at this
    have e : zetaOf x = Complex.arg
        (((x 0 / aC (1 / 4) σ : ℝ) : ℂ) + ((x 1 / bC (1 / 4) σ : ℝ) : ℂ) * Complex.I) := rfl
    rw [e]; simpa using this
  have hsζ : Real.sin (zetaOf x) = x 1 / bC (1 / 4) σ := by
    have := Complex.norm_mul_sin_arg
      (((x 0 / aC (1 / 4) σ : ℝ) : ℂ) + ((x 1 / bC (1 / 4) σ : ℝ) : ℂ) * Complex.I)
    rw [hn1, one_mul] at this
    have e : zetaOf x = Complex.arg
        (((x 0 / aC (1 / 4) σ : ℝ) : ℂ) + ((x 1 / bC (1 / 4) σ : ℝ) : ℂ) * Complex.I) := rfl
    rw [e]; simpa using this
  -- the radius `k` and the poloidal angle
  have hk2 : 2 * psi (1 / 4) 4 lam x = vR (1 / 4) 4 lam x ^ 2 + (-sz lam x) ^ 2 := by
    unfold psi; ring
  have hnk : ‖(((vR (1 / 4) 4 lam x : ℝ) : ℂ) + ((-sz lam x : ℝ) : ℂ) * Complex.I)‖ =
      kOf lam x := by
    rw [Complex.norm_add_mul_I, kOf, hk2]
  have hcχ : kOf lam x * Real.cos (chiOf lam x) = vR (1 / 4) 4 lam x := by
    have := Complex.norm_mul_cos_arg
      (((vR (1 / 4) 4 lam x : ℝ) : ℂ) + ((-sz lam x : ℝ) : ℂ) * Complex.I)
    rw [hnk] at this
    simpa [chiOf] using this
  have hsχ : kOf lam x * Real.sin (chiOf lam x) = -sz lam x := by
    have := Complex.norm_mul_sin_arg
      (((vR (1 / 4) 4 lam x : ℝ) : ℂ) + ((-sz lam x : ℝ) : ℂ) * Complex.I)
    rw [hnk] at this
    simpa [chiOf] using this
  have hkk : kOf lam x ^ 2 = vR (1 / 4) 4 lam x ^ 2 + sz lam x ^ 2 := by
    rw [kOf, Real.sq_sqrt (by linarith), hk2]; ring
  -- `ν = (ε/2) sin 2ζ`
  have hnu : nuc (1 / 4) (Real.sin (2 * zetaOf x)) = nu (1 / 4) x := by
    rw [nuc, Real.sin_two_mul, hsζ, hcζ, nu]
    calc 1 / 4 / 2 * (2 * (x 1 / bC (1 / 4) σ) * (x 0 / aC (1 / 4) σ))
        = 1 / 4 * x 0 * x 1 / (aC (1 / 4) σ * bC (1 / 4) σ) := by field_simp
      _ = 1 / 4 * x 0 * x 1 / σ := by rw [hab]
  -- `T = Re u`, `cos λz`, `sin(σ - S)`
  have hT : Tc (1 / 4) (kOf lam x) (Real.sin (2 * zetaOf x)) = uR (1 / 4) 4 lam x := by
    rw [Tc, chc, hnu, ← Real.sqrt_sq huR.le, hkk]
    congr 1
    have hsq := uR_sq_add (1 / 4) 4 lam x
    unfold Xf Yf at hsq
    linarith
  have hcc : cc (kOf lam x) (Real.sin (chiOf lam x)) = cz lam x := by
    rw [cc, Yc, hsχ, ← Real.sqrt_sq hcz.le]
    congr 1
    unfold cz sz; linarith
  have hT0 : 0 < Real.cosh (nu (1 / 4) x) ^ 2 - (-sz lam x) ^ 2 := by
    have := Real.one_le_cosh (nu (1 / 4) x)
    have : sz lam x ^ 2 < 1 := by unfold sz; unfold cz at hcz; nlinarith
    nlinarith
  have hsA : sA (1 / 4) (kOf lam x) (Real.sin (chiOf lam x)) (Real.cos (chiOf lam x))
      (Real.sin (2 * zetaOf x)) = Real.sin (σ - 4) := by
    unfold sA
    rw [hcc, hT, Xc, Yc, hcχ, hsχ, T0c, Yc, hsχ, chc, shc, hnu, div_eq_iff hT0.ne']
    unfold vR uR cz sz
    linear_combination (Real.sin (σ - 4) * Real.cosh (nu (1 / 4) x) ^ 2) * hcs -
      (Real.sin (σ - 4) * Real.sin (lam * x 2) ^ 2) * hch
  have hsig : sigP (coordInv lam x) = σ := by
    simp only [sigP, coordInv_0, coordInv_1, coordInv_2, sigc]
    rw [hsA, Real.arcsin_sin (by linarith [(abs_lt.1 hξ).1]) (by linarith [(abs_lt.1 hξ).2])]
    ring
  ext i
  fin_cases i
  · change coordMap lam (coordInv lam x) 0 = x 0
    rw [coordMap_0, hsig, coordInv_2, hcζ]; field_simp
  · change coordMap lam (coordInv lam x) 1 = x 1
    rw [coordMap_1, hsig, coordInv_2, hsζ]; field_simp
  · change coordMap lam (coordInv lam x) 2 = x 2
    rw [coordMap_2, zP, coordInv_0, coordInv_1, hsχ, sz, Real.arcsin_neg,
      Real.arcsin_sin (by linarith [(abs_lt.1 hz).1]) (by linarith [(abs_lt.1 hz).2])]
    field_simp

/-- **Image of the box**: for `0 ≤ k₀ ≤ 19/20` the box is mapped onto the shell
`0 < ψ ≤ k₀²/2` of `R`. -/
theorem image_coordMap (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ ≤ 19 / 20) :
    coordMap lam '' coordDom k₀ = shell lam k₀ := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact coordMap_mem_shell hl hk₀ hp
  · intro hx
    exact ⟨coordInv lam x, coordInv_mem hk0 hx, coordMap_coordInv hl hk0 hk₀ hx⟩

/-- **Injectivity** of the coordinate map on the box (`k₀ ≤ 19/20`). -/
theorem injOn_coordMap (hl : 0 < lam) (hk₀ : k₀ ≤ 19 / 20) :
    InjOn (coordMap lam) (coordDom k₀) := by
  intro p hp q hq h
  rw [← coordInv_coordMap hl hk₀ hp, h, coordInv_coordMap hl hk₀ hq]

/-- The magnetic axis of `R` lies in the plane `z = 0`. -/
theorem axisPart_sub (hl : lam ≠ 0) : axisPart lam ⊆ {x : Space | x 2 = 0} := by
  rintro x ⟨⟨-, -, hz⟩, hψ⟩
  have h1 : sz lam x ^ 2 = 0 := by
    unfold psi at hψ; nlinarith [sq_nonneg (sz lam x), sq_nonneg (vR (1 / 4) 4 lam x)]
  have h2 : Real.sin (lam * x 2) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  have h3 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [(abs_lt.1 hz).1, Real.pi_pos])
    (by linarith [(abs_lt.1 hz).2, Real.pi_pos])).1 h2
  change x 2 = 0
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h hl
  · exact h

/-- **The magnetic axis is a Lebesgue null set.** -/
theorem volume_axisPart (hl : lam ≠ 0) : volume (axisPart lam) = 0 := by
  let S : Submodule ℝ Space := LinearMap.ker (pr 2 : Space →ₗ[ℝ] ℝ)
  have hS : S ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single 2 (1 : ℝ) : Space) ∈ S := h ▸ Submodule.mem_top
    simp [S, pr] at this
  refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_submodule volume S hS)
  have := axisPart_sub hl hx
  change pr 2 x = 0
  simpa [pr] using this

/-- The plasma is the shell plus the magnetic axis. -/
theorem plasma_eq (k₀ : ℝ) : plasma lam k₀ = shell lam k₀ ∪ axisPart lam := by
  ext x
  simp only [plasma, shell, axisPart, mem_union, mem_ofPred_eq]
  have := psi_nonneg (1 / 4) 4 lam x
  constructor
  · rintro ⟨hR, h⟩
    rcases this.lt_or_eq with h' | h'
    · exact Or.inl ⟨hR, h', h⟩
    · exact Or.inr ⟨hR, h'.symm⟩
  · rintro (⟨hR, -, h⟩ | ⟨hR, h⟩)
    · exact ⟨hR, h⟩
    · exact ⟨hR, by rw [h]; positivity⟩

/-- **The plasma `{ψ ≤ k₀²/2}` and the image of the coordinate box agree up to a null set.** -/
theorem plasma_ae_eq_shell (hl : lam ≠ 0) (k₀ : ℝ) : plasma lam k₀ =ᵐ[volume] shell lam k₀ := by
  rw [plasma_eq]
  exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (volume_axisPart hl))

end Image

/-! ## The flux-label coordinates `(ψ, χ, ζ)` -/

/-- `(ψ, χ, ζ) ↦ (k, χ, ζ)` with `k = √(2ψ)`. -/
@[expose] def psiToK (p : Space) : Space := toLp 2 ![√(2 * p 0), p 1, p 2]

/-- **The coordinate map in the flux label** `(ψ, χ, ζ) ↦ x` (paper (3.12)–(3.18)). -/
@[expose] def coordMapPsi (lam : ℝ) (p : Space) : Space := coordMap lam (psiToK p)

/-- The derivative of `psiToK`: `diag(1/√(2ψ), 1, 1)`. -/
@[expose] def psiToKDeriv (p : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    !![(√(2 * p 0))⁻¹, 0, 0; 0, 1, 0; 0, 0, 1])

section PsiCoords
variable {lam : ℝ} {p : Space}

/-- `psiToK` is differentiable for `ψ > 0`. -/
theorem hasFDerivAt_psiToK (hp : 0 < p 0) : HasFDerivAt psiToK (psiToKDeriv p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  have happ : ∀ v : Space, ∀ j : Fin 3, psiToKDeriv p v j =
      ∑ m, (!![(√(2 * p 0))⁻¹, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) j m * v m :=
    fun v j => by simp [psiToKDeriv, Matrix.mulVec, dotProduct]
  fin_cases i
  · have h := ((hasFDerivAt_pr p 0).const_mul 2).sqrt (by positivity)
    refine h.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, PiLp.proj_apply]
    rw [happ]
    simp [Fin.sum_univ_three]
    field_simp
  · refine (hasFDerivAt_pr p 1).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, PiLp.proj_apply]
    rw [happ]
    simp [Fin.sum_univ_three]
  · refine (hasFDerivAt_pr p 2).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, PiLp.proj_apply]
    rw [happ]
    simp [Fin.sum_univ_three]

/-- `det D(psiToK) = 1/√(2ψ)`. -/
theorem psiToKDeriv_det (p : Space) : (psiToKDeriv p).det = (√(2 * p 0))⁻¹ := by
  rw [ContinuousLinearMap.det, psiToKDeriv, LinearMap.coe_toContinuousLinearMap,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_fin_three]
  simp

/-- `k = √(2ψ)` component of `psiToK`. -/
@[simp] theorem psiToK_0 (p : Space) : psiToK p 0 = √(2 * p 0) := by simp [psiToK]

/-- **The flux-label coordinate map is differentiable** for `0 < ψ ≤ (19/20)²/2`. -/
theorem hasFDerivAt_coordMapPsi (hp : 0 < p 0) (hp' : p 0 ≤ (19 / 20) ^ 2 / 2) :
    HasFDerivAt (coordMapPsi lam) ((coordDeriv lam (psiToK p)).comp (psiToKDeriv p)) p := by
  have hg : Good (psiToK p) := by
    refine ⟨by rw [psiToK_0]; positivity, ?_⟩
    rw [psiToK_0, show (19 / 20 : ℝ) = √((19 / 20) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  exact (hasFDerivAt_coordMap hg).comp p (hasFDerivAt_psiToK hp)

/-- **Jacobian in the flux label: `det D_{(ψ,χ,ζ)} x = JacR`** (paper (3.18) derived), for
`0 < ψ < (19/20)²/2`, `λ > 0`. -/
theorem coordDerivPsi_det (hl : 0 < lam) (hp : 0 < p 0) (hp' : p 0 < (19 / 20) ^ 2 / 2) :
    ((coordDeriv lam (psiToK p)).comp (psiToKDeriv p)).det = JacP lam (psiToK p) := by
  have hk : 0 < √(2 * p 0) := by positivity
  have hk' : √(2 * p 0) < 19 / 20 := by
    rw [show (19 / 20 : ℝ) = √((19 / 20) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hg : Good (psiToK p) := ⟨by rw [psiToK_0]; exact hk, by rw [psiToK_0]; exact hk'.le⟩
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det, psiToKDeriv_det,
    coordDeriv_det hl hg (by rw [psiToK_0]; exact hk'), psiToK_0]
  field_simp

end PsiCoords

end PlasmaLean.Design.LandremanFamily2Coords
