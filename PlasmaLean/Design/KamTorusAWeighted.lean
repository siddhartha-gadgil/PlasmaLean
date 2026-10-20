/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusA
public import PlasmaLean.Design.KamTorusAWeightedCheck

/-!
# The weighted K2 certificate of torus A (KAM route, lemma K3.3)

Stage K2 (`Design/KamTorusA`) bounds the invariance residual of torus A in the sup norm, which is
the weighted `ℓ¹` norm at strip width `0`. The a posteriori KAM step (`notes/theory/kam-k3-plan.md`
§2–§4) needs the analytic norm on a complex strip: the weighted `ℓ¹` norm
`‖f‖_r = ∑ |f_{k,m}| e^{r(|k| + |m|)}` of `Theory/KAM/Cohomological` (`wnorm`). It is used at
`r = r_A = 0.1257 ≈ 2π · 0.02` (`rA`). This file certifies that norm for the residual and for the
other Fourier data of torus A, with the exact coefficients of K2. There is no truncation, because
every quantity is a finite trigonometric polynomial.

**Fourier coefficients.** Every quantity `f(θ, φ)` comes with an explicit finitely supported
coefficient function `c : ℤ × ℤ → ℂ` with `f(θ, φ) = fourierSum c θ (psi φ)` for all real
`θ, φ`. Here mode `(k, m)` is `e^{i(kθ + mψ)}` and `ψ = 2φ − π/2`. The coefficients are read off
the integer polynomials of K2 (`coefZ2`, `eq_fourierSum_of_evalC`), so they are the Fourier
coefficients of `f`, which are unique.

**Main results.**
* `torusA_weighted_error_le` (the residual, with the exact `ι = (75 + √5)/562`):
  `‖resR‖_{r_A} ≤ 5.83 × 10⁻²²` and `‖resZ‖_{r_A} ≤ 3.465 × 10⁻²²` (oracle: `5.829 × 10⁻²²`,
  `3.463 × 10⁻²²`). The dyadic residual is bounded through `R̂_R`, `R̂_z`. The `ι − ι_q` correction
  `(ι − ι_q) D ∂_θK` uses the exact weighted norms of `D̂ R̂_θ` and `D̂ Ẑ_θ` (`≤ 0.29`), times
  `|ι − ι_q| ≤ 10⁻²⁹`.
* `torusA_weighted_torus`: `‖R − 1‖ ≤ 0.228`, `‖z‖ ≤ 0.224`, `‖∂_θR‖ ≤ 0.236`,
  `‖∂_θz‖ ≤ 0.231`, `‖∂_ψR‖ ≤ 0.065`, `‖∂_ψz‖ ≤ 0.063`, all at `r_A`. Here `R = 1, z = 0` is the
  exact magnetic axis, and `∂_ψ = ∂_φ/2`.
* `torusA_weighted_D`: `D = d₀ + D'` with the constant `d₀ = c0D/(16σ⁵) ∈ [1, 1.007]` and
  `‖D'‖_{r_A} ≤ 0.483`. A Neumann series in the Banach algebra `ℓ¹_{r_A}` (lemma K3.2) then gives
  `‖1/D‖_{r_A} ≤ 1/(1 − 0.483) < 1.94`; that algebra is not formalized here.

**Weights.** `e^{r_A} ≤ 74315/2^16` (`exp_rA_le`, Taylor bound). Each mode is weighted by
`(74315/2^16)^{|k|+|m|}`, using the integer weights of `Certificates/Kronecker2DWeighted`. The
loss from the rational base is a factor of at most `(1 + 1.4 × 10⁻⁵)^{325} < 1.005`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Theory.KAM

/-! ## The strip width and the weight base -/

/-- The strip width `r_A = 0.1257` (radians), approximately `2π · 0.02` (`ρ = 0.02` turns). -/
def rA : ℝ := 1257 / 10000

/-- `e^{r_A} ≤ 74315 / 2^16` (degree-6 Taylor bound with remainder). -/
theorem exp_rA_le : Real.exp rA ≤ ((74315 : ℕ) : ℝ) / 2 ^ 16 := by
  refine (Real.exp_bound' (x := rA) (by norm_num [rA]) (by norm_num [rA]) (n := 6)
    (by norm_num)).trans ?_
  norm_num [rA, Finset.sum_range_succ, Nat.factorial]

/-! ## Generic steps -/

/-- From a scaled kernel bound `X · D ≤ c κ S` and `‖f‖ · S ≤ X` to `‖f‖ ≤ (c/D) κ`. -/
theorem le_of_scaled {w X S c κ D : ℝ} (hS : 0 < S) (hD : 0 < D) (h1 : w * S ≤ X)
    (h2 : X * D ≤ c * (κ * S)) : w ≤ c / D * κ := by
  have h3 := mul_le_mul_of_nonneg_right h1 hD.le
  have h4 : (w * D) * S ≤ (c * κ) * S := by linarith
  have h5 := le_of_mul_le_mul_right h4 hS
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  linarith

/-- **Weighted norm from one kernel check** (weights `74315^s 2^{16(K − s)}`, strip `r_A`). -/
theorem wnorm_of_check {P : P2} {a J W b dc dr : ℕ} (hb : 1 ≤ b) (hbox : InBox P a J)
    (ha : a < W) (hW : W ≤ 2 ^ dc) (hJ : J + 1 ≤ 2 ^ dr) (hl1 : l1 P < 2 ^ (b - 1))
    (i₀ j₀ Ki Kj : ℕ) {Nv : ℤ} (hk : kron b W P = Nv) {c κ D : ℝ} (hD : 0 < D)
    (hc : (wl1KronP b W dc dr (J + 1) (fun i => kwtS 74315 16 Ki (ndist i i₀))
        (fun j => kwtS 74315 16 Kj (ndist j j₀)) Nv : ℝ) * D ≤
      c * (κ * 2 ^ (16 * (Ki + Kj)))) :
    InWeighted rA (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ≤ c / D * κ := by
  obtain ⟨h1, h2⟩ := wnorm_coefZ2_le_wl1KronP hb hbox ha hW hJ hl1 i₀ j₀ exp_rA_le Ki Kj
  rw [hk] at h2
  exact ⟨h1, le_of_scaled (by positivity) hD h2 hc⟩

/-- Scalar multiples of a bounded `coefZ2`. -/
theorem wnorm_smul_le {f : ℤ × ℤ → ℂ} {B : ℝ} (hf : wnorm rA f ≤ B) (c : ℂ) :
    wnorm rA (fun km => c * f km) ≤ ‖c‖ * B := by
  rw [wnorm_smul]; gcongr

/-- `‖i / x‖ = 1 / x` for `x > 0`. -/
theorem norm_I_div {x : ℝ} (hx : 0 < x) : ‖Complex.I / (x : ℂ)‖ = 1 / x := by
  rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hx.le]

/-- `‖1 / x‖ = 1 / x` for `x > 0`. -/
theorem norm_one_div {x : ℝ} (hx : 0 < x) : ‖(1 : ℂ) / (x : ℂ)‖ = 1 / x := by
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hx.le]

/-! ## Kronecker images and a priori bounds of the new polynomials -/

/-- Kronecker image of `D̂ R̂_θ`. -/
theorem kron_DRth : kron 656 385 (Dpoly * gridPoly gRth) = DRthint := by
  rw [map_mul, kron_Dpoly, kron_gridPoly]; rfl

/-- Kronecker image of `D̂ Ẑ_θ`. -/
theorem kron_DZth : kron 656 385 (Dpoly * gridPoly gZth) = DZthint := by
  rw [map_mul, kron_Dpoly, kron_gridPoly]; rfl

/-- Kronecker image of `D̂ − c0D u^{5N} v^{5M+1}`. -/
theorem kron_Dsub : kron 656 385 (Dpoly - Dmono) = Dsubint := by
  rw [map_sub, kron_Dpoly, Dmono, kron_monomial, Dsubint, pow2_eq]; push_cast; rfl

/-- Kronecker image of `R̂ − t` (grid parameters). -/
theorem kron_Rm1 : kron 128 65 (gridPoly gR - tP) = packGrid 128 65 gR (2 * M + 1) - tGrid := by
  rw [map_sub, kron_gridPoly, kron_tP]; rfl

/-- Degree box of `R̂_R`. -/
theorem box_RRpoly : InBox RRpoly (12 * N) (12 * M + 2) :=
  box_RRform (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) box_tP box_vP
    box_ChP box_SvP

/-- Degree box of `R̂_z`. -/
theorem box_RZpoly : InBox RZpoly (12 * N) (12 * M + 2) :=
  box_RZform (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) box_tP box_vP
    box_ChP box_SvP

/-- Degree box of `D̂ R̂_θ`. -/
theorem box_DRth : InBox (Dpoly * gridPoly gRth) (12 * N) (12 * M + 2) :=
  InBox.mul_le (box_Dform (box_gridPoly _) (box_gridPoly _) box_tP box_vP box_ChP box_SvP)
    (box_gridPoly _) (by omega) (by omega)

/-- Degree box of `D̂ Ẑ_θ`. -/
theorem box_DZth : InBox (Dpoly * gridPoly gZth) (12 * N) (12 * M + 2) :=
  InBox.mul_le (box_Dform (box_gridPoly _) (box_gridPoly _) box_tP box_vP box_ChP box_SvP)
    (box_gridPoly _) (by omega) (by omega)

/-- Degree box of `D̂ − c0D u^{5N} v^{5M+1}`. -/
theorem box_Dsub : InBox (Dpoly - Dmono) (10 * N) (10 * M + 2) :=
  InBox.sub (box_Dform (box_gridPoly _) (box_gridPoly _) box_tP box_vP box_ChP box_SvP)
    (InBox.mono (InBox.monomial _ _ _) (by omega) (by omega))

/-- Degree box of `R̂ − t`. -/
theorem box_Rm1 : InBox (gridPoly gR - tP) (2 * N) (2 * M) :=
  InBox.sub (box_gridPoly _) (InBox.mono box_tP (by omega) (by omega))

/-- A priori `ℓ¹` bound for `D̂`. -/
theorem l1_Dpoly_le : l1 Dpoly ≤ Dbd (gridL1 gR) (gridL1 gZ) sig :=
  l1_Dform (l1_gridPoly_le _) (l1_gridPoly_le _) l1_tP l1_vP l1_ChP l1_SvP

/-- A priori `ℓ¹` bound for `R̂_R` (digit sums are exact). -/
theorem l1_RRpoly_lt : l1 RRpoly < 2 ^ (656 - 1) :=
  (l1_RRform (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _) l1_tP
    l1_vP l1_ChP l1_SvP).trans_lt apriori_RR

/-- A priori `ℓ¹` bound for `R̂_z`. -/
theorem l1_RZpoly_lt : l1 RZpoly < 2 ^ (656 - 1) :=
  (l1_RZform (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _) l1_tP
    l1_vP l1_ChP l1_SvP).trans_lt apriori_RZ

/-- A priori `ℓ¹` bound for `D̂ R̂_θ`. -/
theorem l1_DRth_lt : l1 (Dpoly * gridPoly gRth) < 2 ^ (656 - 1) :=
  (l1_mul' l1_Dpoly_le (l1_gridPoly_le _)).trans_lt apriori_DRth

/-- A priori `ℓ¹` bound for `D̂ Ẑ_θ`. -/
theorem l1_DZth_lt : l1 (Dpoly * gridPoly gZth) < 2 ^ (656 - 1) :=
  (l1_mul' l1_Dpoly_le (l1_gridPoly_le _)).trans_lt apriori_DZth

/-- A priori `ℓ¹` bound for `D̂ − c0D u^{5N} v^{5M+1}`. -/
theorem l1_Dsub_lt : l1 (Dpoly - Dmono) < 2 ^ (656 - 1) :=
  (l1_sub' l1_Dpoly_le (le_of_eq (by rw [Dmono, l1_monomial]; rfl))).trans_lt apriori_D

/-- A priori `ℓ¹` bound for `R̂ − t`. -/
theorem l1_Rm1_lt : l1 (gridPoly gR - tP) < 2 ^ (128 - 1) :=
  (l1_sub' (l1_gridPoly_le _) l1_tP).trans_lt apriori_grid.1

/-! ## Weighted norms of the coefficient functions -/

/-- `‖coef R̂_R‖_{r_A} ≤ 5.829 × 10⁻²² · 2^{Q+4} σ⁶`. -/
theorem wnorm_RR :
    InWeighted rA (fun km => (coefZ2 RRpoly (6 * N) (6 * M + 1) km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 RRpoly (6 * N) (6 * M + 1) km : ℂ)) ≤
        5829 / 10 ^ 25 * (2 ^ (Q + 4) * (sig : ℝ) ^ 6) :=
  wnorm_of_check (dc := 9) (dr := 9) (by norm_num)
    box_RRpoly (by norm_num [N]) (by norm_num) (by norm_num [M]) l1_RRpoly_lt
    (6 * N) (6 * M + 1) 192 133 kron_RRpoly (by norm_num) (by exact_mod_cast wcheck_RR)

/-- `‖coef R̂_z‖_{r_A} ≤ 3.464 × 10⁻²² · 2^{Q+5} σ⁶`. -/
theorem wnorm_RZ :
    InWeighted rA (fun km => (coefZ2 RZpoly (6 * N) (6 * M + 1) km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 RZpoly (6 * N) (6 * M + 1) km : ℂ)) ≤
        3464 / 10 ^ 25 * (2 ^ (Q + 5) * (sig : ℝ) ^ 6) :=
  wnorm_of_check (dc := 9) (dr := 9) (by norm_num)
    box_RZpoly (by norm_num [N]) (by norm_num) (by norm_num [M]) l1_RZpoly_lt
    (6 * N) (6 * M + 1) 192 133 kron_RZpoly (by norm_num) (by exact_mod_cast wcheck_RZ)

/-- `‖coef D̂ R̂_θ‖_{r_A} ≤ 0.28 · 16 σ⁶`. -/
theorem wnorm_DRth :
    InWeighted rA (fun km => (coefZ2 (Dpoly * gridPoly gRth) (6 * N) (6 * M + 1) km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 (Dpoly * gridPoly gRth) (6 * N) (6 * M + 1) km : ℂ)) ≤
        28 / 100 * (16 * (sig : ℝ) ^ 6) :=
  wnorm_of_check (dc := 9) (dr := 9) (by norm_num) box_DRth (by norm_num [N]) (by norm_num)
    (by norm_num [M]) l1_DRth_lt (6 * N) (6 * M + 1) 192 133 kron_DRth (by norm_num)
    (by exact_mod_cast wcheck_DRth)

/-- `‖coef D̂ Ẑ_θ‖_{r_A} ≤ 0.29 · 16 σ⁶`. -/
theorem wnorm_DZth :
    InWeighted rA (fun km => (coefZ2 (Dpoly * gridPoly gZth) (6 * N) (6 * M + 1) km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 (Dpoly * gridPoly gZth) (6 * N) (6 * M + 1) km : ℂ)) ≤
        29 / 100 * (16 * (sig : ℝ) ^ 6) :=
  wnorm_of_check (dc := 9) (dr := 9) (by norm_num) box_DZth (by norm_num [N]) (by norm_num)
    (by norm_num [M]) l1_DZth_lt (6 * N) (6 * M + 1) 192 133 kron_DZth (by norm_num)
    (by exact_mod_cast wcheck_DZth)

/-- `‖coef (D̂ − c0D mono)‖_{r_A} ≤ 0.483 · 16 σ⁵`. -/
theorem wnorm_Dsub :
    InWeighted rA (fun km => (coefZ2 (Dpoly - Dmono) (5 * N) (5 * M + 1) km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 (Dpoly - Dmono) (5 * N) (5 * M + 1) km : ℂ)) ≤
        483 / 1000 * (16 * (sig : ℝ) ^ 5) :=
  wnorm_of_check (dc := 9) (dr := 8) (by norm_num) box_Dsub (by norm_num [N]) (by norm_num)
    (by norm_num [M]) l1_Dsub_lt (5 * N) (5 * M + 1) 160 111 kron_Dsub (by norm_num)
    (by exact_mod_cast wcheck_Dsub)

/-- Weighted norm of a torus grid from `wcheck_grid`. -/
theorem wnorm_grid {P : P2} (hbox : InBox P (2 * N) (2 * M)) (hl1 : l1 P < 2 ^ (128 - 1))
    {Nv : ℤ} (hk : kron 128 65 P = Nv) {c : ℝ}
    (hc : (wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) Nv : ℝ) * 1000 ≤
      c * ((sig : ℝ) * 2 ^ (16 * (32 + 22)))) :
    InWeighted rA (fun km => (coefZ2 P N M km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 P N M km : ℂ)) ≤ c / 1000 * sig :=
  wnorm_of_check (dc := 7) (dr := 6) (by norm_num) hbox (by norm_num [N]) (by norm_num [N])
    (by norm_num [M]) hl1 N M 32 22 hk (by norm_num) hc

/-! ## Fourier expansions -/

/-- `u = e^{iθ}`. -/
theorem uu_eq (θ : ℝ) : uu θ = Complex.exp (θ * Complex.I) := rfl
/-- `v = e^{iψ}`. -/
theorem vv_eq (φ : ℝ) : vv φ = Complex.exp (psi φ * Complex.I) := rfl

/-- `σ ≠ 0` in `ℂ`. -/
theorem sigC_ne : ((sig : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sig_pos.ne'

/-- Fourier coefficients of the residual `resR` (exact `ι`). -/
def resRcoef (km : ℤ × ℤ) : ℂ :=
  Complex.I / ((2 ^ (Q + 4) * (sig : ℝ) ^ 6 : ℝ) : ℂ) * coefZ2 RRpoly (6 * N) (6 * M + 1) km +
    ((iota - iotaQ : ℝ) : ℂ) * (Complex.I / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ)) *
      coefZ2 (Dpoly * gridPoly gRth) (6 * N) (6 * M + 1) km

/-- Fourier coefficients of the residual `resZ` (exact `ι`). -/
def resZcoef (km : ℤ × ℤ) : ℂ :=
  1 / ((2 ^ (Q + 5) * (sig : ℝ) ^ 6 : ℝ) : ℂ) * coefZ2 RZpoly (6 * N) (6 * M + 1) km +
    ((iota - iotaQ : ℝ) : ℂ) * (1 / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ)) *
      coefZ2 (Dpoly * gridPoly gZth) (6 * N) (6 * M + 1) km

/-- The dyadic `R`-residual (transform `ι_q`) is the Fourier series of `(i/κ_R) coefZ2 R̂_R`. -/
theorem resRq_fourier (θ φ : ℝ) :
    (resRw iotaQ θ φ : ℂ) = fourierSum (fun km =>
      Complex.I / ((2 ^ (Q + 4) * (sig : ℝ) ^ 6 : ℝ) : ℂ) *
        coefZ2 RRpoly (6 * N) (6 * M + 1) km) θ (psi φ) := by
  have hκ : ((2 ^ (Q + 4) * (sig : ℝ) ^ 6 : ℝ) : ℂ) ≠ 0 := by
    have := sig_pos; exact_mod_cast (by positivity : (0 : ℝ) < 2 ^ (Q + 4) * (sig : ℝ) ^ 6).ne'
  have h := eq_fourierSum_of_evalC (P := RRpoly) (θ := θ) (ψ := psi φ)
    box_RRpoly (by norm_num [N] : 12 * N < 385) le_rfl (6 * N) (6 * M + 1)
    (c := -Complex.I * ((2 ^ (Q + 4) * (sig : ℝ) ^ 6 : ℝ) : ℂ)) (f := (resRw iotaQ θ φ : ℂ))
    (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) hκ)
    (by rw [← uu_eq, ← vv_eq, evalC_RR, ww]; push_cast; ring)
  rw [h]
  congr 1; funext km; congr 1
  rw [mul_inv, inv_neg, Complex.inv_I, div_eq_mul_inv]; ring

/-- `D ∂_θR` is the Fourier series of `(i/(16σ⁶)) coefZ2 (D̂ R̂_θ)`. -/
theorem DRth_fourier (θ φ : ℝ) :
    ((Dval θ φ * torusRθ θ φ : ℝ) : ℂ) = fourierSum (fun km =>
      Complex.I / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ) *
        coefZ2 (Dpoly * gridPoly gRth) (6 * N) (6 * M + 1) km) θ (psi φ) := by
  have hκ : ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ) ≠ 0 := by
    have := sig_pos; exact_mod_cast (by positivity : (0 : ℝ) < 16 * (sig : ℝ) ^ 6).ne'
  have h := eq_fourierSum_of_evalC (θ := θ) (ψ := psi φ) box_DRth (by norm_num [N] : 12 * N < 385)
    le_rfl (6 * N) (6 * M + 1)
    (c := -Complex.I * ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ)) (f := ((Dval θ φ * torusRθ θ φ : ℝ) : ℂ))
    (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) hκ)
    (by rw [← uu_eq, ← vv_eq, map_mul, evalC_D, evalC_Rth, tt, ww]; push_cast; ring)
  rw [h]
  congr 1; funext km; congr 1
  rw [mul_inv, inv_neg, Complex.inv_I, div_eq_mul_inv]; ring

/-- The dyadic `z`-residual is the Fourier series of `κ_z⁻¹ coefZ2 R̂_z`. -/
theorem resZq_fourier (θ φ : ℝ) :
    (resZw iotaQ θ φ : ℂ) = fourierSum (fun km =>
      1 / ((2 ^ (Q + 5) * (sig : ℝ) ^ 6 : ℝ) : ℂ) *
        coefZ2 RZpoly (6 * N) (6 * M + 1) km) θ (psi φ) := by
  have hκ : ((2 ^ (Q + 5) * (sig : ℝ) ^ 6 : ℝ) : ℂ) ≠ 0 := by
    have := sig_pos; exact_mod_cast (by positivity : (0 : ℝ) < 2 ^ (Q + 5) * (sig : ℝ) ^ 6).ne'
  have h := eq_fourierSum_of_evalC (P := RZpoly) (θ := θ) (ψ := psi φ)
    box_RZpoly (by norm_num [N] : 12 * N < 385) le_rfl (6 * N) (6 * M + 1)
    (c := ((2 ^ (Q + 5) * (sig : ℝ) ^ 6 : ℝ) : ℂ)) (f := (resZw iotaQ θ φ : ℂ)) hκ
    (by rw [← uu_eq, ← vv_eq, evalC_RZ, ww]; push_cast; ring)
  rw [h]
  congr 1; funext km; congr 1
  rw [one_div]

/-- `D ∂_θz` is the Fourier series of `(16σ⁶)⁻¹ coefZ2 (D̂ Ẑ_θ)`. -/
theorem DZth_fourier (θ φ : ℝ) :
    ((Dval θ φ * torusZθ θ φ : ℝ) : ℂ) = fourierSum (fun km =>
      1 / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ) *
        coefZ2 (Dpoly * gridPoly gZth) (6 * N) (6 * M + 1) km) θ (psi φ) := by
  have hκ : ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ) ≠ 0 := by
    have := sig_pos; exact_mod_cast (by positivity : (0 : ℝ) < 16 * (sig : ℝ) ^ 6).ne'
  have h := eq_fourierSum_of_evalC (θ := θ) (ψ := psi φ) box_DZth (by norm_num [N] : 12 * N < 385)
    le_rfl (6 * N) (6 * M + 1)
    (c := ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ)) (f := ((Dval θ φ * torusZθ θ φ : ℝ) : ℂ)) hκ
    (by rw [← uu_eq, ← vv_eq, map_mul, evalC_D, evalC_Zth, tt, ww]; push_cast; ring)
  rw [h]
  congr 1; funext km; congr 1
  rw [one_div]

/-- `resR` is the Fourier series of `resRcoef`. -/
theorem resR_fourier (θ φ : ℝ) : (resR θ φ : ℂ) = fourierSum resRcoef θ (psi φ) := by
  have e : resR θ φ = resRw iotaQ θ φ + (iota - iotaQ) * (Dval θ φ * torusRθ θ φ) := by
    rw [← sub_eq_iff_eq_add', resR_sub]; ring
  have hs1 := summable_smul_coefZ2_mode
    box_RRpoly (by norm_num [N] : 12 * N < 385) le_rfl (6 * N) (6 * M + 1)
    (Complex.I / ((2 ^ (Q + 4) * (sig : ℝ) ^ 6 : ℝ) : ℂ)) θ (psi φ)
  have hs2 := summable_smul_coefZ2_mode box_DRth (by norm_num [N] : 12 * N < 385) le_rfl
    (6 * N) (6 * M + 1)
    (((iota - iotaQ : ℝ) : ℂ) * (Complex.I / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ))) θ (psi φ)
  unfold resRcoef
  rw [fourierSum_add hs1 hs2, e, Complex.ofReal_add, Complex.ofReal_mul,
    resRq_fourier, DRth_fourier]
  congr 1
  simp only [fourierSum, mul_assoc]
  simp only [tsum_mul_left]

/-- `resZ` is the Fourier series of `resZcoef`. -/
theorem resZ_fourier (θ φ : ℝ) : (resZ θ φ : ℂ) = fourierSum resZcoef θ (psi φ) := by
  have e : resZ θ φ = resZw iotaQ θ φ + (iota - iotaQ) * (Dval θ φ * torusZθ θ φ) := by
    rw [← sub_eq_iff_eq_add', resZ_sub]; ring
  have hs1 := summable_smul_coefZ2_mode
    box_RZpoly (by norm_num [N] : 12 * N < 385) le_rfl (6 * N) (6 * M + 1)
    (1 / ((2 ^ (Q + 5) * (sig : ℝ) ^ 6 : ℝ) : ℂ)) θ (psi φ)
  have hs2 := summable_smul_coefZ2_mode box_DZth (by norm_num [N] : 12 * N < 385) le_rfl
    (6 * N) (6 * M + 1)
    (((iota - iotaQ : ℝ) : ℂ) * (1 / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ))) θ (psi φ)
  unfold resZcoef
  rw [fourierSum_add hs1 hs2, e, Complex.ofReal_add, Complex.ofReal_mul,
    resZq_fourier, DZth_fourier]
  congr 1
  simp only [fourierSum, mul_assoc]
  simp only [tsum_mul_left]

/-! ## The weighted residual bound -/

/-- **Weighted K2 certificate (lemma K3.3).** The invariance residuals of torus A (exact
`ι = (75 + √5)/562`) are the Fourier series of the finitely supported coefficient functions
`resRcoef`, `resZcoef`, and on the strip `r_A = 0.1257`
`‖resR‖_{r_A} = ∑ |resRcoef_{k,m}| e^{r_A(|k|+|m|)} ≤ 5.83 × 10⁻²²` and
`‖resZ‖_{r_A} ≤ 3.465 × 10⁻²²`. -/
theorem torusA_weighted_error_le :
    (∀ θ φ, (resR θ φ : ℂ) = fourierSum resRcoef θ (psi φ)) ∧
      (∀ θ φ, (resZ θ φ : ℂ) = fourierSum resZcoef θ (psi φ)) ∧
      InWeighted rA resRcoef ∧ InWeighted rA resZcoef ∧
      wnorm rA resRcoef ≤ 583 / 10 ^ 24 ∧ wnorm rA resZcoef ≤ 3465 / 10 ^ 25 := by
  have hσ := sig_pos
  have hi := iota_sub_iotaQ
  obtain ⟨iR, wR⟩ := wnorm_RR
  obtain ⟨iZ, wZ⟩ := wnorm_RZ
  obtain ⟨iDR, wDR⟩ := wnorm_DRth
  obtain ⟨iDZ, wDZ⟩ := wnorm_DZth
  have κR : (0 : ℝ) < 2 ^ (Q + 4) * (sig : ℝ) ^ 6 := by positivity
  have κZ : (0 : ℝ) < 2 ^ (Q + 5) * (sig : ℝ) ^ 6 := by positivity
  have κD : (0 : ℝ) < 16 * (sig : ℝ) ^ 6 := by positivity
  have hnI : ‖((iota - iotaQ : ℝ) : ℂ) * (Complex.I / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ))‖ ≤
      1 / 10 ^ 29 * (1 / (16 * (sig : ℝ) ^ 6)) := by
    rw [norm_mul, norm_I_div κD, Complex.norm_real, Real.norm_eq_abs]; gcongr
  have hn1 : ‖((iota - iotaQ : ℝ) : ℂ) * (1 / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ))‖ ≤
      1 / 10 ^ 29 * (1 / (16 * (sig : ℝ) ^ 6)) := by
    rw [norm_mul, norm_one_div κD, Complex.norm_real, Real.norm_eq_abs]; gcongr
  refine ⟨resR_fourier, resZ_fourier, inWeighted_add (inWeighted_smul iR _)
    (inWeighted_smul iDR _), inWeighted_add (inWeighted_smul iZ _) (inWeighted_smul iDZ _),
    ?_, ?_⟩
  · refine (wnorm_add_le (inWeighted_smul iR _) (inWeighted_smul iDR _)).trans ?_
    have a1 := wnorm_smul_le wR (Complex.I / ((2 ^ (Q + 4) * (sig : ℝ) ^ 6 : ℝ) : ℂ))
    have a2 := wnorm_smul_le wDR
      (((iota - iotaQ : ℝ) : ℂ) * (Complex.I / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ)))
    rw [norm_I_div κR] at a1
    have a3 : ‖((iota - iotaQ : ℝ) : ℂ) * (Complex.I / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ))‖ *
        (28 / 100 * (16 * (sig : ℝ) ^ 6)) ≤ 1 / 10 ^ 29 * (28 / 100) := by
      calc _ ≤ 1 / 10 ^ 29 * (1 / (16 * (sig : ℝ) ^ 6)) * (28 / 100 * (16 * (sig : ℝ) ^ 6)) := by
            gcongr
        _ = _ := by field_simp
    have a4 : 1 / (2 ^ (Q + 4) * (sig : ℝ) ^ 6) *
        (5829 / 10 ^ 25 * (2 ^ (Q + 4) * (sig : ℝ) ^ 6)) = 5829 / 10 ^ 25 := by field_simp
    linarith
  · refine (wnorm_add_le (inWeighted_smul iZ _) (inWeighted_smul iDZ _)).trans ?_
    have a1 := wnorm_smul_le wZ (1 / ((2 ^ (Q + 5) * (sig : ℝ) ^ 6 : ℝ) : ℂ))
    have a2 := wnorm_smul_le wDZ
      (((iota - iotaQ : ℝ) : ℂ) * (1 / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ)))
    rw [norm_one_div κZ] at a1
    have a3 : ‖((iota - iotaQ : ℝ) : ℂ) * (1 / ((16 * (sig : ℝ) ^ 6 : ℝ) : ℂ))‖ *
        (29 / 100 * (16 * (sig : ℝ) ^ 6)) ≤ 1 / 10 ^ 29 * (29 / 100) := by
      calc _ ≤ 1 / 10 ^ 29 * (1 / (16 * (sig : ℝ) ^ 6)) * (29 / 100 * (16 * (sig : ℝ) ^ 6)) := by
            gcongr
        _ = _ := by field_simp
    have a4 : 1 / (2 ^ (Q + 5) * (sig : ℝ) ^ 6) *
        (3464 / 10 ^ 25 * (2 ^ (Q + 5) * (sig : ℝ) ^ 6)) = 3464 / 10 ^ 25 := by field_simp
    linarith

/-! ## The torus and the denominator `D` in the weighted norm -/

/-- Fourier expansion plus weighted bound for `c⁻¹ coefZ2 P i₀ j₀`, from an evaluation identity
`P(u, v) = c f u^{i₀} v^{j₀}` and a weighted bound for `coefZ2 P i₀ j₀`. -/
theorem fourier_wnorm {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {B : ℝ}
    (hP : InWeighted rA (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ∧
      wnorm rA (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ≤ B)
    {c : ℂ} (hc : c ≠ 0) {f : ℝ → ℝ → ℝ}
    (hf : ∀ θ φ, evalC (uu θ) (vv φ) P = c * (f θ φ : ℂ) * (uu θ ^ i₀ * vv φ ^ j₀)) :
    (∀ θ φ, (f θ φ : ℂ) = fourierSum (fun km => c⁻¹ * coefZ2 P i₀ j₀ km) θ (psi φ)) ∧
      InWeighted rA (fun km => c⁻¹ * coefZ2 P i₀ j₀ km) ∧
      wnorm rA (fun km => c⁻¹ * coefZ2 P i₀ j₀ km) ≤ ‖c‖⁻¹ * B :=
  ⟨fun θ φ => eq_fourierSum_of_evalC hbox ha hS i₀ j₀ hc (hf θ φ), inWeighted_smul hP.1 _, by
    rw [wnorm_smul, norm_inv]; gcongr; exact hP.2⟩

/-- `‖σ‖ = σ`. -/
theorem norm_sigC : ‖((sig : ℝ) : ℂ)‖ = sig := by
  rw [Complex.norm_real, Real.norm_of_nonneg sig_pos.le]

/-- `‖iσ‖ = σ`. -/
theorem norm_I_sigC : ‖Complex.I * ((sig : ℝ) : ℂ)‖ = sig := by
  rw [norm_mul, Complex.norm_I, one_mul, norm_sigC]

/-- `‖−iσ‖ = σ`. -/
theorem norm_negI_sigC : ‖-Complex.I * ((sig : ℝ) : ℂ)‖ = sig := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_sigC]

/-- `iσ ≠ 0`. -/
theorem I_sigC_ne : Complex.I * ((sig : ℝ) : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero sigC_ne

/-- `−iσ ≠ 0`. -/
theorem negI_sigC_ne : -Complex.I * ((sig : ℝ) : ℂ) ≠ 0 :=
  mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) sigC_ne

/-- `σ⁻¹ (c/1000 · σ) = c/1000`. -/
theorem sig_inv_mul (c : ℝ) : (sig : ℝ)⁻¹ * (c / 1000 * sig) = c / 1000 := by
  have := sig_pos.ne'; field_simp

/-- Fourier coefficients of `R − 1` (distance from the axis value `R = 1`). -/
def Rm1coef (km : ℤ × ℤ) : ℂ := ((sig : ℝ) : ℂ)⁻¹ * coefZ2 (gridPoly gR - tP) N M km
/-- Fourier coefficients of `z`. -/
def Zcoef (km : ℤ × ℤ) : ℂ := (Complex.I * ((sig : ℝ) : ℂ))⁻¹ * coefZ2 (gridPoly gZ) N M km
/-- Fourier coefficients of `∂_θ R`. -/
def Rθcoef (km : ℤ × ℤ) : ℂ := (-Complex.I * ((sig : ℝ) : ℂ))⁻¹ * coefZ2 (gridPoly gRth) N M km
/-- Fourier coefficients of `∂_θ z`. -/
def Zθcoef (km : ℤ × ℤ) : ℂ := ((sig : ℝ) : ℂ)⁻¹ * coefZ2 (gridPoly gZth) N M km
/-- Fourier coefficients of `∂_ψ R = ∂_φ R / 2`. -/
def Rψcoef (km : ℤ × ℤ) : ℂ := (-Complex.I * ((sig : ℝ) : ℂ))⁻¹ * coefZ2 (gridPoly gRps) N M km
/-- Fourier coefficients of `∂_ψ z = ∂_φ z / 2`. -/
def Zψcoef (km : ℤ × ℤ) : ℂ := ((sig : ℝ) : ℂ)⁻¹ * coefZ2 (gridPoly gZps) N M km

/-- `R − 1`: expansion and `‖R − 1‖_{r_A} ≤ 0.228`. -/
theorem torusA_weighted_Rm1 :
    (∀ θ φ, ((torusR θ φ - 1 : ℝ) : ℂ) = fourierSum Rm1coef θ (psi φ)) ∧
      InWeighted rA Rm1coef ∧ wnorm rA Rm1coef ≤ 228 / 1000 := by
  have h := fourier_wnorm box_Rm1 (by norm_num [N] : 2 * N < 65) le_rfl N M
    (wnorm_grid box_Rm1 l1_Rm1_lt kron_Rm1 (c := 228) (by exact_mod_cast wcheck_grid.1)) sigC_ne
    (f := fun θ φ => torusR θ φ - 1)
    (fun θ φ => by rw [map_sub, evalC_Rh, evalC_tP, tt, ww]; push_cast; ring)
  rw [norm_sigC, sig_inv_mul] at h
  exact h

/-- `z`: expansion and `‖z‖_{r_A} ≤ 0.224`. -/
theorem torusA_weighted_Z :
    (∀ θ φ, (torusZ θ φ : ℂ) = fourierSum Zcoef θ (psi φ)) ∧
      InWeighted rA Zcoef ∧ wnorm rA Zcoef ≤ 224 / 1000 := by
  have h := fourier_wnorm (box_gridPoly gZ) (by norm_num [N] : 2 * N < 65) le_rfl N M
    (wnorm_grid (box_gridPoly gZ) (lt_of_le_of_lt (l1_gridPoly_le _) apriori_grid.2.1)
      (kron_gridPoly 128 65 gZ) (c := 224) (by exact_mod_cast wcheck_grid.2.1)) I_sigC_ne
    (f := fun θ φ => torusZ θ φ) (fun θ φ => by rw [evalC_Zh, tt, ww]; push_cast; ring)
  rw [norm_I_sigC, sig_inv_mul] at h
  exact h

/-- `∂_θ R`: expansion and `‖∂_θ R‖_{r_A} ≤ 0.236`. -/
theorem torusA_weighted_Rθ :
    (∀ θ φ, (torusRθ θ φ : ℂ) = fourierSum Rθcoef θ (psi φ)) ∧
      InWeighted rA Rθcoef ∧ wnorm rA Rθcoef ≤ 236 / 1000 := by
  have h := fourier_wnorm (box_gridPoly gRth) (by norm_num [N] : 2 * N < 65) le_rfl N M
    (wnorm_grid (box_gridPoly gRth) (lt_of_le_of_lt (l1_gridPoly_le _) apriori_grid.2.2.1)
      (kron_gridPoly 128 65 gRth) (c := 236) (by exact_mod_cast wcheck_grid.2.2.1)) negI_sigC_ne
    (f := fun θ φ => torusRθ θ φ) (fun θ φ => by rw [evalC_Rth, tt, ww]; push_cast; ring)
  rw [norm_negI_sigC, sig_inv_mul] at h
  exact h

/-- `∂_θ z`: expansion and `‖∂_θ z‖_{r_A} ≤ 0.231`. -/
theorem torusA_weighted_Zθ :
    (∀ θ φ, (torusZθ θ φ : ℂ) = fourierSum Zθcoef θ (psi φ)) ∧
      InWeighted rA Zθcoef ∧ wnorm rA Zθcoef ≤ 231 / 1000 := by
  have h := fourier_wnorm (box_gridPoly gZth) (by norm_num [N] : 2 * N < 65) le_rfl N M
    (wnorm_grid (box_gridPoly gZth) (lt_of_le_of_lt (l1_gridPoly_le _) apriori_grid.2.2.2.1)
      (kron_gridPoly 128 65 gZth) (c := 231) (by exact_mod_cast wcheck_grid.2.2.2.1)) sigC_ne
    (f := fun θ φ => torusZθ θ φ) (fun θ φ => by rw [evalC_Zth, tt, ww]; push_cast; ring)
  rw [norm_sigC, sig_inv_mul] at h
  exact h

/-- `∂_ψ R = ∂_φ R / 2`: expansion and `‖∂_ψ R‖_{r_A} ≤ 0.065`. -/
theorem torusA_weighted_Rψ :
    (∀ θ φ, ((torusRφ θ φ / 2 : ℝ) : ℂ) = fourierSum Rψcoef θ (psi φ)) ∧
      InWeighted rA Rψcoef ∧ wnorm rA Rψcoef ≤ 65 / 1000 := by
  have h := fourier_wnorm (box_gridPoly gRps) (by norm_num [N] : 2 * N < 65) le_rfl N M
    (wnorm_grid (box_gridPoly gRps) (lt_of_le_of_lt (l1_gridPoly_le _) apriori_grid.2.2.2.2.1)
      (kron_gridPoly 128 65 gRps) (c := 65) (by exact_mod_cast wcheck_grid.2.2.2.2.1)) negI_sigC_ne
    (f := fun θ φ => torusRφ θ φ / 2)
    (fun θ φ => by rw [evalC_Rps, tt, ww]; push_cast; ring)
  rw [norm_negI_sigC, sig_inv_mul] at h
  exact h

/-- `∂_ψ z = ∂_φ z / 2`: expansion and `‖∂_ψ z‖_{r_A} ≤ 0.063`. -/
theorem torusA_weighted_Zψ :
    (∀ θ φ, ((torusZφ θ φ / 2 : ℝ) : ℂ) = fourierSum Zψcoef θ (psi φ)) ∧
      InWeighted rA Zψcoef ∧ wnorm rA Zψcoef ≤ 63 / 1000 := by
  have h := fourier_wnorm (box_gridPoly gZps) (by norm_num [N] : 2 * N < 65) le_rfl N M
    (wnorm_grid (box_gridPoly gZps) (lt_of_le_of_lt (l1_gridPoly_le _) apriori_grid.2.2.2.2.2)
      (kron_gridPoly 128 65 gZps) (c := 63) (by exact_mod_cast wcheck_grid.2.2.2.2.2)) sigC_ne
    (f := fun θ φ => torusZφ θ φ / 2)
    (fun θ φ => by rw [evalC_Zps, tt, ww]; push_cast; ring)
  rw [norm_sigC, sig_inv_mul] at h
  exact h

/-- **The torus in the weighted norm**: on the strip `r_A = 0.1257`,
`‖R − 1‖ ≤ 0.228`, `‖z‖ ≤ 0.224`, `‖∂_θR‖ ≤ 0.236`, `‖∂_θz‖ ≤ 0.231`, `‖∂_ψR‖ ≤ 0.065`,
`‖∂_ψz‖ ≤ 0.063` (each a finitely supported Fourier expansion; see the component theorems
`torusA_weighted_Rm1`, …, `torusA_weighted_Zψ` for the expansions). -/
theorem torusA_weighted_torus :
    wnorm rA Rm1coef ≤ 228 / 1000 ∧ wnorm rA Zcoef ≤ 224 / 1000 ∧
      wnorm rA Rθcoef ≤ 236 / 1000 ∧ wnorm rA Zθcoef ≤ 231 / 1000 ∧
      wnorm rA Rψcoef ≤ 65 / 1000 ∧ wnorm rA Zψcoef ≤ 63 / 1000 :=
  ⟨torusA_weighted_Rm1.2.2, torusA_weighted_Z.2.2, torusA_weighted_Rθ.2.2,
    torusA_weighted_Zθ.2.2, torusA_weighted_Rψ.2.2, torusA_weighted_Zψ.2.2⟩

/-- The constant part `d₀ = c0D / (16σ⁵)` of `D`. -/
def dA0 : ℝ := (c0D : ℝ) / (16 * (sig : ℝ) ^ 5)

/-- Fourier coefficients of `D − d₀`. -/
def Dsubcoef (km : ℤ × ℤ) : ℂ :=
  ((16 * (sig : ℝ) ^ 5 : ℝ) : ℂ)⁻¹ * coefZ2 (Dpoly - Dmono) (5 * N) (5 * M + 1) km

/-- **`D` in the weighted norm**: `D = d₀ + D'` with `1 ≤ d₀ ≤ 1.007` and `‖D'‖_{r_A} ≤ 0.483`,
where `D'` is the Fourier series of `Dsubcoef`. -/
theorem torusA_weighted_D :
    1 ≤ dA0 ∧ dA0 ≤ 1007 / 1000 ∧
      (∀ θ φ, ((Dval θ φ - dA0 : ℝ) : ℂ) = fourierSum Dsubcoef θ (psi φ)) ∧
      InWeighted rA Dsubcoef ∧ wnorm rA Dsubcoef ≤ 483 / 1000 := by
  have hσ := sig_pos
  have hκ : (0 : ℝ) < 16 * (sig : ℝ) ^ 5 := by positivity
  have hκC : ((16 * (sig : ℝ) ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  obtain ⟨c1, c2⟩ := check_c0D
  have c1' : 16 * (sig : ℝ) ^ 5 ≤ c0D := by exact_mod_cast c1
  have c2' : (c0D : ℝ) * 1000 ≤ 1007 * (16 * (sig : ℝ) ^ 5) := by exact_mod_cast c2
  have h := fourier_wnorm box_Dsub (by norm_num [N] : 10 * N < 385) le_rfl (5 * N) (5 * M + 1)
    wnorm_Dsub hκC (f := fun θ φ => Dval θ φ - dA0) (fun θ φ => by
      have hs : ((sig : ℕ) : ℂ) ≠ 0 := by exact_mod_cast sig_pos.ne'
      rw [map_sub, evalC_D, Dmono, evalC_monomial, dA0]
      push_cast
      field_simp)
  rw [Complex.norm_real, Real.norm_of_nonneg hκ.le,
    show (16 * (sig : ℝ) ^ 5)⁻¹ * (483 / 1000 * (16 * (sig : ℝ) ^ 5)) = 483 / 1000 by
      field_simp] at h
  refine ⟨?_, ?_, h⟩
  · rw [dA0, le_div_iff₀ hκ]; linarith
  · rw [dA0, div_le_iff₀ hκ]; linarith

end PlasmaLean.Design.KamTorusA
