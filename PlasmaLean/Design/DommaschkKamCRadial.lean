/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCAdmTail
public import PlasmaLean.Design.RationalStellaratorConfinedForever
public import PlasmaLean.Certificates.KronProof2D
meta import PlasmaLean.Design.DommaschkKamCAdmEnv

/-!
# Torus C is star-shaped about its `θ`-average in the direction `θ` (N-33 item 10)

The poloidal-angle convention of the contract (`Theory/Contract`, `PoloidalAngle`) needs a
continuous polar angle of each cross-section of the exact torus about a reference curve, winding
once in `θ` and not at all in `φ`. The smooth lift `angF θ a b`
(`Design/RationalStellaratorForeverCoords`) provides it as soon as the **radial condition**
`a cos θ + b sin θ > 0` holds, where `(a, b) = K(θ, φ) − K̄(φ)` and `K̄(φ)` is the `θ`-average of
the torus (`thProj`). This file proves the radial condition for every real torus `10⁻¹²`-close
(in `ℓ¹`) to the data torus C.

**The `θ`-average.** `thProj x` keeps the Fourier coefficients with `k = 0` (`coeff_thProj`); its
values do not depend on `θ` (`eval_thProj`), it is real for real `x` (`isReal_thProj`), commutes
with `rotψ` (`thProj_rotψ`) and does not increase strip norms (`Bd_thProj`, `Bd_sub_thProj`).

**The radial form.** For real `u, z`, `(u − ū) cos θ + (z − z̄) sin θ = Re (Q e^{iθ})` with
`Q = (u − ū) − i (z − z̄)` (`radQ`, `re_radQ`). If `‖Q − c₀ e^{−iθ}‖ ≤ E` with real `c₀ > E` (in
`ℓ¹`, strip `0`), the radial form is at least `c₀ − E > 0` (`re_eval_mul_ge`).

**The certificate.** For the low-resolution surrogate `(xA 4, xA 5)` of the admissibility chain
(`Design/DommaschkKamCAdmEnv`, `24 × 28` modes, scale `2^{-64}`), `Q − c₀ e^{−iθ}` is the grid
centre of `hQ` (`radQ_surr`; `c₀ = 427595792228986440/2^64 ≈ 0.023180`), whose `ℓ¹` norm is
`390457790055713542/2^64 ≈ 0.021167` (one Kronecker digit sum, `tk_rad`, `kron2_proof`). The data
torus is within `9.4 × 10⁻¹³` (`U`) and `2.9 × 10⁻¹⁶` (`z`) of the surrogate (`Bd_tg_U`,
`Bd_tg_Z`), so every torus with `‖u − u₀C‖, ‖z − z₀C‖ ≤ 10⁻¹²` satisfies the radial condition
with margin `0.002` (`radial_ge_of_close`).

**Sanity.** `thProj_one` (degenerate: constants are their own average), `thProj_mode`
(a mode with `k ≠ 0` has average `0`), `c0Q_pos` and `radMargin_pos` (concrete), and the
rejected fixture `radQ_surr_ne` (`Q` of the surrogate is not `c₀ e^{−iθ}`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open Polynomial PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.Kron2
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall WEll1Z2 Complex

/-! ## The `θ`-average -/

/-- The coefficients with `k = 0`. -/
def thSym (f : ℤ × ℤ → ℂ) (n : ℤ × ℤ) : ℂ := if n.1 = 0 then f n else 0

/-- The `k = 0` part has smaller coefficients. -/
theorem norm_thSym_le (f : ℤ × ℤ → ℂ) (n : ℤ × ℤ) : ‖thSym f n‖ ≤ ‖f n‖ := by
  unfold thSym; split_ifs <;> simp

/-- Weights are positive. -/
theorem weight_pos' (r : ℝ) (n : ℤ × ℤ) : 0 < weight r n := Real.exp_pos _

/-- Domination preserves weighted summability. -/
theorem inWeighted_of_norm_le {r : ℝ} {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (h : ∀ n, ‖g n‖ ≤ ‖f n‖) : InWeighted r g :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (weight_pos' r n).le)
    (fun n => mul_le_mul_of_nonneg_right (h n) (weight_pos' r n).le) hf

/-- Domination decreases the weighted norm. -/
theorem wnorm_le_of_norm_le {r : ℝ} {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (h : ∀ n, ‖g n‖ ≤ ‖f n‖) : wnorm r g ≤ wnorm r f :=
  Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (h n) (weight_pos' r n).le)
    (inWeighted_of_norm_le hf h) hf

/-- Strip bounds pass to elements with smaller coefficients. -/
theorem Bd_of_norm_coeff_le {ρ B : ℝ} {x y : FA} (hx : Bd ρ x B)
    (h : ∀ n, ‖coeff y n‖ ≤ ‖coeff x n‖) : Bd ρ y B :=
  ⟨inWeighted_of_norm_le hx.1 h, (wnorm_le_of_norm_le hx.1 h).trans hx.2⟩

/-- **The `θ`-average** of `x`: the Fourier modes with `k = 0`. -/
def thProj (x : FA) : FA :=
  ofCoeff (thSym (coeff x)) (inWeighted_of_norm_le (inWeighted_coeff x) (norm_thSym_le _))

/-- Coefficients of the `θ`-average. -/
@[simp] theorem coeff_thProj (x : FA) (n : ℤ × ℤ) :
    coeff (thProj x) n = if n.1 = 0 then coeff x n else 0 := by
  simp [thProj, thSym]

/-- The average does not increase strip norms. -/
theorem Bd_thProj {ρ B : ℝ} {x : FA} (h : Bd ρ x B) : Bd ρ (thProj x) B :=
  Bd_of_norm_coeff_le h fun n => by rw [coeff_thProj]; split_ifs <;> simp

/-- Removing the average does not increase strip norms. -/
theorem Bd_sub_thProj {ρ B : ℝ} {x : FA} (h : Bd ρ x B) : Bd ρ (x - thProj x) B :=
  Bd_of_norm_coeff_le h fun n => by rw [coeff_sub, coeff_thProj]; split_ifs <;> simp

/-- The average of an analytic element is analytic. -/
theorem ana_thProj {x : FA} (h : Ana x) : Ana (thProj x) := by
  obtain ⟨ρ, B, hρ, hB⟩ := h
  exact ⟨ρ, B, hρ, Bd_thProj hB⟩

/-- The average is additive. -/
theorem thProj_add (x y : FA) : thProj (x + y) = thProj x + thProj y :=
  ext_coeff fun n => by simp only [coeff_thProj, coeff_add]; split_ifs <;> simp

/-- The average commutes with the rotation `rotψ`. -/
theorem thProj_rotψ (x : FA) : thProj (rotψ x) = rotψ (thProj x) :=
  ext_coeff fun n => by simp only [coeff_thProj, coeff_rotψ]; split_ifs <;> simp

/-- The average of a real element is real. -/
theorem isReal_thProj {x : FA} (h : IsReal x) : IsReal (thProj x) :=
  IsReal.of_coeff fun n => by
    simp only [coeff_thProj, Prod.fst_neg, neg_eq_zero]
    split_ifs <;> simp [h.coeff_neg]

/-- **The average does not depend on `θ`.** -/
theorem eval_thProj (x : FA) (θ ψ : ℝ) : eval (thProj x) θ ψ = eval (thProj x) 0 ψ := by
  simp only [WEll1Z2.eval, fourierSum]
  refine tsum_congr fun n => ?_
  rw [coeff_thProj]
  split_ifs with h
  · simp [fourierMode, h]
  · simp

/-- **Sanity (degenerate)**: constants are their own average. -/
theorem thProj_one : thProj 1 = 1 :=
  ext_coeff fun n => by
    rw [coeff_thProj, coeff_one, delta2]
    split_ifs with h1 h2 <;> simp_all

/-- **Sanity**: a mode with `k ≠ 0` has average `0`. -/
theorem thProj_mode {k m : ℤ} (hk : k ≠ 0) : thProj (mode 0 (k, m)) = 0 :=
  ext_coeff fun n => by
    rw [coeff_thProj, coeff_zero]
    split_ifs with h
    · rw [coeff_mode, Pi.single_apply, ite_eq_right]
      rintro rfl; exact hk h
    · rfl

/-! ## The radial form -/

/-- `Q = (u − ū) − i (z − z̄)`: `Re (Q e^{iθ}) = (u − ū) cos θ + (z − z̄) sin θ`. -/
def radQ (x y : FA) : FA := (x - thProj x) - I • (y - thProj y)

/-- Strip bound of `Q`. -/
theorem Bd_radQ {ρ a b : ℝ} {x y : FA} (hx : Bd ρ x a) (hy : Bd ρ y b) :
    Bd ρ (radQ x y) (a + b) := by
  have h := (Bd_sub_thProj hx).sub ((Bd_sub_thProj hy).smul I)
  simpa [radQ] using h

/-- `Q` is additive. -/
theorem radQ_add (x y x' y' : FA) : radQ (x + x') (y + y') = radQ x y + radQ x' y' := by
  simp only [radQ, thProj_add, smul_sub, smul_add]
  abel

/-- `Q` commutes with `rotψ`. -/
theorem radQ_rotψ (x y : FA) : radQ (rotψ x) (rotψ y) = rotψ (radQ x y) := by
  simp only [radQ, thProj_rotψ, rotψ_sub, rotψ_smul]

/-- `e^{−iθ}` is fixed by `rotψ`. -/
theorem rotψ_mode_neg_one_zero : rotψ (mode 0 (-1, 0)) = mode 0 (-1, 0) := by
  rw [rotψ_mode]; simp

/-- **The radial form as a real part**, for real `u, z`. -/
theorem re_radQ {u z : FA} (hu : IsReal u) (hz : IsReal z) (θ ψ : ℝ) :
    (eval (radQ u z) θ ψ * fourierMode (1, 0) θ ψ).re =
      ((eval u θ ψ).re - (eval (thProj u) 0 ψ).re) * Real.cos θ +
        ((eval z θ ψ).re - (eval (thProj z) 0 ψ).re) * Real.sin θ := by
  have h1 := hu.eval_im θ ψ
  have h2 := hz.eval_im θ ψ
  have h3 := (isReal_thProj hu).eval_im θ ψ
  have h4 := (isReal_thProj hz).eval_im θ ψ
  have hf : fourierMode (1, 0) θ ψ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [fourierMode, show ((((1, 0) : ℤ × ℤ).1 : ℝ) * θ + (((1, 0) : ℤ × ℤ).2 : ℝ) * ψ) = θ by
      simp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [← eval_thProj u θ ψ, ← eval_thProj z θ ψ]
  simp only [radQ, eval_sub', eval_smul', hf]
  simp [Complex.mul_re, h1, h2, h3, h4, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- **Lower bound of the radial form**: if `‖x − c e^{−iθ}‖ ≤ E` (`ℓ¹`), then
`Re (x e^{iθ}) ≥ c − E`. -/
theorem re_eval_mul_ge {x : FA} {c E : ℝ} (h : Bd 0 (x - (c : ℂ) • mode 0 (-1, 0)) E)
    (θ ψ : ℝ) : c - E ≤ (eval x θ ψ * fourierMode (1, 0) θ ψ).re := by
  have hb := norm_eval_le_of_Bd le_rfl h θ ψ
  have hm : fourierMode (-1, 0) θ ψ * fourierMode (1, 0) θ ψ = 1 := by
    rw [fourierMode, fourierMode, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast; ring
  have e : eval x θ ψ * fourierMode (1, 0) θ ψ =
      c + eval (x - (c : ℂ) • mode 0 (-1, 0)) θ ψ * fourierMode (1, 0) θ ψ := by
    rw [eval_sub', eval_smul', eval_mode, sub_mul, mul_assoc, hm]; ring
  rw [e, Complex.add_re, Complex.ofReal_re]
  have h2 : ‖eval (x - (c : ℂ) • mode 0 (-1, 0)) θ ψ * fourierMode (1, 0) θ ψ‖ ≤ E := by
    rw [norm_mul, norm_fourierMode, mul_one]; exact hb
  have h3 := (abs_le.mp ((Complex.abs_re_le_norm
    (eval (x - (c : ℂ) • mode 0 (-1, 0)) θ ψ * fourierMode (1, 0) θ ψ)).trans h2)).1
  linarith

/-! ## The certificate for the surrogate -/

/-- The grid of `Q − c₀ e^{−iθ}` for the surrogate (layout `24 × 28`, scale `2^{-64}`): the grid
of `U − z` without the column `k = 0` and the entry `(k, m) = (−1, 0)`. -/
def hQ : ℕ → ℕ → ℤ := fun i j =>
  if i = NA ∨ (i = NA - 1 ∧ j = MA) then 0 else gA 4 i j - gA 5 i j

/-- The `e^{−iθ}`-coefficient `c₀` of `Q` for the surrogate. -/
def c0Q : ℚ := 427595792228986440 / 2 ^ 64

/-- The `ℓ¹` bound of `Q − c₀ e^{−iθ}` for the surrogate. -/
def tQ : ℚ := 390457790055713542 / 2 ^ 64

/-- The entry `(−1, 0)` of the surrogate's `U − z` grid. -/
theorem gA_c0 : gA 4 (NA - 1) MA - gA 5 (NA - 1) MA = 427595792228986440 := by kernel_fact

/-- `xA 4` as a grid centre. -/
theorem xA4_grid : xA 4 = ctr SA NA MA (1, 0, 0) (gridPolyNM NA MA (gA 4)) := rfl

/-- `xA 5` as a grid centre. -/
theorem xA5_grid : xA 5 = ctr SA NA MA (1, 0, 1) (gridPolyNM NA MA (gA 5)) := rfl

/-- **`Q − c₀ e^{−iθ}` of the surrogate is the grid centre of `hQ`.** -/
theorem radQ_surr : radQ (xA 4) (xA 5) - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0) =
    ctr SA NA MA (1, 0, 0) (gridPolyNM NA MA hQ) := by
  refine ext_coeff fun km => ?_
  obtain ⟨k, m⟩ := km
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have h2 : (2 : ℂ) ^ (64 : ℕ) ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [radQ, coeff_sub, coeff_smul, coeff_thProj, coeff_mode, xA4_grid, xA5_grid,
    coeff_ctr_grid, SA, pow_zero, mul_one, pow_one, Pi.single_apply, Prod.mk.injEq]
  by_cases hb : |k| ≤ (NA : ℤ) ∧ |m| ≤ (MA : ℤ)
  · rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left hb]
    have hk := abs_le.mp hb.1
    have hm := abs_le.mp hb.2
    by_cases hk0 : k = 0
    · subst hk0
      simp [hQ]
    · by_cases hkm : k = -1 ∧ m = 0
      · obtain ⟨rfl, rfl⟩ := hkm
        have e4 : ((-1 : ℤ) + (NA : ℤ)).toNat = NA - 1 := rfl
        have e5 : ((0 : ℤ) + (MA : ℤ)).toNat = MA := rfl
        have hQc : hQ (NA - 1) MA = 0 := by simp [hQ]
        have hc' : ((gA 4 (NA - 1) MA : ℤ) : ℂ) - ((gA 5 (NA - 1) MA : ℤ) : ℂ) =
            427595792228986440 := by exact_mod_cast gA_c0
        rw [e4, e5, hQc]
        simp only [c0Q, show ((-1 : ℤ) = 0) = False by norm_num, ↓reduceIte, and_self,
          sub_zero, mul_one, Int.cast_zero, mul_zero]
        field_simp
        push_cast
        linear_combination hc'
      · have e : hQ (k + NA).toNat (m + MA).toNat =
            gA 4 (k + NA).toNat (m + MA).toNat - gA 5 (k + NA).toNat (m + MA).toNat := by
          simp only [hQ]
          rw [ite_eq_right]
          rintro (h | ⟨h1, h2⟩)
          · exact hk0 (by omega)
          · exact hkm ⟨by omega, by omega⟩
        rw [e]
        simp only [hk0, hkm, ↓reduceIte, sub_zero, mul_zero]
        field_simp
        push_cast
        ring
  · rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right hb]
    have hkm : ¬ (k = -1 ∧ m = 0) := by
      rintro ⟨rfl, rfl⟩; exact hb ⟨by simp [NA], by simp [MA]⟩
    rw [ite_eq_right hkm]
    split_ifs <;> simp

/-- Entries of `hQ` are below `2^61`. -/
theorem abs_hQ (i j : ℕ) : |hQ i j| ≤ ((2 ^ 61 : ℕ) : ℤ) := by
  unfold hQ
  split_ifs
  · simp
  · have h4 : |gA 4 i j| ≤ ((2 ^ 60 : ℕ) : ℤ) := abs_dataGrid_le NA MA 60 datA_U 0 (by norm_num) i j
    have h5 : |gA 5 i j| ≤ ((2 ^ 60 : ℕ) : ℤ) := abs_dataGrid_le NA MA 60 datA_Z 1 (by norm_num) i j
    have h := abs_sub (gA 4 i j) (gA 5 i j)
    push_cast at h4 h5 ⊢
    linarith

set_option linter.style.longLine false in
/-- Kernel check: the `ℓ¹` norm (unit weights) of the grid `hQ`. -/
theorem tk_rad : wl1KronP 80 49 6 6 (2 * MA + 1) (fun i => kwtS 1 0 NA (ndist i (1 * NA)))
    (fun j => kwtS 1 0 MA (ndist j (1 * MA + 0))) (packGridNM 80 49 NA hQ (2 * MA + 1)) ≤ 390457790055713542 := by
  kron2_proof

/-- **The certificate**: `‖Q − c₀ e^{−iθ}‖ ≤ tQ` for the surrogate (`ℓ¹`, strip `0`). -/
theorem Bd_radQ_surr :
    Bd 0 (radQ (xA 4) (xA 5) - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0)) ((tQ : ℚ) : ℝ) := by
  rw [radQ_surr]
  have hl1 : l1 (gridPolyNM NA MA hQ) < 2 ^ (80 - 1) :=
    (l1_gridPolyNM_le_const NA MA (C := 2 ^ 61) fun i j _ _ => abs_hQ i j).trans_lt
      (by norm_num [NA, MA])
  have h := Bd_ctr_kronw (r := 0) (P := 1) (Eb := 0) (S := SA) (N := NA) (M := MA)
    (w := (1, 0, 0)) (a := 2 * NA) (J := 2 * MA) (W := 49) (b := 80) (dc := 6) (dr := 6)
    (Ki := NA) (Kj := MA) (K := 390457790055713542) (by norm_num) (by norm_num)
    (box_gridPolyNM NA MA _) (by norm_num [NA]) (by norm_num) (by norm_num [MA]) hl1
    (kron_gridPolyNM _ _ _ _ _) tk_rad
  refine h.le (le_of_eq ?_)
  norm_num [tQ, SA]

/-- **Rejected fixture**: `Q` of the surrogate is not `c₀ e^{−iθ}` (the grid `hQ` is not zero:
the certificate is not vacuous). -/
theorem radQ_surr_ne : radQ (xA 4) (xA 5) - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0) ≠ 0 := by
  rw [radQ_surr]
  intro h
  have h1 := congrArg (fun x => coeff x (1, 0)) h
  simp only [coeff_ctr_grid, coeff_zero] at h1
  rw [ite_eq_left (by simp [NA, MA])] at h1
  have h2 : hQ ((1 : ℤ) + NA).toNat ((0 : ℤ) + MA).toNat ≠ 0 := by
    have e4 : ((1 : ℤ) + NA).toNat = NA + 1 := by simp [NA]
    have e5 : ((0 : ℤ) + MA).toNat = MA := by simp [MA]
    rw [e4, e5]
    have : hQ (NA + 1) MA = 23709104065867630 := by kernel_fact
    rw [this]; norm_num
  have h3 : ((2 : ℂ) ^ SA * I ^ 0)⁻¹ ≠ 0 := by simp
  exact h2 (by exact_mod_cast (mul_eq_zero.mp h1).resolve_left h3)

/-! ## Transfer to every close torus -/

/-- The data torus: `‖Q(u₀C, z₀C) − c₀ e^{−iθ}‖ ≤ tQ + tU + tZ` with the surrogate distances. -/
theorem Bd_radQ_data : Bd 0 (radQ u₀C z₀C - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0))
    ((tQ : ℚ) + ((117 / 125000000000000 : ℚ) : ℝ) + ((2833 / 10 ^ 16 : ℚ) : ℝ)) := by
  have hq : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by norm_num
  have hU := Bd_tg_U hq
  have hZ := Bd_tg_Z hq
  rw [← Uo_sub_xA] at hU
  rw [← Zo_sub_xA] at hZ
  have e : radQ u₀C z₀C - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0) =
      rotψ (radQ (xA 4) (xA 5) - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0)) +
        rotψ (radQ (Uo - xA 4) (Zo - xA 5)) := by
    have h1 : radQ Uo Zo = radQ (xA 4) (xA 5) + radQ (Uo - xA 4) (Zo - xA 5) := by
      rw [← radQ_add]; congr 1 <;> abel
    rw [u₀C, z₀C, radQ_rotψ, h1, rotψ_sub, rotψ_smul, rotψ_mode_neg_one_zero, rotψ_add]
    abel
  rw [e, add_assoc]
  exact (Bd_rotψ Bd_radQ_surr).add (Bd_rotψ (Bd_radQ hU hZ))

/-- The margin `c₀ − tQ − tU − tZ − 2·10⁻¹²` of the radial condition. -/
def radMargin : ℚ := c0Q - tQ - 117 / 125000000000000 - 2833 / 10 ^ 16 - 2 / 10 ^ 12

/-- **Sanity (concrete)**: `c₀ > 0`. -/
theorem c0Q_pos : 0 < c0Q := by norm_num [c0Q]

/-- **Sanity (concrete)**: the margin is positive (about `0.002`). -/
theorem radMargin_pos : 1 / 500 < radMargin := by norm_num [radMargin, c0Q, tQ]

/-- **The radial condition for every close real torus**: if `‖u − u₀C‖, ‖z − z₀C‖ ≤ 10⁻¹²`
(`ℓ¹`), then `(u − ū) cos θ + (z − z̄) sin θ ≥ radMargin > 0.002` everywhere. -/
theorem radial_ge_of_close {u z : FA} (hur : IsReal u) (hzr : IsReal z)
    (hu : Bd 0 (u - u₀C) (1 / 10 ^ 12)) (hz : Bd 0 (z - z₀C) (1 / 10 ^ 12)) (θ ψ : ℝ) :
    (radMargin : ℝ) ≤ ((eval u θ ψ).re - (eval (thProj u) 0 ψ).re) * Real.cos θ +
        ((eval z θ ψ).re - (eval (thProj z) 0 ψ).re) * Real.sin θ := by
  have e : radQ u z - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0) =
      (radQ u₀C z₀C - ((c0Q : ℚ) : ℂ) • mode 0 (-1, 0)) + radQ (u - u₀C) (z - z₀C) := by
    rw [show u = u₀C + (u - u₀C) by abel, show z = z₀C + (z - z₀C) by abel, radQ_add]
    simp only [add_sub_cancel_left]
    abel
  have hB := Bd_radQ_data.add (Bd_radQ hu hz)
  rw [← e] at hB
  have h := re_eval_mul_ge (c := ((c0Q : ℚ) : ℝ)) (by exact_mod_cast hB) θ ψ
  rw [re_radQ hur hzr] at h
  refine le_trans (le_of_eq ?_) h
  simp only [radMargin]
  push_cast
  ring

end PlasmaLean.Design.DommaschkKamC
