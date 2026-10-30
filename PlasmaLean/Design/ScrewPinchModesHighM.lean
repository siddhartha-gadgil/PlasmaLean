/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.ScrewPinchModes
public import PlasmaLean.Theory.Stability.Mercier

/-!
# Newcomb stability of the screw-pinch example for every `|m| ≥ 7`, uniformly

`PlasmaLean.Design.ScrewPinchModes` certifies every mode with `1 ≤ |m| ≤ 6`, and for
`|m| ≥ 7` only the modes with `k m ≥ 0` or `5 n² ≥ 9 m²`. This file closes the remaining
gap (`|m| ≥ 7`, `k m < 0`, `5 n² < 9 m²`) **uniformly in `m` and for every real `k`**,
with an analytic Picone certificate; no numerical data are involved.

**Scaling (general profiles).** Writing `k = -m t`, `F̂ = b - t Bz`, `σ = 1/(1 + t² r²)`:

* `coefF_scale`: `f = r³ F̂² / (1 + t² r²)` does not depend on `m`;
* `coefG_scale`: `g = 2t²r² μ₀p' σ + (m² - σ) r F̂² + 2t²r³ (t²Bz² - b²) σ²`, which
  increases with `m²`.

Hence `modeStable_mono_m`: stability of `(m₀, -m₀ t)` implies stability of `(m, -m t)`
for every `m² ≥ m₀²` (any profiles). This is the scaling argument; the theorem below
does not even need it, because its certificate works directly for every `m² ≥ 49`.

**Analytic certificate (the example).** For `0 ≤ t ≤ 1/5` (the band containing every
resonant surface: `q` ranges over `[5/4, 2.52]`, so `F̂` vanishes in `[0, 1]` only for
`t ∈ [0.0996, 1/5]`) take the Suydam-type Picone function

  `φ = -½ σ r³ F̂ F̂' = ½ σ r⁴ F̂ φ₁`,   `F̂' = -r φ₁`,   `φ₁ = 1 + t q(r)/Bz`,

with `q = -2 + 5r² - r⁴` (`S' = 2 r q`). Then `f = σ r³ F̂²` and the Picone discriminant
factors exactly: with `h = φ'`,

  `g - h - φ²/f = r (σ a r⁴ + σ B r² F̂ + (m² - σ) F̂²)`   (`key_identity`),

a quadratic form in `(r², F̂)`, where `a = φ₁²/4 - 4t²` and `B` is an explicit bounded
function. Crude interval bounds (`Bz ∈ [4.69, 5.02]`, `t ≤ 1/5`) give `192 a ≥ B²`
(`disc_bound`), so the form is nonnegative as soon as `m² - σ ≥ 48`
(`residual_nonneg`). `picone_lower` (free axis value, `φ(0) = 0`) then gives
`stable_band`. At the resonant surface this is exactly Suydam's mechanism; the factor
`m²` dominates elsewhere.

For `1/5 ≤ t ≤ 1/2` there is no resonance (`F̂ ≤ -(18/55) r²`) and `g ≥ 0`
(`stable_nonresonant`); `t ≥ 1/2` is `stable_of_large_k`, and `k m ≥ 0` is
`stable_of_same_sign`.

**Main results.**

* `stable_high_m`: every real `k` and every real `m` with `m² ≥ 49` is stable;
* `stable_all_modes`: **every** mode `(m, n)` with `m ≠ 0` of the screw-pinch example
  is stable in Newcomb's reduced energy (conducting wall at `r = a`), combining
  `stable_low_m` (27 exact certificates for `|m| ≤ 6`) with `stable_high_m`.

Also recorded: `mercier_cyl_stable`, the cylindrical Mercier criterion `D_I ≤ 0` for the
example (equivalent to Suydam, `PlasmaLean.Stability.Mercier`).

Scope: unchanged from the parent file — fixed-boundary ideal MHD for the supplied Newcomb
reduction (`NewcombReduction`), `m ≠ 0`; no free-boundary, resistive, kinetic or toroidal
effects. This is a current-carrying screw pinch, not a stellarator.
-/
public section

noncomputable section
namespace PlasmaLean.Design.ScrewPinchModesHighM
open Set PlasmaLean.Stability PlasmaLean.Stability.ScrewPinchModes
open PlasmaLean.Design.ScrewPinchExample PlasmaLean.Design.ScrewPinchModes

/-! ## Scaling identities for general profiles -/

/-- `F = k Bz + m b = m (b - t Bz)` for `k = -m t`. -/
theorem kpar_scale (m t : ℝ) (Bz b : ℝ → ℝ) (r : ℝ) :
    kpar m (-(m * t)) Bz b r = m * (b r - t * Bz r) := by
  unfold kpar; ring

/-- `μ² = m² (1 + t² r²)` for `k = -m t`. -/
theorem muSq_scale (m t r : ℝ) : muSq m (-(m * t)) r = m ^ 2 * (1 + t ^ 2 * r ^ 2) := by
  unfold muSq; ring

/-- The shear coefficient does not depend on `m` at fixed `t = -k/m`. -/
theorem coefF_scale {m : ℝ} (hm : m ≠ 0) (t : ℝ) (Bz b : ℝ → ℝ) (r : ℝ) :
    coefF m (-(m * t)) Bz b r = r ^ 3 * (b r - t * Bz r) ^ 2 / (1 + t ^ 2 * r ^ 2) := by
  have hK : 1 + t ^ 2 * r ^ 2 ≠ 0 := by positivity
  unfold coefF
  rw [kpar_scale, muSq_scale]
  field_simp

/-- The potential coefficient at fixed `t = -k/m`: only the term `m² r F̂²` depends on
`m`. -/
theorem coefG_scale {m : ℝ} (hm : m ≠ 0) (μ₀ t : ℝ) (p' Bz b : ℝ → ℝ) (r : ℝ) :
    coefG μ₀ m (-(m * t)) p' Bz b r =
      2 * t ^ 2 * r ^ 2 * (μ₀ * p' r) / (1 + t ^ 2 * r ^ 2) +
        (m ^ 2 - 1 / (1 + t ^ 2 * r ^ 2)) * r * (b r - t * Bz r) ^ 2 +
        2 * t ^ 2 * r ^ 3 * (t ^ 2 * Bz r ^ 2 - b r ^ 2) / (1 + t ^ 2 * r ^ 2) ^ 2 := by
  have hK : 1 + t ^ 2 * r ^ 2 ≠ 0 := by positivity
  unfold coefG
  rw [kpar_scale, muSq_scale]
  field_simp

/-- `g` increases with `m²` at fixed `t`: the difference is `(m² - m₀²) r F̂²`. -/
theorem coefG_scale_sub {m m₀ : ℝ} (hm : m ≠ 0) (hm₀ : m₀ ≠ 0) (μ₀ t : ℝ)
    (p' Bz b : ℝ → ℝ) (r : ℝ) :
    coefG μ₀ m (-(m * t)) p' Bz b r - coefG μ₀ m₀ (-(m₀ * t)) p' Bz b r =
      (m ^ 2 - m₀ ^ 2) * r * (b r - t * Bz r) ^ 2 := by
  rw [coefG_scale hm, coefG_scale hm₀]; ring

/-- **Monotonicity in `m` (scaling argument, general profiles).** If the mode
`(m₀, k₀ = -m₀ t)` is stable, so is every `(m, -m t)` with `m² ≥ m₀²`. -/
theorem modeStable_mono_m {μ₀ a m₀ m t : ℝ} {p' Bz b : ℝ → ℝ} (hm₀ : m₀ ≠ 0)
    (hm : m₀ ^ 2 ≤ m ^ 2) (ha : 0 ≤ a) (hp : ContinuousOn p' (uIcc 0 a))
    (hBz : ContinuousOn Bz (uIcc 0 a)) (hb : ContinuousOn b (uIcc 0 a))
    (h : ModeStable μ₀ a m₀ (-(m₀ * t)) p' Bz b) : ModeStable μ₀ a m (-(m * t)) p' Bz b := by
  have hm0 : m ≠ 0 := by
    rintro rfl; have := pow_pos (abs_pos.mpr hm₀) 2; rw [sq_abs] at this; nlinarith
  intro ξ ξ' hξ hξa
  have hf : coefF m (-(m * t)) Bz b = coefF m₀ (-(m₀ * t)) Bz b := by
    funext r; rw [coefF_scale hm0, coefF_scale hm₀]
  rw [hf]
  refine le_trans (h ξ ξ' hξ hξa) (newcombForm_mono_g ha hξ (coefF_continuousOn hm₀ hBz hb)
    (coefG_continuousOn hm₀ hp hBz hb) (coefG_continuousOn hm0 hp hBz hb) fun r hr => ?_)
  rw [uIcc_of_le ha] at hr
  have := coefG_scale_sub hm0 hm₀ μ₀ t p' Bz b r
  have : 0 ≤ (m ^ 2 - m₀ ^ 2) * r * (b r - t * Bz r) ^ 2 := by
    have := hr.1; have : 0 ≤ m ^ 2 - m₀ ^ 2 := by linarith
    positivity
  linarith

/-! ## The analytic Picone certificate for the example -/

/-- `q(r) = -2 + 5r² - r⁴`, so that `S' = 2 r q`. -/
@[expose] def qq (r : ℝ) : ℝ := -2 + 5 * r ^ 2 - r ^ 4

/-- `q'(r) = 10 r - 4 r³`. -/
@[expose] def dqq (r : ℝ) : ℝ := 10 * r - 4 * r ^ 3

/-- `σ = 1/(1 + t² r²)`. -/
@[expose] def sig (t r : ℝ) : ℝ := (1 + t ^ 2 * r ^ 2)⁻¹

/-- Normalized bending factor `F̂ = b - t Bz` (`F = m F̂` for `k = -m t`). -/
@[expose] def Fh (t r : ℝ) : ℝ := bθ r - t * Bz r

/-- Companion factor `Ĝ = b + t Bz`, with `F̂ Ĝ = b² - t² S`. -/
@[expose] def Gh (t r : ℝ) : ℝ := bθ r + t * Bz r

/-- `φ₁ = 1 + t q/Bz`, so that `F̂' = -r φ₁`. -/
@[expose] def phi1 (t r : ℝ) : ℝ := 1 + t * qq r / Bz r

/-- `φ₁' = t (q' S - r q²)/Bz³`. -/
@[expose] def dphi1 (t r : ℝ) : ℝ := t * (dqq r * S r - r * qq r ^ 2) / Bz r ^ 3

/-- Picone function `φ = ½ σ r⁴ F̂ φ₁ = -½ σ r³ F̂ F̂'`. -/
@[expose] def picPhi (t r : ℝ) : ℝ := 1 / 2 * sig t r * r ^ 4 * Fh t r * phi1 t r

/-- Its derivative `h = φ'`. -/
@[expose] def picH (t r : ℝ) : ℝ :=
  -(t ^ 2 * r ^ 5 * sig t r ^ 2 * Fh t r * phi1 t r) + 2 * sig t r * r ^ 3 * Fh t r * phi1 t r -
    1 / 2 * sig t r * r ^ 5 * phi1 t r ^ 2 + 1 / 2 * sig t r * r ^ 4 * Fh t r * dphi1 t r

/-- Cross coefficient `B` of the residual quadratic form. -/
@[expose] def Bt (t r : ℝ) : ℝ :=
  -2 * t ^ 2 * sig t r * Gh t r + t ^ 2 * r ^ 2 * sig t r * phi1 t r - 2 * phi1 t r -
    1 / 2 * (r * dphi1 t r)

/-- Diagonal coefficient `a = φ₁²/4 - 4t²` (Suydam margin in this normalization). -/
@[expose] def aa (t r : ℝ) : ℝ := 1 / 4 * phi1 t r ^ 2 - 4 * t ^ 2

section deriv
variable {t r : ℝ}

theorem S'_eq (r : ℝ) : S' r = 2 * r * qq r := by unfold S' qq; ring

theorem Bz_pos (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 < Bz r := by linarith [Bz_ge h0 h1]

theorem hasDerivAt_Bz (h0 : 0 ≤ r) (h1 : r ≤ 1) : HasDerivAt Bz (r * qq r / Bz r) r := by
  have hS : S r ≠ 0 := by linarith [S_ge h0 h1]
  refine ((S_hasDerivAt r).sqrt hS).congr_deriv ?_
  rw [S'_eq]
  change 2 * r * qq r / (2 * Real.sqrt (S r)) = r * qq r / Real.sqrt (S r)
  have := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (S_ge h0 h1))
  field_simp

theorem hasDerivAt_sig (t r : ℝ) : HasDerivAt (sig t) (-2 * t ^ 2 * r * sig t r ^ 2) r := by
  have hK : 1 + t ^ 2 * r ^ 2 ≠ 0 := by positivity
  refine ((((hasDerivAt_pow 2 r).const_mul (t ^ 2)).const_add 1).inv hK).congr_deriv ?_
  unfold sig
  field_simp
  push_cast
  ring

theorem hasDerivAt_bθ (r : ℝ) : HasDerivAt bθ (-r) r := by
  refine (((hasDerivAt_pow 2 r).div_const 2).const_sub 1).congr_deriv ?_
  push_cast; ring

theorem hasDerivAt_Fh (h0 : 0 ≤ r) (h1 : r ≤ 1) : HasDerivAt (Fh t) (-r * phi1 t r) r := by
  refine ((hasDerivAt_bθ r).sub ((hasDerivAt_Bz h0 h1).const_mul t)).congr_deriv ?_
  have := Bz_pos h0 h1
  unfold phi1
  field_simp
  ring

theorem hasDerivAt_qq (r : ℝ) : HasDerivAt qq (dqq r) r := by
  refine ((((hasDerivAt_pow 2 r).const_mul 5).const_add (-2)).sub
    (hasDerivAt_pow 4 r)).congr_deriv ?_
  unfold dqq; push_cast; ring

theorem hasDerivAt_phi1 (h0 : 0 ≤ r) (h1 : r ≤ 1) : HasDerivAt (phi1 t) (dphi1 t r) r := by
  have hB := Bz_pos h0 h1
  refine ((((hasDerivAt_qq r).const_mul t).div (hasDerivAt_Bz h0 h1) hB.ne').const_add
    1).congr_deriv ?_
  unfold dphi1
  rw [← Bz_sq h0 h1]
  field_simp

theorem hasDerivAt_picPhi (h0 : 0 ≤ r) (h1 : r ≤ 1) : HasDerivAt (picPhi t) (picH t r) r := by
  refine (((((hasDerivAt_sig t r).const_mul (1 / 2)).mul (hasDerivAt_pow 4 r)).mul
    (hasDerivAt_Fh (t := t) h0 h1)).mul (hasDerivAt_phi1 (t := t) h0 h1)).congr_deriv ?_
  unfold picH; simp only [Pi.mul_apply]; push_cast; ring

theorem continuousOn_phi1 (t : ℝ) : ContinuousOn (phi1 t) (Icc 0 1) := by
  unfold phi1
  exact continuousOn_const.add ((continuousOn_const.mul (by unfold qq; fun_prop)).div
    continuous_Bz.continuousOn fun r hr => (Bz_pos hr.1 hr.2).ne')

theorem continuousOn_dphi1 (t : ℝ) : ContinuousOn (dphi1 t) (Icc 0 1) := by
  unfold dphi1
  exact (continuousOn_const.mul (by unfold dqq S qq; fun_prop)).div
    (continuous_Bz.pow 3).continuousOn fun r hr => pow_ne_zero 3 (Bz_pos hr.1 hr.2).ne'

theorem continuous_sig (t : ℝ) : Continuous (sig t) := by
  unfold sig
  exact Continuous.inv₀ (by fun_prop) fun r => by positivity

theorem continuous_Fh (t : ℝ) : Continuous (Fh t) := by
  unfold Fh; exact continuous_bθ.sub (continuous_const.mul continuous_Bz)

theorem continuousOn_picH (t : ℝ) : ContinuousOn (picH t) (Icc 0 1) := by
  have h1 := continuousOn_phi1 t
  have h2 := continuousOn_dphi1 t
  have h3 := (continuous_sig t).continuousOn (s := Icc (0 : ℝ) 1)
  have h4 := (continuous_Fh t).continuousOn (s := Icc (0 : ℝ) 1)
  unfold picH
  fun_prop

end deriv

/-! ## Algebraic identities -/

section identities
variable {μ₀ m t r : ℝ}

theorem sig_pos (t r : ℝ) : 0 < sig t r := by unfold sig; positivity

theorem sig_le_one (t r : ℝ) : sig t r ≤ 1 := by
  unfold sig
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (t * r)])

/-- `f = σ r³ F̂²`. -/
theorem coefF_eq (hm : m ≠ 0) (t r : ℝ) :
    coefF m (-(m * t)) Bz bθ r = sig t r * r ^ 3 * Fh t r ^ 2 := by
  rw [coefF_scale hm]; unfold sig Fh; ring

/-- `g = -4t²r⁵σ + (m² - σ) r F̂² - 2t²r³σ² F̂ Ĝ` for the example. -/
theorem coefG_eq (hμ : μ₀ ≠ 0) (hm : m ≠ 0) (t r : ℝ) :
    coefG μ₀ m (-(m * t)) (pressure' μ₀) Bz bθ r =
      -4 * t ^ 2 * r ^ 5 * sig t r + (m ^ 2 - sig t r) * r * Fh t r ^ 2 -
        2 * t ^ 2 * r ^ 3 * sig t r ^ 2 * Fh t r * Gh t r := by
  rw [coefG_scale hm, mu_pressure' hμ]
  unfold sig Fh Gh
  have hK : 1 + t ^ 2 * r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Key identity.** The Picone residual `g - φ' - φ²/f` (written without division)
is `r (σ a r⁴ + σ B r² F̂ + (m² - σ) F̂²)`. -/
theorem key_identity (hμ : μ₀ ≠ 0) (hm : m ≠ 0) (t r : ℝ) :
    coefG μ₀ m (-(m * t)) (pressure' μ₀) Bz bθ r - picH t r -
        1 / 4 * sig t r * r ^ 5 * phi1 t r ^ 2 =
      r * (sig t r * aa t r * (r ^ 2) ^ 2 + sig t r * Bt t r * r ^ 2 * Fh t r +
        (m ^ 2 - sig t r) * Fh t r ^ 2) := by
  rw [coefG_eq hμ hm]
  unfold picH Bt aa
  ring

end identities

/-! ## Interval bounds -/

section bounds
variable {t r : ℝ}

theorem qq_bounds (h0 : 0 ≤ r) (h1 : r ≤ 1) : -2 ≤ qq r ∧ qq r ≤ 2 := by
  unfold qq
  have hu0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hu1 : r ^ 2 ≤ 1 := by nlinarith
  constructor <;> nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]

theorem phi1_bounds (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 5) :
    429 / 469 ≤ phi1 t r ∧ phi1 t r ≤ 509 / 469 := by
  have hB := Bz_ge h0 h1
  have hBp := Bz_pos h0 h1
  obtain ⟨hq0, hq1⟩ := qq_bounds h0 h1
  have htq1 : t * qq r ≤ 2 / 5 := by nlinarith
  have htq0 : -(2 / 5) ≤ t * qq r := by nlinarith
  unfold phi1
  constructor
  · have : -(40 / 469) ≤ t * qq r / Bz r := by
      rw [le_div_iff₀ hBp]; nlinarith
    linarith
  · have : t * qq r / Bz r ≤ 40 / 469 := by
      rw [div_le_iff₀ hBp]; nlinarith
    linarith

theorem rdphi1_bounds (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 5) :
    -(1 / 100) ≤ r * dphi1 t r ∧ r * dphi1 t r ≤ 1 / 2 := by
  have hB := Bz_ge h0 h1
  have hBp := Bz_pos h0 h1
  have hB3 : (469 / 100) ^ 3 ≤ Bz r ^ 3 := pow_le_pow_left₀ (by norm_num) hB 3
  obtain ⟨hq0, hq1⟩ := qq_bounds h0 h1
  have hS0 := S_ge h0 h1
  have hS1 := S_le h0 h1
  have hd0 : 0 ≤ dqq r := by
    have : dqq r = r * (10 - 4 * r ^ 2) := by unfold dqq; ring
    rw [this]; exact mul_nonneg h0 (by nlinarith)
  have hd1 : dqq r ≤ 10 := by unfold dqq; nlinarith [pow_nonneg h0 3]
  have hq2 : qq r ^ 2 ≤ 4 := by nlinarith
  -- numerator `N = r (q' S - r q²)` lies in `[-4, 10 · 5.02²]`
  have hN1 : r * (dqq r * S r - r * qq r ^ 2) ≤ 10 * (251 / 50) ^ 2 := by
    have : dqq r * S r ≤ 10 * (251 / 50) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (qq r), mul_nonneg h0 (mul_nonneg h0 (sq_nonneg (qq r))),
      mul_le_mul_of_nonneg_left this h0, mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ S r)]
  have hN0 : -4 ≤ r * (dqq r * S r - r * qq r ^ 2) := by
    have : 0 ≤ r * (dqq r * S r) := mul_nonneg h0 (mul_nonneg hd0 (by linarith))
    have : r * (r * qq r ^ 2) ≤ 4 := by
      have : r * r ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (qq r)]
    nlinarith
  have e : r * dphi1 t r = t * (r * (dqq r * S r - r * qq r ^ 2)) / Bz r ^ 3 := by
    unfold dphi1; ring
  rw [e]
  have hB3p : 0 < Bz r ^ 3 := by positivity
  constructor
  · rw [le_div_iff₀ hB3p]; nlinarith
  · rw [div_le_iff₀ hB3p]; nlinarith

theorem Gh_bounds (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 5) :
    0 ≤ Gh t r ∧ Gh t r ≤ 501 / 250 := by
  have hB := Bz_le h0 h1
  have hBp := Bz_pos h0 h1
  have hb := bθ_bounds h0 h1
  unfold Gh
  constructor
  · nlinarith
  · nlinarith

/-- **Discriminant bound.** For `0 ≤ t ≤ 1/5` and `r ∈ [0, 1]`: `B² ≤ 192 a` and `a ≥ 0`. -/
theorem disc_bound (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 5) :
    0 ≤ aa t r ∧ Bt t r ^ 2 ≤ 192 * aa t r := by
  obtain ⟨hp0, hp1⟩ := phi1_bounds h0 h1 ht0 ht1
  obtain ⟨hv0, hv1⟩ := rdphi1_bounds h0 h1 ht0 ht1
  obtain ⟨hG0, hG1⟩ := Gh_bounds h0 h1 ht0 ht1
  have hs0 := sig_pos t r
  have hs1 := sig_le_one t r
  have ht2 : t ^ 2 ≤ 1 / 25 := by nlinarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have ha : 9 ≤ 192 * aa t r := by
    unfold aa; nlinarith
  -- bounds on the four terms of `B`
  have e1 : 0 ≤ t ^ 2 * sig t r * Gh t r := by positivity
  have e1' : t ^ 2 * sig t r * Gh t r ≤ 1 / 25 * (501 / 250) := by
    have : sig t r * Gh t r ≤ 501 / 250 := by nlinarith
    calc t ^ 2 * sig t r * Gh t r = t ^ 2 * (sig t r * Gh t r) := by ring
      _ ≤ 1 / 25 * (501 / 250) := by
          apply mul_le_mul ht2 this (by positivity) (by norm_num)
  have e2 : 0 ≤ t ^ 2 * r ^ 2 * sig t r * phi1 t r := by
    have := sq_nonneg t; have := sq_nonneg r; have : 0 ≤ phi1 t r := by linarith
    positivity
  have e2' : t ^ 2 * r ^ 2 * sig t r * phi1 t r ≤ 1 / 25 * (509 / 469) := by
    have hsp : sig t r * phi1 t r ≤ 509 / 469 := by nlinarith
    have htr : t ^ 2 * r ^ 2 ≤ 1 / 25 := by nlinarith [sq_nonneg t]
    calc t ^ 2 * r ^ 2 * sig t r * phi1 t r = (t ^ 2 * r ^ 2) * (sig t r * phi1 t r) := by ring
      _ ≤ 1 / 25 * (509 / 469) :=
          mul_le_mul htr hsp (by nlinarith) (by norm_num)
  have hBlo : -(2581 / 1000) ≤ Bt t r := by unfold Bt; nlinarith
  have hBhi : Bt t r ≤ 0 := by unfold Bt; nlinarith
  refine ⟨by linarith, ?_⟩
  nlinarith

/-- **Residual nonnegativity.** For `0 ≤ t ≤ 1/5`, `r ∈ [0, 1]` and `m² ≥ 49`, the Picone
residual quadratic form is nonnegative. -/
theorem residual_nonneg {m : ℝ} (hm : 49 ≤ m ^ 2) (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 5) :
    0 ≤ r * (sig t r * aa t r * (r ^ 2) ^ 2 + sig t r * Bt t r * r ^ 2 * Fh t r +
        (m ^ 2 - sig t r) * Fh t r ^ 2) := by
  obtain ⟨ha, hdisc⟩ := disc_bound h0 h1 ht0 ht1
  have hs0 := sig_pos t r
  have hs1 := sig_le_one t r
  set σ := sig t r
  set A := m ^ 2 - σ
  set X := Fh t r
  set Y := r ^ 2
  set a := aa t r
  set B := Bt t r
  have hA : 48 ≤ A := by simp only [A]; linarith
  have hgap : 0 ≤ 4 * A * a - σ * B ^ 2 := by
    have : σ * B ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg B]
    nlinarith
  have key : 4 * A * (σ * a * Y ^ 2 + σ * B * Y * X + A * X ^ 2) =
      (2 * A * X + σ * Y * B) ^ 2 + σ * Y ^ 2 * (4 * A * a - σ * B ^ 2) := by ring
  have hq : 0 ≤ σ * a * Y ^ 2 + σ * B * Y * X + A * X ^ 2 := by
    have : 0 ≤ 4 * A * (σ * a * Y ^ 2 + σ * B * Y * X + A * X ^ 2) := by
      rw [key]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) (by linarith : (0 : ℝ) < 4 * A)
  exact mul_nonneg h0 hq

end bounds

/-! ## Stability theorems -/

/-- Sanity: the Picone function vanishes on the axis (free axis value in `picone_lower`). -/
theorem picPhi_zero (t : ℝ) : picPhi t 0 = 0 := by simp [picPhi]

/-- Sanity: `σ = 1` at `t = 0`. -/
theorem sig_zero (r : ℝ) : sig 0 r = 1 := by simp [sig]

/-- No resonance for `t ≥ 1/5`: `F̂ ≤ -(18/55) r²` on `[0, 1]` (so `F̂ < 0` off the
axis). -/
theorem Fh_le_of_ge {t r : ℝ} (ht : 1 / 5 ≤ t) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Fh t r ≤ -(18 / 55) * r ^ 2 := by
  have hB := Bz_ge h0 h1
  have hB' := Bz_le h0 h1
  have hb := bθ_bounds h0 h1
  have hSq := Bz_sq h0 h1
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hD : 18 * r ^ 2 ≤ Bz r ^ 2 - 25 * bθ r ^ 2 := by
    rw [hSq]; unfold S bθ
    nlinarith [pow_nonneg (sq_nonneg r) 2, pow_nonneg (sq_nonneg r) 3,
      mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr2),
      mul_nonneg (pow_nonneg (sq_nonneg r) 2) (sub_nonneg.mpr hr2)]
  have h5 : 18 * r ^ 2 / 11 ≤ Bz r - 5 * bθ r := by
    rw [div_le_iff₀ (by norm_num)]
    have hp : 0 < Bz r + 5 * bθ r := by linarith
    have hle : Bz r + 5 * bθ r ≤ 11 := by linarith
    have hnn : 0 ≤ Bz r - 5 * bθ r := by
      by_contra hneg; push Not at hneg; nlinarith [sq_nonneg r]
    nlinarith [mul_le_mul_of_nonneg_left hle hnn]
  unfold Fh
  nlinarith

/-- Sanity: the residual is nonnegative even at a resonant surface (`F̂ = 0`), where it
reduces to Suydam's margin `σ a r⁵ ≥ 0`. -/
theorem residual_at_resonance {t r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 5) : 0 ≤ r * (sig t r * aa t r * (r ^ 2) ^ 2) := by
  have := (disc_bound h0 h1 ht0 ht1).1
  have := sig_pos t r
  positivity

/-- **Resonant band.** For `0 ≤ t ≤ 1/5` and `m² ≥ 49`, the mode `(m, k = -m t)` is stable:
the analytic Picone function `picPhi` certifies it through `picone_lower`. -/
theorem stable_band {μ₀ m t : ℝ} (hμ : μ₀ ≠ 0) (hm : 49 ≤ m ^ 2) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 5) : ModeStable μ₀ 1 m (-(m * t)) (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  intro ξ ξ' hξ hξ1
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  refine picone_lower (fL := coefF m (-(m * t)) Bz bθ)
    (gL := coefG μ₀ m (-(m * t)) (pressure' μ₀) Bz bθ) (φ := picPhi t) (h := picH t)
    zero_le_one hξ (picPhi_zero t) hξ1 (coefF_cont hm0 _) (coefG_cont hm0 _)
    (fun x hx => by rw [hI] at hx; exact hasDerivAt_picPhi hx.1 hx.2)
    (hI ▸ continuousOn_picH t)
    (fun x hx => by rw [hI] at hx; exact coefF_nonneg hm0 Bz bθ hx.1)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_ ?_
  · intro x hx
    rw [hI] at hx
    have hk := key_identity hμ hm0 t x
    have hr := residual_nonneg hm hx.1 hx.2 ht0 ht1
    have : 0 ≤ 1 / 4 * sig t x * x ^ 5 * phi1 t x ^ 2 := by
      have := sig_pos t x; have := hx.1; positivity
    linarith
  · intro x hx
    rw [hI] at hx
    have hk := key_identity hμ hm0 t x
    have hr := residual_nonneg hm hx.1 hx.2 ht0 ht1
    rw [coefF_eq hm0]
    have e : picPhi t x ^ 2 =
        sig t x * x ^ 3 * Fh t x ^ 2 * (1 / 4 * sig t x * x ^ 5 * phi1 t x ^ 2) := by
      unfold picPhi; ring
    rw [e]
    have hc : 0 ≤ sig t x * x ^ 3 * Fh t x ^ 2 := by
      have := sig_pos t x; have := hx.1; positivity
    apply mul_le_mul_of_nonneg_left _ hc
    linarith

/-- **Non-resonant band.** For `1/5 ≤ t ≤ 1/2` and `m² ≥ 49`, `g ≥ 0` on `[0, 1]`, so the
mode `(m, -m t)` is stable without a certificate. -/
theorem stable_nonresonant {μ₀ m t : ℝ} (hμ : μ₀ ≠ 0) (hm : 49 ≤ m ^ 2) (ht0 : 1 / 5 ≤ t)
    (ht1 : t ≤ 1 / 2) : ModeStable μ₀ 1 m (-(m * t)) (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg hm0 zero_le_one fun r hr => ?_
  obtain ⟨h0, h1⟩ := hr
  rw [coefG_eq hμ hm0]
  have hs0 := sig_pos t r
  have hs1 := sig_le_one t r
  have hF := Fh_le_of_ge ht0 h0 h1
  have hFn : Fh t r ≤ 0 := by nlinarith [sq_nonneg r]
  have hF2 : (18 / 55) ^ 2 * (r ^ 2) ^ 2 ≤ Fh t r ^ 2 := by nlinarith [sq_nonneg r]
  have hG : 0 ≤ Gh t r := by
    have := Bz_pos h0 h1; have := (bθ_bounds h0 h1).1
    unfold Gh; nlinarith
  have t2 : 0 ≤ -(2 * t ^ 2 * r ^ 3 * sig t r ^ 2 * Fh t r * Gh t r) := by
    have : 0 ≤ 2 * t ^ 2 * r ^ 3 * sig t r ^ 2 * Gh t r := by positivity
    nlinarith
  have hA : 48 ≤ m ^ 2 - sig t r := by linarith
  have h4 : 4 * t ^ 2 * sig t r ≤ 1 := by nlinarith
  have t1 : 4 * t ^ 2 * r ^ 5 * sig t r ≤ (m ^ 2 - sig t r) * r * Fh t r ^ 2 := by
    have hr4 : 0 ≤ r * (r ^ 2) ^ 2 := by positivity
    have : 4 * t ^ 2 * sig t r * (r * (r ^ 2) ^ 2) ≤ 1 * (r * (r ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_right h4 hr4
    have : (r * (r ^ 2) ^ 2) ≤ (m ^ 2 - sig t r) * r * Fh t r ^ 2 := by
      have := mul_le_mul hA hF2 (by positivity) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left this h0]
    nlinarith
  linarith

/-- **Every real wavenumber for `m² ≥ 49`.** For the screw-pinch example, every mode with
`m² ≥ 49` and every real `k` is stable in Newcomb's reduced energy. -/
theorem stable_high_m {μ₀ m k : ℝ} (hμ : μ₀ ≠ 0) (hm : 49 ≤ m ^ 2) :
    ModeStable μ₀ 1 m k (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  rcases le_or_gt 0 (k * m) with hkm | hkm
  · exact stable_of_same_sign hμ (by linarith) hkm
  · set t := -k / m with ht
    have hk : k = -(m * t) := by rw [ht]; field_simp
    have htpos : 0 < t := by
      have : t = -(k * m) / m ^ 2 := by rw [ht]; field_simp
      rw [this]; exact div_pos (by linarith) (by positivity)
    rw [hk]
    rcases le_or_gt t (1 / 5) with h1 | h1
    · exact stable_band hμ hm htpos.le h1
    rcases le_or_gt t (1 / 2) with h2 | h2
    · exact stable_nonresonant hμ hm h1.le h2
    · refine stable_of_large_k hμ (by linarith) ?_
      have : (-(m * t)) ^ 2 = m ^ 2 * t ^ 2 := by ring
      rw [this]
      have : 1 / 4 ≤ t ^ 2 := by nlinarith
      nlinarith

/-- Integer modes with `|m| ≥ 7`: every `n`. -/
theorem stable_high_m_int {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (h7 : 7 ≤ |m|) :
    ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  refine stable_high_m hμ ?_
  have : (49 : ℤ) ≤ m ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
  exact_mod_cast this

/-- **The previously open family.** Every mode with `|m| ≥ 7`, `k m < 0` and
`5 n² < 9 m²` is stable (the gap left by `ScrewPinchModes.stable_uniform`). -/
theorem stable_open_family {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (h7 : 7 ≤ |m|)
    (_hkm : n * m < 0) (_hn : 5 * n ^ 2 < 9 * m ^ 2) :
    ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ :=
  stable_high_m_int hμ m n h7

/-- **Main result: the full mode spectrum.** For the screw-pinch example, every mode
`(m, n)` with `m ≠ 0` (`k = n/R₀`, `R₀ = 4` metres) is stable in Newcomb's reduced energy with
a conducting wall at the plasma edge. -/
theorem stable_all_modes {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (hm : m ≠ 0) :
    ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  rcases le_or_gt |m| 6 with h | h
  · exact stable_low_m hμ m n hm h
  · exact stable_high_m_int hμ m n (by omega)

/-- **Screw-pinch headline with force balance (audit finding MA-L6).** For `μ₀ > 0` the
example is an equilibrium and is stable to every mode with `m ≠ 0`, for the same profiles:
(1) the cylindrical radial force balance `RadialBalance` holds on `(0, 1]` for the pressure
`p = (1 − r⁴)/(2μ₀)` with derivative `p' = pressure' μ₀`, the azimuthal field `Bθ` and
`S = Bz²` (`ScrewPinchExample.balance`); (2) the mode-stability profiles are these same fields,
`Bz = √S` with `Bz² = S` and `bθ = Bθ/r` on `(0, 1]`; (3) every `(m, n)` with `m ≠ 0` is
Newcomb-stable (`stable_all_modes`, Newcomb's reduced form) with the pressure gradient
`pressure' μ₀` of the balanced pressure. -/
theorem stable_all_modes_equilibrium {μ₀ : ℝ} (hμ : 0 < μ₀) :
    PlasmaLean.Equilibrium.ScrewPinch.RadialBalance μ₀ 1 (pressure μ₀) Bθ S (pressure' μ₀)
        Bθ' S' ∧
      (∀ r ∈ Ioc (0 : ℝ) 1, Bz r ^ 2 = S r ∧ bθ r = Bθ r / r) ∧
      ∀ m n : ℤ, m ≠ 0 → ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ :=
  ⟨balance hμ, fun _ hr => ⟨Bz_sq hr.1.le hr.2, bθ_eq hr.1.ne'⟩,
    fun m n hm => stable_all_modes hμ.ne' m n hm⟩

/-- Under a supplied Newcomb reduction for the mode `(m, n)`, the full ideal-MHD energy of
every admissible displacement is nonnegative, for every `m ≠ 0`. -/
theorem energy_nonneg_all_modes {Disp : Type*} {W : Disp → ℝ} {admissible : Disp → Prop}
    {radial : Disp → (ℝ → ℝ) × (ℝ → ℝ)} {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (hm : m ≠ 0)
    (hR : NewcombReduction W admissible radial μ₀ 1 m ((n : ℝ) / 4) (pressure' μ₀) Bz bθ)
    (d : Disp) (hd : admissible d) : 0 ≤ W d :=
  hR.energy_nonneg (stable_all_modes hμ m n hm) d hd

/-! ## Cylindrical Mercier criterion for the example -/

/-- The example satisfies the cylindrical Mercier criterion `D_I ≤ 0` on every surface
(equivalent to Suydam, `PlasmaLean.Stability.Mercier.mercierStableOn_iff`). -/
theorem mercier_cyl_stable {μ₀ : ℝ} (hμ : 0 < μ₀) :
    PlasmaLean.Stability.Mercier.MercierStableOn μ₀ 1 (pressure' μ₀) Bθ S Bθ' S' :=
  (PlasmaLean.Stability.Mercier.mercierStableOn_iff hμ
    (fun r hr => lt_of_lt_of_le (by norm_num) (S_ge hr.1.le hr.2))
    (fun r hr => (shear_pos hr.1 hr.2).ne')).mpr (suydam_stable hμ)

/-- The example (with `R₀ = 4` metres, `q ≥ 5/4`) also satisfies the large-aspect-ratio
Mercier criterion built from its own safety factor. -/
theorem mercier_tokamak_example {μ₀ r : ℝ} (hμ : 0 < μ₀) (h0 : 0 < r) (h1 : r ≤ 1) :
    0 ≤ PlasmaLean.Stability.Mercier.mercierTokamak μ₀ 4 (pressure' μ₀) Bθ S Bθ' S' r := by
  refine PlasmaLean.Stability.Mercier.mercierTokamak_of_safetyFactor_ge_one hμ h0.le
    (by linarith [S_ge h0.le h1]) (by linarith [safetyFactor_ge h0 h1]) ?_
  unfold pressure'
  have := pow_pos h0 3
  have : 0 < 2 / μ₀ := by positivity
  nlinarith

end PlasmaLean.Design.ScrewPinchModesHighM
