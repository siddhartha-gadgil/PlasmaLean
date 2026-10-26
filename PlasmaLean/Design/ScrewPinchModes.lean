/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.ScrewPinchModes
public import PlasmaLean.Design.ScrewPinchExample
public import PlasmaLean.Certificates.PolyInterval
public import PlasmaLean.Certificates.EvalCert

/-!
# Mode-by-mode ideal-MHD stability of the screw-pinch example

The exact screw pinch of `PlasmaLean.Design.ScrewPinchExample` (`a = 1 m`, `R₀ = 4 m`,
`Bz² = S(r)`, `Bθ = r - r³/2`, `μ₀ p' = -2r³`, `⟨β⟩ = 2/75`) is tested against Newcomb's
reduced energy (`PlasmaLean.Stability.ScrewPinchModes`) for the periodic modes
`exp i(mθ + n z/R₀)`, i.e. `k = n/4`, with a conducting wall at the plasma edge.

**Removing the square root.** `Bz = √S` enters `F = k Bz + m b` (`b = Bθ/r = 1 - r²/2`).
With `G = k Bz - m b` we have `F G = D := k² S - m² b²` (polynomial). Using
`469/100 ≤ √S ≤ 251/50` on `[0, 1]`:

* if `k m < 0` (the helicity that can resonate, since `q > 0`), `|G| ≤ E := (251/50)|k| + |m| b`,
  so `F² ≥ D²/E²`;
* if `k m ≥ 0`, `|F| ≥ E⁻ := (469/100)|k| + |m| b`.

This gives polynomial-rational lower bounds `fL ≤ f`, `gL ≤ g` (`coefF_lower`,
`coefG_lower_neg`, `coefG_lower_pos`). Stability then follows either from `gL ≥ 0`
(an exact polynomial check of its numerator) or from a Picone certificate
`φ = D ψ` with a polynomial `ψ` found numerically outside Lean, checked through two
exact polynomial inequalities `P1 ≥ 0` (gap) and `P2 ≥ 0` (discriminant, after dividing
by `D²`, which is what lets `φ` vanish at irrational resonant surfaces). All checks are
explicit evaluation certificates (`eval_cert`, `Certificates/EvalCert`) of the sound checker
`PlasmaLean.Certificates.QPoly.checkOn`.

**Uniform families (all real `k`).**

* `stable_of_large_k`: `9 m² ≤ 80 k²` (with `m² ≥ 1`): `g ≥ 0`;
* `stable_of_same_sign`: `k m ≥ 0` and `m² ≥ 4`: `g ≥ 0`;
* `k = 0`: `zero_k_stable`.

**Main result.** `stable_low_m`: every mode with `1 ≤ |m| ≤ 6` and every integer `n` is
stable (`ModeStable`, i.e. Newcomb's reduced `δW ≥ 0` for every C¹ radial displacement
vanishing at the wall), using 27 explicit certificates (9 Picone, 18 potential checks)
for the finitely many remaining `(m, n)`. `stable_of_large_k` and `stable_of_same_sign`
also cover every `|m| ≥ 7` mode with `k m ≥ 0` or `5 n² ≥ 9 m²`.

**Open.** Modes with `|m| ≥ 7`, `k m < 0` and `5 n² < 9 m²` (which include resonant
surfaces) are not certified: the numerical margins shrink with `m` (localized, Suydam-like
modes) and a uniform-in-`m` argument is not available here. The `m = 0` mode is excluded
(compressibility). The Newcomb reduction itself is supplied
(`NewcombReduction`); free-boundary, resistive, kinetic and toroidal effects are not
treated. This is a current-carrying screw pinch, not a stellarator.
-/
public section

noncomputable section
namespace PlasmaLean.Design.ScrewPinchModes
open Set PlasmaLean.Stability PlasmaLean.Stability.ScrewPinchModes
open PlasmaLean.Design.ScrewPinchExample PlasmaLean.Certificates.QPoly

/-- Axial field `Bz = √S`. -/
@[expose] def Bz (r : ℝ) : ℝ := Real.sqrt (S r)

/-- Azimuthal field over radius, `b = Bθ / r = 1 - r²/2` (regular at the axis). -/
@[expose] def bθ (r : ℝ) : ℝ := 1 - r ^ 2 / 2

/-- Consistency with the equilibrium profile: `b = Bθ / r` off the axis. -/
theorem bθ_eq {r : ℝ} (hr : r ≠ 0) : bθ r = Bθ r / r := by
  unfold bθ Bθ; field_simp

/-! ## Profile bounds -/

theorem S_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : S r ≤ (251 / 50) ^ 2 := by
  unfold S
  have hu0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hu1 : r ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1), mul_nonneg (mul_nonneg hu0 hu0)
    (sub_nonneg.mpr hu1), pow_nonneg h0 4, pow_nonneg h0 6]

theorem Bz_sq {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : Bz r ^ 2 = S r :=
  Real.sq_sqrt (by linarith [S_ge h0 h1])

theorem Bz_ge {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 469 / 100 ≤ Bz r :=
  Real.le_sqrt_of_sq_le (by nlinarith [S_ge h0 h1])

theorem Bz_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : Bz r ≤ 251 / 50 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, S_le h0 h1⟩

theorem bθ_bounds {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 1 / 2 ≤ bθ r ∧ bθ r ≤ 1 := by
  unfold bθ; constructor <;> nlinarith

theorem continuous_Bz : Continuous Bz := by
  unfold Bz S; fun_prop

theorem continuous_bθ : Continuous bθ := by
  unfold bθ; fun_prop

theorem continuous_pressure' (μ₀ : ℝ) : Continuous (pressure' μ₀) := by
  unfold pressure'; fun_prop

/-! ## Exact polynomial data -/

/-- `S` as a coefficient list. -/
@[expose] def Spoly : List ℚ := [25, 0, -2, 0, 5 / 2, 0, -1 / 3]

/-- `b = 1 - r²/2`. -/
@[expose] def bpoly : List ℚ := [1, 0, -1 / 2]

/-- `μ₀ p' = -2 r³`. -/
@[expose] def mupPoly : List ℚ := [0, 0, 0, -2]

/-- `μ² = m² + k² r²`. -/
@[expose] def Kpoly (m k : ℚ) : List ℚ := [m ^ 2, 0, k ^ 2]

/-- `D = F G = k² S - m² b²`. -/
@[expose] def Dpoly (m k : ℚ) : List ℚ :=
  add (scale (k ^ 2) Spoly) (scale (-m ^ 2) (mul bpoly bpoly))

/-- Upper bound `E = (251/50)|k| + |m| b` for `|G|` when `k m < 0`. -/
@[expose] def Epoly (m k : ℚ) : List ℚ := add [251 / 50 * |k|] (scale |m| bpoly)

/-- Lower bound `E⁻ = (469/100)|k| + |m| b` for `|F|` when `k m ≥ 0`. -/
@[expose] def Fpoly (m k : ℚ) : List ℚ := add [469 / 100 * |k|] (scale |m| bpoly)

/-- Numerator of `gL` for `k m < 0` (denominator `μ⁴ E²`). -/
@[expose] def GNneg (m k : ℚ) : List ℚ :=
  add (add (scale (2 * k ^ 2) (mul (mul [0, 0, 1] mupPoly)
      (mul (Kpoly m k) (mul (Epoly m k) (Epoly m k)))))
    (mul (mul (add (Kpoly m k) [-1]) [0, 1]) (mul (mul (Dpoly m k) (Dpoly m k)) (Kpoly m k))))
    (scale (2 * k ^ 2) (mul [0, 0, 0, 1] (mul (Dpoly m k) (mul (Epoly m k) (Epoly m k)))))

/-- Numerator of `gL` for `k m ≥ 0` (denominator `μ⁴`). -/
@[expose] def GNpos (m k : ℚ) : List ℚ :=
  add (add (scale (2 * k ^ 2) (mul (mul [0, 0, 1] mupPoly) (Kpoly m k)))
    (mul (mul (add (Kpoly m k) [-1]) [0, 1]) (mul (mul (Fpoly m k) (Fpoly m k)) (Kpoly m k))))
    (scale (2 * k ^ 2) (mul [0, 0, 0, 1] (Dpoly m k)))

/-- Gap polynomial `P1 = μ⁴E² (gL - φ')` for `φ = D ψ`. -/
@[expose] def P1poly (m k : ℚ) (ψ : List ℚ) : List ℚ :=
  add (GNneg m k) (scale (-1) (mul (deriv (mul (Dpoly m k) ψ))
    (mul (mul (Kpoly m k) (Kpoly m k)) (mul (Epoly m k) (Epoly m k)))))

/-- Discriminant polynomial `P2 = r³ P1 - ψ² μ⁶ E⁴`. -/
@[expose] def P2poly (m k : ℚ) (ψ : List ℚ) : List ℚ :=
  add (mul [0, 0, 0, 1] (P1poly m k ψ)) (scale (-1) (mul (mul ψ ψ)
    (mul (mul (Kpoly m k) (mul (Kpoly m k) (Kpoly m k)))
      (mul (mul (Epoly m k) (Epoly m k)) (mul (Epoly m k) (Epoly m k))))))

theorem eval_Spoly (r : ℝ) : eval Spoly r = S r := by
  simp [Spoly, S]; ring

theorem eval_bpoly (r : ℝ) : eval bpoly r = bθ r := by
  simp [bpoly, bθ]; ring

theorem eval_mup (r : ℝ) : eval mupPoly r = -2 * r ^ 3 := by
  simp [mupPoly]; ring

theorem eval_Kpoly (m k : ℚ) (r : ℝ) : eval (Kpoly m k) r = muSq m k r := by
  simp [Kpoly, muSq]; ring

theorem eval_Dpoly (m k : ℚ) (r : ℝ) :
    eval (Dpoly m k) r = (k : ℝ) ^ 2 * S r - (m : ℝ) ^ 2 * bθ r ^ 2 := by
  simp [Dpoly, eval_Spoly, eval_bpoly]; ring

theorem eval_Epoly (m k : ℚ) (r : ℝ) :
    eval (Epoly m k) r = 251 / 50 * |(k : ℝ)| + |(m : ℝ)| * bθ r := by
  simp [Epoly, eval_bpoly]

theorem eval_Fpoly (m k : ℚ) (r : ℝ) :
    eval (Fpoly m k) r = 469 / 100 * |(k : ℝ)| + |(m : ℝ)| * bθ r := by
  simp [Fpoly, eval_bpoly]

theorem eval_GNneg (m k : ℚ) (r : ℝ) : eval (GNneg m k) r =
    2 * (k : ℝ) ^ 2 * r ^ 2 * (-2 * r ^ 3) * muSq m k r * eval (Epoly m k) r ^ 2 +
    (muSq m k r - 1) * r * eval (Dpoly m k) r ^ 2 * muSq m k r +
    2 * (k : ℝ) ^ 2 * r ^ 3 * eval (Dpoly m k) r * eval (Epoly m k) r ^ 2 := by
  simp only [GNneg, eval_add, eval_mul, eval_scale, eval_mup, eval_Kpoly]
  simp; ring

theorem eval_GNpos (m k : ℚ) (r : ℝ) : eval (GNpos m k) r =
    2 * (k : ℝ) ^ 2 * r ^ 2 * (-2 * r ^ 3) * muSq m k r +
    (muSq m k r - 1) * r * eval (Fpoly m k) r ^ 2 * muSq m k r +
    2 * (k : ℝ) ^ 2 * r ^ 3 * eval (Dpoly m k) r := by
  simp only [GNpos, eval_add, eval_mul, eval_scale, eval_mup, eval_Kpoly]
  simp; ring

theorem eval_P1poly (m k : ℚ) (ψ : List ℚ) (r : ℝ) : eval (P1poly m k ψ) r =
    eval (GNneg m k) r - eval (deriv (mul (Dpoly m k) ψ)) r *
      (muSq m k r ^ 2 * eval (Epoly m k) r ^ 2) := by
  simp only [P1poly, eval_add, eval_mul, eval_scale, eval_Kpoly]
  push_cast; ring

theorem eval_P2poly (m k : ℚ) (ψ : List ℚ) (r : ℝ) : eval (P2poly m k ψ) r =
    r ^ 3 * eval (P1poly m k ψ) r -
      eval ψ r ^ 2 * (muSq m k r ^ 3 * eval (Epoly m k) r ^ 4) := by
  simp only [P2poly, eval_add, eval_mul, eval_scale, eval_Kpoly]
  simp; ring

/-! ## Lower bounds for the Newcomb coefficients -/

section bounds
variable {μ₀ : ℝ} {m k : ℚ} {r : ℝ}

/-- `E > 0` on the plasma radius. -/
theorem E_pos (hm : m ≠ 0) (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 < eval (Epoly m k) r := by
  rw [eval_Epoly]
  have := (bθ_bounds h0 h1).1
  have : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  positivity

/-- `|G| ≤ E` when `k m < 0`, i.e. `(k Bz - m b)² ≤ E²`. -/
theorem G_sq_le (hkm : k * m < 0) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ((k : ℝ) * Bz r - m * bθ r) ^ 2 ≤ eval (Epoly m k) r ^ 2 := by
  have hkmR : (k : ℝ) * m < 0 := by exact_mod_cast hkm
  have hab : |(k : ℝ)| * |(m : ℝ)| = -((k : ℝ) * m) := by
    rw [← abs_mul, abs_of_neg hkmR]
  have hs0 := Bz_ge h0 h1
  have hs1 := Bz_le h0 h1
  have hb := (bθ_bounds h0 h1).1
  have hG : ((k : ℝ) * Bz r - m * bθ r) ^ 2 = (|(k : ℝ)| * Bz r + |(m : ℝ)| * bθ r) ^ 2 := by
    have e1 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
    have e2 : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
    linear_combination (Bz r) ^ 2 * e1 + bθ r ^ 2 * e2 - 2 * Bz r * bθ r * hab
  rw [hG, eval_Epoly]
  have hk := abs_nonneg (k : ℝ)
  have hmm := abs_nonneg (m : ℝ)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hs1 hk]

/-- `|F| ≥ E⁻` when `k m ≥ 0`. -/
theorem F_sq_ge (hkm : 0 ≤ k * m) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    eval (Fpoly m k) r ^ 2 ≤ kpar m k Bz bθ r ^ 2 := by
  have hkmR : 0 ≤ (k : ℝ) * m := by exact_mod_cast hkm
  have hab : |(k : ℝ)| * |(m : ℝ)| = (k : ℝ) * m := by
    rw [← abs_mul, abs_of_nonneg hkmR]
  have hs0 := Bz_ge h0 h1
  have hb := (bθ_bounds h0 h1).1
  have hF : kpar m k Bz bθ r ^ 2 = (|(k : ℝ)| * Bz r + |(m : ℝ)| * bθ r) ^ 2 := by
    unfold kpar
    have e1 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
    have e2 : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
    linear_combination (Bz r) ^ 2 * e1 + bθ r ^ 2 * e2 - 2 * Bz r * bθ r * hab
  rw [hF, eval_Fpoly]
  have hk := abs_nonneg (k : ℝ)
  have hmm := abs_nonneg (m : ℝ)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hs0 hk]

/-- `F G = D`. -/
theorem FG_eq (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    kpar m k Bz bθ r * ((k : ℝ) * Bz r - m * bθ r) = eval (Dpoly m k) r := by
  rw [eval_Dpoly, ← Bz_sq h0 h1]; unfold kpar; ring

/-- `D² ≤ F² E²` when `k m < 0`. -/
theorem D_sq_le (hkm : k * m < 0) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    eval (Dpoly m k) r ^ 2 ≤ kpar m k Bz bθ r ^ 2 * eval (Epoly m k) r ^ 2 := by
  rw [← FG_eq h0 h1, mul_pow]
  exact mul_le_mul_of_nonneg_left (G_sq_le hkm h0 h1) (sq_nonneg _)

/-- Lower bound `fL = r³ D² / (μ² E²) ≤ f` when `k m < 0`. -/
theorem coefF_lower (hm : m ≠ 0) (hkm : k * m < 0) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    r ^ 3 * eval (Dpoly m k) r ^ 2 / (muSq m k r * eval (Epoly m k) r ^ 2) ≤
      coefF m k Bz bθ r := by
  have hK := muSq_pos (m := (m : ℝ)) (by exact_mod_cast hm) k r
  have hE := E_pos (k := k) hm h0 h1
  unfold coefF
  rw [div_le_div_iff₀ (by positivity) hK]
  have := D_sq_le hkm h0 h1
  have h3 : 0 ≤ r ^ 3 * muSq m k r := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this h3]

/-- Lower bound `gL = GNneg / (μ⁴ E²) ≤ g` when `k m < 0`. -/
theorem coefG_lower_neg (hμ : μ₀ ≠ 0) (hm : 1 ≤ m ^ 2) (hkm : k * m < 0) (h0 : 0 ≤ r)
    (h1 : r ≤ 1) :
    eval (GNneg m k) r / (muSq m k r ^ 2 * eval (Epoly m k) r ^ 2) ≤
      coefG μ₀ m k (pressure' μ₀) Bz bθ r := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  have hmR : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hm
  have hK := muSq_pos (m := (m : ℝ)) (by exact_mod_cast hm0) k r
  have hK1 := one_le_muSq hmR k r
  have hE := E_pos (k := k) hm0 h0 h1
  have hD := D_sq_le hkm h0 h1
  have key : coefG μ₀ m k (pressure' μ₀) Bz bθ r -
      eval (GNneg m k) r / (muSq m k r ^ 2 * eval (Epoly m k) r ^ 2) =
      (muSq m k r - 1) * r * (kpar m k Bz bθ r ^ 2 * eval (Epoly m k) r ^ 2 -
        eval (Dpoly m k) r ^ 2) / (muSq m k r * eval (Epoly m k) r ^ 2) := by
    have hK' := hK.ne'
    have hE' := hE.ne'
    rw [eval_GNneg]
    unfold coefG
    rw [mu_pressure' hμ, Bz_sq h0 h1, eval_Dpoly]
    field_simp
    ring
  have : 0 ≤ (muSq m k r - 1) * r * (kpar m k Bz bθ r ^ 2 * eval (Epoly m k) r ^ 2 -
        eval (Dpoly m k) r ^ 2) / (muSq m k r * eval (Epoly m k) r ^ 2) := by
    have : 0 ≤ muSq m k r - 1 := by linarith
    have : 0 ≤ kpar m k Bz bθ r ^ 2 * eval (Epoly m k) r ^ 2 - eval (Dpoly m k) r ^ 2 := by
      linarith
    positivity
  linarith

/-- Lower bound `gL = GNpos / μ⁴ ≤ g` when `k m ≥ 0`. -/
theorem coefG_lower_pos (hμ : μ₀ ≠ 0) (hm : 1 ≤ m ^ 2) (hkm : 0 ≤ k * m) (h0 : 0 ≤ r)
    (h1 : r ≤ 1) :
    eval (GNpos m k) r / muSq m k r ^ 2 ≤ coefG μ₀ m k (pressure' μ₀) Bz bθ r := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  have hmR : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hm
  have hK := muSq_pos (m := (m : ℝ)) (by exact_mod_cast hm0) k r
  have hK1 := one_le_muSq hmR k r
  have hF := F_sq_ge hkm h0 h1
  have key : coefG μ₀ m k (pressure' μ₀) Bz bθ r - eval (GNpos m k) r / muSq m k r ^ 2 =
      (muSq m k r - 1) * r * (kpar m k Bz bθ r ^ 2 - eval (Fpoly m k) r ^ 2) / muSq m k r := by
    have hK' := hK.ne'
    rw [eval_GNpos]
    unfold coefG
    rw [mu_pressure' hμ, Bz_sq h0 h1, eval_Dpoly]
    field_simp
    ring
  have : 0 ≤ (muSq m k r - 1) * r * (kpar m k Bz bθ r ^ 2 - eval (Fpoly m k) r ^ 2) /
      muSq m k r := by
    have : 0 ≤ muSq m k r - 1 := by linarith
    have : 0 ≤ kpar m k Bz bθ r ^ 2 - eval (Fpoly m k) r ^ 2 := by linarith
    positivity
  linarith

end bounds

/-! ## Certificate-to-stability bridges -/

theorem coefF_cont {m k : ℝ} (hm : m ≠ 0) (s : Set ℝ) : ContinuousOn (coefF m k Bz bθ) s :=
  coefF_continuousOn hm continuous_Bz.continuousOn continuous_bθ.continuousOn

theorem coefG_cont {μ₀ m k : ℝ} (hm : m ≠ 0) (s : Set ℝ) :
    ContinuousOn (coefG μ₀ m k (pressure' μ₀) Bz bθ) s :=
  coefG_continuousOn hm (continuous_pressure' μ₀).continuousOn continuous_Bz.continuousOn
    continuous_bθ.continuousOn

/-- An accepted potential check for `k m < 0` proves stability. -/
theorem stable_of_check_neg {μ₀ : ℝ} (hμ : μ₀ ≠ 0) {m k : ℚ} (hm : 1 ≤ m ^ 2)
    (hkm : k * m < 0) {pts : List ℚ} (h : checkOn (GNneg m k) 0 0 1 pts = true) :
    ModeStable μ₀ 1 m k (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg (by exact_mod_cast hm0) zero_le_one fun r hr => ?_
  refine le_trans ?_ (coefG_lower_neg hμ hm hkm hr.1 hr.2)
  have hc := checkOn_sound h r (by simpa using hr)
  have := E_pos (k := k) hm0 hr.1 hr.2
  have := muSq_pos (m := (m : ℝ)) (by exact_mod_cast hm0) k r
  apply div_nonneg (by simpa using hc) (by positivity)

/-- An accepted potential check for `k m ≥ 0` proves stability. -/
theorem stable_of_check_pos {μ₀ : ℝ} (hμ : μ₀ ≠ 0) {m k : ℚ} (hm : 1 ≤ m ^ 2)
    (hkm : 0 ≤ k * m) {pts : List ℚ} (h : checkOn (GNpos m k) 0 0 1 pts = true) :
    ModeStable μ₀ 1 m k (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg (by exact_mod_cast hm0) zero_le_one fun r hr => ?_
  refine le_trans ?_ (coefG_lower_pos hμ hm hkm hr.1 hr.2)
  have hc := checkOn_sound h r (by simpa using hr)
  apply div_nonneg (by simpa using hc) (by positivity)

/-- Accepted Picone checks (`φ = D ψ`, `ψ(0) = 0`) prove stability when `k m < 0`. -/
theorem stable_of_picone {μ₀ : ℝ} (hμ : μ₀ ≠ 0) {m k : ℚ} (hm : 1 ≤ m ^ 2)
    (hkm : k * m < 0) {ψ pts₁ pts₂ : List ℚ} (hψ : eval ψ 0 = 0)
    (h₁ : checkOn (P1poly m k ψ) 0 0 1 pts₁ = true)
    (h₂ : checkOn (P2poly m k ψ) 0 0 1 pts₂ = true) :
    ModeStable μ₀ 1 m k (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  have hm0R : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  intro ξ ξ' hξ hξ1
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  refine picone_lower (fL := fun r => r ^ 3 * eval (Dpoly m k) r ^ 2 /
      (muSq m k r * eval (Epoly m k) r ^ 2))
    (gL := fun r => eval (GNneg m k) r / (muSq m k r ^ 2 * eval (Epoly m k) r ^ 2))
    (φ := eval (mul (Dpoly m k) ψ)) (h := eval (deriv (mul (Dpoly m k) ψ)))
    zero_le_one hξ (by simp [hψ]) hξ1 (coefF_cont hm0R _) (coefG_cont hm0R _)
    (fun x _ => hasDerivAt_eval _ x) (continuous_eval _).continuousOn ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [hI] at hr
    have := E_pos (k := k) hm0 hr.1 hr.2
    have := muSq_pos hm0R k r
    have := hr.1
    positivity
  · intro r hr; rw [hI] at hr; exact coefF_lower hm0 hkm hr.1 hr.2
  · intro r hr; rw [hI] at hr; exact coefG_lower_neg hμ hm hkm hr.1 hr.2
  · intro r hr
    rw [hI] at hr
    have hE := E_pos (k := k) hm0 hr.1 hr.2
    have hK := muSq_pos hm0R k r
    have hP := checkOn_sound h₁ r (by simpa using hr)
    rw [eval_P1poly] at hP
    simp only [Rat.cast_zero] at hP
    rw [le_div_iff₀ (by positivity)]
    linarith
  · intro r hr
    rw [hI] at hr
    have hE := E_pos (k := k) hm0 hr.1 hr.2
    have hK := muSq_pos hm0R k r
    have hP := checkOn_sound h₂ r (by simpa using hr)
    rw [eval_P2poly, eval_P1poly] at hP
    simp only [Rat.cast_zero] at hP
    set E := eval (Epoly m k) r
    set D := eval (Dpoly m k) r
    set K := muSq m k r
    set G := eval (GNneg m k) r
    set h := eval (deriv (mul (Dpoly m k) ψ)) r
    have key : r ^ 3 * D ^ 2 / (K * E ^ 2) * (G / (K ^ 2 * E ^ 2) - h) =
        r ^ 3 * D ^ 2 * (G - h * (K ^ 2 * E ^ 2)) / (K ^ 3 * E ^ 4) := by
      field_simp
    simp only [eval_mul]
    change (D * eval ψ r) ^ 2 ≤ r ^ 3 * D ^ 2 / (K * E ^ 2) * (G / (K ^ 2 * E ^ 2) - h)
    rw [key, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg D) hP]

/-! ## Uniform families -/

/-- **Large wavenumber.** If `9 m² ≤ 80 k²` (and `m² ≥ 1`), then `g ≥ 0` on the whole
radius, so the mode is stable. Real `k`; no certificate needed. -/
theorem stable_of_large_k {μ₀ m k : ℝ} (hμ : μ₀ ≠ 0) (hm : 1 ≤ m ^ 2)
    (hk : 9 * m ^ 2 ≤ 80 * k ^ 2) : ModeStable μ₀ 1 m k (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg hm0 zero_le_one fun r hr => ?_
  obtain ⟨h0, h1⟩ := hr
  have hK := muSq_pos hm0 k r
  have hK1 := one_le_muSq hm k r
  have hSg := S_ge h0 h1
  have hb := bθ_bounds h0 h1
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hr4 : r ^ 4 ≤ 1 := by nlinarith
  have key : coefG μ₀ m k (pressure' μ₀) Bz bθ r =
      (muSq m k r - 1) * r * kpar m k Bz bθ r ^ 2 / muSq m k r +
        2 * k ^ 2 * r ^ 3 * (k ^ 2 * S r - m ^ 2 * bθ r ^ 2 - 2 * r ^ 2 * muSq m k r) /
          muSq m k r ^ 2 := by
    unfold coefG
    rw [mu_pressure' hμ, Bz_sq h0 h1]
    field_simp
    ring
  have hlin : 0 ≤ k ^ 2 * S r - m ^ 2 * bθ r ^ 2 - 2 * r ^ 2 * muSq m k r := by
    have hKd : muSq m k r = m ^ 2 + k ^ 2 * r ^ 2 := rfl
    rw [hKd]
    have h20 : 20 ≤ S r - 2 * r ^ 4 := by nlinarith
    have h94 : bθ r ^ 2 + 2 * r ^ 2 ≤ 9 / 4 := by
      unfold bθ; nlinarith
    have hk2 := sq_nonneg k
    have hm2 := sq_nonneg m
    nlinarith [mul_le_mul_of_nonneg_left h20 hk2, mul_le_mul_of_nonneg_left h94 hm2]
  rw [key]
  have : 0 ≤ muSq m k r - 1 := by linarith
  positivity

/-- **Same helicity.** If `k m ≥ 0` and `m² ≥ 4`, then `g ≥ 0`, so the mode is stable,
for every real `k`. -/
theorem stable_of_same_sign {μ₀ m k : ℝ} (hμ : μ₀ ≠ 0) (hm : 4 ≤ m ^ 2) (hkm : 0 ≤ k * m) :
    ModeStable μ₀ 1 m k (pressure' μ₀) Bz bθ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg hm0 zero_le_one fun r hr => ?_
  obtain ⟨h0, h1⟩ := hr
  have hK := muSq_pos hm0 k r
  have hSg := S_ge h0 h1
  have hb := bθ_bounds h0 h1
  have hs0 : 0 ≤ Bz r := Real.sqrt_nonneg _
  have hKd : muSq m k r = m ^ 2 + k ^ 2 * r ^ 2 := rfl
  have hK4 : 4 ≤ muSq m k r := by rw [hKd]; nlinarith [sq_nonneg (k * r)]
  have hF : k ^ 2 * S r ≤ kpar m k Bz bθ r ^ 2 := by
    unfold kpar
    rw [← Bz_sq h0 h1]
    nlinarith [mul_nonneg (mul_nonneg hkm hs0) (by linarith [hb.1] : (0 : ℝ) ≤ bθ r),
      sq_nonneg (m * bθ r)]
  have key : muSq m k r ^ 2 * coefG μ₀ m k (pressure' μ₀) Bz bθ r =
      (muSq m k r - 1) * r * kpar m k Bz bθ r ^ 2 * muSq m k r +
        2 * k ^ 2 * r ^ 3 * (k ^ 2 * S r - m ^ 2 * bθ r ^ 2) -
        4 * k ^ 2 * r ^ 5 * muSq m k r := by
    unfold coefG
    rw [mu_pressure' hμ, Bz_sq h0 h1]
    field_simp
    ring
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 ≤ muSq m k r ^ 2 * coefG μ₀ m k (pressure' μ₀) Bz bθ r := by
    rw [key]
    have hk2 := sq_nonneg k
    have hmb : m ^ 2 * bθ r ^ 2 ≤ muSq m k r := by
      rw [hKd]; nlinarith [sq_nonneg (k * r), mul_le_mul_of_nonneg_left
        (by nlinarith : bθ r ^ 2 ≤ 1) (sq_nonneg m)]
    have t1 : (muSq m k r - 1) * r * (22 * k ^ 2) * muSq m k r ≤
        (muSq m k r - 1) * r * kpar m k Bz bθ r ^ 2 * muSq m k r := by
      have : 0 ≤ (muSq m k r - 1) * r := by nlinarith
      have : 22 * k ^ 2 ≤ kpar m k Bz bθ r ^ 2 := by nlinarith
      have h' := mul_le_mul_of_nonneg_left this (by nlinarith : 0 ≤ (muSq m k r - 1) * r)
      nlinarith
    have t2 : -(2 * k ^ 2 * r * muSq m k r) ≤
        2 * k ^ 2 * r ^ 3 * (k ^ 2 * S r - m ^ 2 * bθ r ^ 2) := by
      have a1 : 0 ≤ k ^ 2 * r ^ 3 * (k ^ 2 * S r) := by positivity
      have a2 : k ^ 2 * r ^ 3 * (m ^ 2 * bθ r ^ 2) ≤ k ^ 2 * r * muSq m k r := by
        have : r ^ 3 ≤ r := by nlinarith
        calc k ^ 2 * r ^ 3 * (m ^ 2 * bθ r ^ 2) ≤ k ^ 2 * r ^ 3 * muSq m k r :=
              mul_le_mul_of_nonneg_left hmb (by positivity)
          _ ≤ k ^ 2 * r * muSq m k r := by
              have := mul_le_mul_of_nonneg_left this hk2
              nlinarith
      nlinarith
    have t3 : 4 * k ^ 2 * r ^ 5 * muSq m k r ≤ 4 * k ^ 2 * r * muSq m k r := by
      have : r ^ 5 ≤ r := by nlinarith [pow_le_one₀ h0 h1 (n := 4)]
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 4 * k ^ 2 * muSq m k r)
      nlinarith
    have t4 : 0 ≤ k ^ 2 * r * muSq m k r * (22 * (muSq m k r - 1) - 6) := by
      have : 0 ≤ 22 * (muSq m k r - 1) - 6 := by linarith
      positivity
    nlinarith
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hpos

/-! ## Numerically found certificate data (checked exactly below) -/

/-- Subdivision for the `(m, n) = (1, 1)` potential check. -/
@[expose] def ptsG1p1 : List ℚ :=
  [1]

/-- Picone certificate `ψ` for `(m, n) = (1, -1)` (found numerically). -/
@[expose] def psi1n1 : List ℚ :=
  [0, 0, (-7249 / 65536), (-106179 / 65536), 953323 / 65536, (-2548761 / 32768),
    11905943 / 65536, (-12258021 / 65536), 4466601 / 65536]

/-- Subdivisions for the `(1, -1)` gap and discriminant checks. -/
@[expose] def pts11n1 : List ℚ :=
  [1 / 16, 1 / 8, 1 / 4, 1 / 2, 1]

@[expose] def pts21n1 : List ℚ :=
  [1 / 16, 1 / 8, 1 / 4, 3 / 8, 1 / 2, 3 / 4, 7 / 8, 1]

/-- Picone certificate `ψ` for `(m, n) = (2, -1)` (found numerically). -/
@[expose] def psi2n1 : List ℚ :=
  [0, 0, (-3459 / 65536), (-115 / 65536), 415 / 16384, (-845 / 32768), 381 / 8192,
    (-2321 / 65536), 495 / 32768]

/-- Subdivisions for the `(2, -1)` gap and discriminant checks. -/
@[expose] def pts12n1 : List ℚ :=
  [1 / 2, 1]

@[expose] def pts22n1 : List ℚ :=
  [1 / 2, 1]

/-- Subdivision for the `(m, n) = (2, -2)` potential check. -/
@[expose] def ptsG2n2 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (3, -1)` potential check. -/
@[expose] def ptsG3n1 : List ℚ :=
  [1 / 2, 3 / 4, 7 / 8, 15 / 16, 31 / 32, 1]

/-- Picone certificate `ψ` for `(m, n) = (3, -2)` (found numerically). -/
@[expose] def psi3n2 : List ℚ :=
  [0, 0, (-1269 / 65536), (-3 / 16384), 887 / 32768, (-287 / 65536), 1139 / 65536,
    (-351 / 32768), 521 / 65536]

/-- Subdivisions for the `(3, -2)` gap and discriminant checks. -/
@[expose] def pts13n2 : List ℚ :=
  [1 / 2, 3 / 4, 1]

@[expose] def pts23n2 : List ℚ :=
  [1 / 2, 1]

/-- Subdivision for the `(m, n) = (3, -3)` potential check. -/
@[expose] def ptsG3n3 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (3, -4)` potential check. -/
@[expose] def ptsG3n4 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (4, -1)` potential check. -/
@[expose] def ptsG4n1 : List ℚ :=
  [1 / 2, 3 / 4, 7 / 8, 1]

/-- Picone certificate `ψ` for `(m, n) = (4, -2)` (found numerically). -/
@[expose] def psi4n2 : List ℚ :=
  [0, 0, 2327 / 32768, (-64887 / 65536), 99881 / 32768, (-215385 / 65536), (-14227 / 16384),
    259599 / 65536, (-32061 / 16384)]

/-- Subdivisions for the `(4, -2)` gap and discriminant checks. -/
@[expose] def pts14n2 : List ℚ :=
  [1 / 16, 1 / 8, 1 / 4, 1 / 2, 3 / 4, 7 / 8, 1]

@[expose] def pts24n2 : List ℚ :=
  [1 / 16, 1 / 8, 3 / 16, 1 / 4, 3 / 8, 1 / 2, 5 / 8, 3 / 4, 7 / 8, 1]

/-- Picone certificate `ψ` for `(m, n) = (4, -3)` (found numerically). -/
@[expose] def psi4n3 : List ℚ :=
  [0, 0, 163 / 16384, (-2099 / 16384), 18021 / 65536, 7971 / 32768, (-41875 / 65536),
    (-42957 / 65536), 51005 / 65536]

/-- Subdivisions for the `(4, -3)` gap and discriminant checks. -/
@[expose] def pts14n3 : List ℚ :=
  [1 / 8, 1 / 4, 5 / 16, 3 / 8, 1 / 2, 1]

@[expose] def pts24n3 : List ℚ :=
  [1 / 16, 1 / 8, 3 / 16, 7 / 32, 1 / 4, 5 / 16, 3 / 8, 1 / 2, 3 / 4, 7 / 8, 1]

/-- Subdivision for the `(m, n) = (4, -4)` potential check. -/
@[expose] def ptsG4n4 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (4, -5)` potential check. -/
@[expose] def ptsG4n5 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (5, -1)` potential check. -/
@[expose] def ptsG5n1 : List ℚ :=
  [1 / 2, 3 / 4, 1]

/-- Picone certificate `ψ` for `(m, n) = (5, -2)` (found numerically). -/
@[expose] def psi5n2 : List ℚ :=
  [0, 0, 5193 / 65536, (-23323 / 16384), 320545 / 65536, (-36873 / 8192), (-281023 / 65536),
    294693 / 32768, (-247159 / 65536)]

/-- Subdivisions for the `(5, -2)` gap and discriminant checks. -/
@[expose] def pts15n2 : List ℚ :=
  [1 / 16, 1 / 8, 1 / 4, 1 / 2, 5 / 8, 3 / 4, 7 / 8, 1]

@[expose] def pts25n2 : List ℚ :=
  [1 / 16, 1 / 8, 5 / 32, 3 / 16, 13 / 64, 7 / 32, 1 / 4, 1 / 2, 5 / 8, 11 / 16, 3 / 4,
    13 / 16, 7 / 8, 1]

/-- Picone certificate `ψ` for `(m, n) = (5, -3)` (found numerically). -/
@[expose] def psi5n3 : List ℚ :=
  [0, 0, (-737 / 32768), 26239 / 65536, (-46467 / 32768), 65805 / 65536, 75889 / 65536,
    (-28975 / 32768), (-24559 / 65536)]

/-- Subdivisions for the `(5, -3)` gap and discriminant checks. -/
@[expose] def pts15n3 : List ℚ :=
  [1 / 4, 3 / 8, 1 / 2, 5 / 8, 11 / 16, 3 / 4, 1]

@[expose] def pts25n3 : List ℚ :=
  [1 / 16, 1 / 8, 1 / 4, 3 / 8, 7 / 16, 1 / 2, 9 / 16, 5 / 8, 11 / 16, 3 / 4, 7 / 8, 1]

/-- Subdivision for the `(m, n) = (5, -4)` potential check. -/
@[expose] def ptsG5n4 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (5, -5)` potential check. -/
@[expose] def ptsG5n5 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (5, -6)` potential check. -/
@[expose] def ptsG5n6 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (6, -1)` potential check. -/
@[expose] def ptsG6n1 : List ℚ :=
  [1 / 2, 3 / 4, 1]

/-- Subdivision for the `(m, n) = (6, -2)` potential check. -/
@[expose] def ptsG6n2 : List ℚ :=
  [1 / 2, 3 / 4, 7 / 8, 15 / 16, 1]

/-- Picone certificate `ψ` for `(m, n) = (6, -3)` (found numerically). -/
@[expose] def psi6n3 : List ℚ :=
  [0, 0, 2915 / 65536, (-37707 / 32768), 45675 / 8192, (-138251 / 16384), (-18997 / 32768),
    84185 / 8192, (-378639 / 65536)]

/-- Subdivisions for the `(6, -3)` gap and discriminant checks. -/
@[expose] def pts16n3 : List ℚ :=
  [1 / 16, 1 / 8, 1 / 4, 3 / 8, 1 / 2, 5 / 8, 3 / 4, 13 / 16, 7 / 8, 1]

@[expose] def pts26n3 : List ℚ :=
  [1 / 32, 1 / 16, 3 / 32, 1 / 8, 9 / 64, 5 / 32, 3 / 16, 1 / 4, 3 / 8, 1 / 2, 5 / 8,
    11 / 16, 3 / 4, 13 / 16, 7 / 8, 1]

/-- Picone certificate `ψ` for `(m, n) = (6, -4)` (found numerically). -/
@[expose] def psi6n4 : List ℚ :=
  [0, 0, 1035 / 65536, 2789 / 32768, (-40863 / 32768), 95817 / 32768, (-66281 / 65536),
    (-21857 / 8192), 7577 / 4096]

/-- Subdivisions for the `(6, -4)` gap and discriminant checks. -/
@[expose] def pts16n4 : List ℚ :=
  [1 / 8, 1 / 4, 3 / 8, 1 / 2, 9 / 16, 19 / 32, 5 / 8, 3 / 4, 1]

@[expose] def pts26n4 : List ℚ :=
  [1 / 64, 1 / 32, 1 / 16, 1 / 8, 1 / 4, 5 / 16, 11 / 32, 3 / 8, 13 / 32, 7 / 16, 1 / 2,
    9 / 16, 19 / 32, 5 / 8, 3 / 4, 7 / 8, 15 / 16, 1]

/-- Subdivision for the `(m, n) = (6, -5)` potential check. -/
@[expose] def ptsG6n5 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (6, -6)` potential check. -/
@[expose] def ptsG6n6 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (6, -7)` potential check. -/
@[expose] def ptsG6n7 : List ℚ :=
  [1]

/-- Subdivision for the `(m, n) = (6, -8)` potential check. -/
@[expose] def ptsG6n8 : List ℚ :=
  [1]

/-! ## Explicit certificates for the remaining low-`m` modes -/

/-- The `(m, n) = (1, 1)` mode is stable (potential check). -/
theorem mode_1p1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((1 : ℤ) : ℝ) (((1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_pos (m := 1) (k := (1 / 4 : ℚ)) (pts := ptsG1p1) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (1, -1)` mode is stable (Picone certificate). -/
theorem mode_1n1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((1 : ℤ) : ℝ) (((-1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 1) (k := (-1 / 4 : ℚ)) (ψ := psi1n1) (pts₁ := pts11n1)
    (pts₂ := pts21n1) hμ (by norm_num) (by norm_num) (by simp [psi1n1])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (2, -1)` mode is stable (Picone certificate). -/
theorem mode_2n1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((2 : ℤ) : ℝ) (((-1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 2) (k := (-1 / 4 : ℚ)) (ψ := psi2n1) (pts₁ := pts12n1)
    (pts₂ := pts22n1) hμ (by norm_num) (by norm_num) (by simp [psi2n1])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (2, -2)` mode is stable (potential check). -/
theorem mode_2n2 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((2 : ℤ) : ℝ) (((-2 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 2) (k := (-1 / 2 : ℚ)) (pts := ptsG2n2) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (3, -1)` mode is stable (potential check). -/
theorem mode_3n1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((3 : ℤ) : ℝ) (((-1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 3) (k := (-1 / 4 : ℚ)) (pts := ptsG3n1) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (3, -2)` mode is stable (Picone certificate). -/
theorem mode_3n2 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((3 : ℤ) : ℝ) (((-2 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 3) (k := (-1 / 2 : ℚ)) (ψ := psi3n2) (pts₁ := pts13n2)
    (pts₂ := pts23n2) hμ (by norm_num) (by norm_num) (by simp [psi3n2])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (3, -3)` mode is stable (potential check). -/
theorem mode_3n3 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((3 : ℤ) : ℝ) (((-3 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 3) (k := (-3 / 4 : ℚ)) (pts := ptsG3n3) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (3, -4)` mode is stable (potential check). -/
theorem mode_3n4 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((3 : ℤ) : ℝ) (((-4 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 3) (k := (-1 : ℚ)) (pts := ptsG3n4) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (4, -1)` mode is stable (potential check). -/
theorem mode_4n1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((4 : ℤ) : ℝ) (((-1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 4) (k := (-1 / 4 : ℚ)) (pts := ptsG4n1) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (4, -2)` mode is stable (Picone certificate). -/
theorem mode_4n2 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((4 : ℤ) : ℝ) (((-2 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 4) (k := (-1 / 2 : ℚ)) (ψ := psi4n2) (pts₁ := pts14n2)
    (pts₂ := pts24n2) hμ (by norm_num) (by norm_num) (by simp [psi4n2])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (4, -3)` mode is stable (Picone certificate). -/
theorem mode_4n3 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((4 : ℤ) : ℝ) (((-3 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 4) (k := (-3 / 4 : ℚ)) (ψ := psi4n3) (pts₁ := pts14n3)
    (pts₂ := pts24n3) hμ (by norm_num) (by norm_num) (by simp [psi4n3])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (4, -4)` mode is stable (potential check). -/
theorem mode_4n4 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((4 : ℤ) : ℝ) (((-4 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 4) (k := (-1 : ℚ)) (pts := ptsG4n4) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (4, -5)` mode is stable (potential check). -/
theorem mode_4n5 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((4 : ℤ) : ℝ) (((-5 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 4) (k := (-5 / 4 : ℚ)) (pts := ptsG4n5) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (5, -1)` mode is stable (potential check). -/
theorem mode_5n1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((5 : ℤ) : ℝ) (((-1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 5) (k := (-1 / 4 : ℚ)) (pts := ptsG5n1) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (5, -2)` mode is stable (Picone certificate). -/
theorem mode_5n2 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((5 : ℤ) : ℝ) (((-2 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 5) (k := (-1 / 2 : ℚ)) (ψ := psi5n2) (pts₁ := pts15n2)
    (pts₂ := pts25n2) hμ (by norm_num) (by norm_num) (by simp [psi5n2])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (5, -3)` mode is stable (Picone certificate). -/
theorem mode_5n3 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((5 : ℤ) : ℝ) (((-3 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 5) (k := (-3 / 4 : ℚ)) (ψ := psi5n3) (pts₁ := pts15n3)
    (pts₂ := pts25n3) hμ (by norm_num) (by norm_num) (by simp [psi5n3])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (5, -4)` mode is stable (potential check). -/
theorem mode_5n4 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((5 : ℤ) : ℝ) (((-4 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 5) (k := (-1 : ℚ)) (pts := ptsG5n4) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (5, -5)` mode is stable (potential check). -/
theorem mode_5n5 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((5 : ℤ) : ℝ) (((-5 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 5) (k := (-5 / 4 : ℚ)) (pts := ptsG5n5) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (5, -6)` mode is stable (potential check). -/
theorem mode_5n6 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((5 : ℤ) : ℝ) (((-6 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 5) (k := (-3 / 2 : ℚ)) (pts := ptsG5n6) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -1)` mode is stable (potential check). -/
theorem mode_6n1 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-1 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 6) (k := (-1 / 4 : ℚ)) (pts := ptsG6n1) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -2)` mode is stable (potential check). -/
theorem mode_6n2 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-2 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 6) (k := (-1 / 2 : ℚ)) (pts := ptsG6n2) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -3)` mode is stable (Picone certificate). -/
theorem mode_6n3 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-3 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 6) (k := (-3 / 4 : ℚ)) (ψ := psi6n3) (pts₁ := pts16n3)
    (pts₂ := pts26n3) hμ (by norm_num) (by norm_num) (by simp [psi6n3])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -4)` mode is stable (Picone certificate). -/
theorem mode_6n4 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-4 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_picone (m := 6) (k := (-1 : ℚ)) (ψ := psi6n4) (pts₁ := pts16n4)
    (pts₂ := pts26n4) hμ (by norm_num) (by norm_num) (by simp [psi6n4])
    (by eval_cert) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -5)` mode is stable (potential check). -/
theorem mode_6n5 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-5 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 6) (k := (-5 / 4 : ℚ)) (pts := ptsG6n5) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -6)` mode is stable (potential check). -/
theorem mode_6n6 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-6 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 6) (k := (-3 / 2 : ℚ)) (pts := ptsG6n6) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -7)` mode is stable (potential check). -/
theorem mode_6n7 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-7 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 6) (k := (-7 / 4 : ℚ)) (pts := ptsG6n7) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-- The `(m, n) = (6, -8)` mode is stable (potential check). -/
theorem mode_6n8 {μ₀ : ℝ} (hμ : μ₀ ≠ 0) :
    ModeStable μ₀ 1 ((6 : ℤ) : ℝ) (((-8 : ℤ) : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have h := stable_of_check_neg (m := 6) (k := (-2 : ℚ)) (pts := ptsG6n8) hμ (by norm_num)
    (by norm_num) (by eval_cert)
  convert h using 2 <;> norm_num

/-! ## All modes with `1 ≤ |m| ≤ 6` -/

/-- Positive `m`: every integer `n`. -/
theorem stable_pos_m {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (h1 : 1 ≤ m) (h6 : m ≤ 6) :
    ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast h1
    nlinarith
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · by_cases hA : 9 * m ^ 2 ≤ 5 * n ^ 2
    · refine stable_of_large_k hμ hm1 ?_
      have : (9 : ℝ) * (m : ℝ) ^ 2 ≤ 5 * (n : ℝ) ^ 2 := by exact_mod_cast hA
      nlinarith
    · push Not at hA
      interval_cases m
      · have hb : -1 ≤ n := by nlinarith
        rcases (by omega : n = -1) with rfl
        · exact mode_1n1 hμ
      · have hb : -2 ≤ n := by nlinarith
        rcases (by omega : n = -1 ∨ n = -2) with rfl | rfl
        · exact mode_2n1 hμ
        · exact mode_2n2 hμ
      · have hb : -4 ≤ n := by nlinarith
        rcases (by omega : n = -1 ∨ n = -2 ∨ n = -3 ∨ n = -4) with rfl | rfl | rfl | rfl
        · exact mode_3n1 hμ
        · exact mode_3n2 hμ
        · exact mode_3n3 hμ
        · exact mode_3n4 hμ
      · have hb : -5 ≤ n := by nlinarith
        rcases (by omega :
            n = -1 ∨ n = -2 ∨ n = -3 ∨ n = -4 ∨ n = -5) with
          rfl | rfl | rfl | rfl | rfl
        · exact mode_4n1 hμ
        · exact mode_4n2 hμ
        · exact mode_4n3 hμ
        · exact mode_4n4 hμ
        · exact mode_4n5 hμ
      · have hb : -6 ≤ n := by nlinarith
        rcases (by omega :
            n = -1 ∨ n = -2 ∨ n = -3 ∨ n = -4 ∨ n = -5 ∨ n = -6) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · exact mode_5n1 hμ
        · exact mode_5n2 hμ
        · exact mode_5n3 hμ
        · exact mode_5n4 hμ
        · exact mode_5n5 hμ
        · exact mode_5n6 hμ
      · have hb : -8 ≤ n := by nlinarith
        rcases (by omega :
            n = -1 ∨ n = -2 ∨ n = -3 ∨ n = -4 ∨ n = -5 ∨ n = -6 ∨ n = -7 ∨ n = -8) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact mode_6n1 hμ
        · exact mode_6n2 hμ
        · exact mode_6n3 hμ
        · exact mode_6n4 hμ
        · exact mode_6n5 hμ
        · exact mode_6n6 hμ
        · exact mode_6n7 hμ
        · exact mode_6n8 hμ
  · simpa using zero_k_stable (μ₀ := μ₀) (p' := pressure' μ₀) (Bz := Bz) (b := bθ) hm1
      zero_le_one
  · rcases eq_or_lt_of_le h1 with h | h
    · subst h
      rcases eq_or_lt_of_le (show (1 : ℤ) ≤ n by omega) with h' | h'
      · subst h'; exact mode_1p1 hμ
      · refine stable_of_large_k hμ hm1 ?_
        have : (2 : ℝ) ≤ n := by exact_mod_cast h'
        push_cast; nlinarith
    · refine stable_of_same_sign hμ ?_ ?_
      · have : (2 : ℝ) ≤ m := by exact_mod_cast h
        nlinarith
      · have : (0 : ℝ) < n := by exact_mod_cast hn
        have : (0 : ℝ) < m := by exact_mod_cast (show (0 : ℤ) < m by omega)
        positivity

/-- **Main result.** For the screw-pinch example, every mode with `1 ≤ |m| ≤ 6` and every
integer `n` (`k = n/R₀`, `R₀ = 4 m`) is stable in Newcomb's reduced energy, with a
conducting wall at the plasma edge. -/
theorem stable_low_m {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (hm : m ≠ 0) (h6 : |m| ≤ 6) :
    ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  rcases lt_or_gt_of_ne hm with h | h
  · have := stable_pos_m hμ (-m) (-n) (by omega) (by rw [abs_of_neg h] at h6; omega)
    rw [← modeStable_neg]
    convert this using 2 <;> push_cast <;> ring
  · exact stable_pos_m hμ m n (by omega) (by rw [abs_of_pos h] at h6; exact h6)

/-- Every mode with `k m ≥ 0` and `|m| ≥ 2`, or with `5 n² ≥ 9 m²`, is stable for every
`m` (uniform families; the remaining open modes have `|m| ≥ 7`, `k m < 0` and
`5 n² < 9 m²`). -/
theorem stable_uniform {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (m n : ℤ) (hm : m ≠ 0)
    (h : (2 ≤ |m| ∧ 0 ≤ n * m) ∨ 9 * m ^ 2 ≤ 5 * n ^ 2) :
    ModeStable μ₀ 1 (m : ℝ) ((n : ℝ) / 4) (pressure' μ₀) Bz bθ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [sq_nonneg m, Int.one_le_abs hm, sq_abs m]
    exact_mod_cast this
  rcases h with ⟨h2, hs⟩ | hA
  · refine stable_of_same_sign hμ ?_ ?_
    · have : (4 : ℤ) ≤ m ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
      exact_mod_cast this
    · have : (0 : ℝ) ≤ (n : ℝ) * m := by exact_mod_cast hs
      nlinarith
  · refine stable_of_large_k hμ hm1 ?_
    have : (9 : ℝ) * (m : ℝ) ^ 2 ≤ 5 * (n : ℝ) ^ 2 := by exact_mod_cast hA
    nlinarith

end PlasmaLean.Design.ScrewPinchModes
