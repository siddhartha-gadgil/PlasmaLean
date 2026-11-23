/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Period-uniform interface gap in the close-wall cylinder benchmark

Q-30(a), N-44. The plasma Bessel multiplier and exterior Neumann impedance enter through their
stated lower bounds. The dimensionless mode coefficient includes the negative curvature term.
The Fourier energy reduction and the special-function estimates are physical/mathematical
inputs from the periodic-cylinder model.
-/

public section
namespace PlasmaLean.Stability.CylinderInterfaceGap

/-- The wall-radius choice h ≤ 1+s/16 implies the logarithmic wall budget. -/
theorem close_wall {s h : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 4)
    (hw : 1 < h) (hh : h ≤ 1 + s / 16) :
    Real.log h + s * ((h ^ 2 - 1) / 2) / (1 - 3 * s / 4) ≤ s / 8 := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < h)
  have hD : (h ^ 2 - 1) / 2 ≤ s / 15 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 1 + s / 16 + h by linarith),
      mul_nonneg hs.le (sub_nonneg.mpr hsmax)]
  have hterm : s * ((h ^ 2 - 1) / 2) / (1 - 3 * s / 4) ≤ s / 16 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - 3 * s / 4)).mpr
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hD),
      mul_nonneg hs.le (sub_nonneg.mpr hsmax)]
  linarith

private theorem weighted_square (x y q A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (q * x + y) ^ 2 / (q ^ 2 * A + B) ≤ x ^ 2 / A + y ^ 2 / B := by
  have hd : 0 < q ^ 2 * A + B := by positivity
  field_simp
  nlinarith [sq_nonneg (B * x - q * A * y)]

/-- For m ≥ 1 and either axial wave-number sign it suffices to check the least favourable
helicity (m c − κ β)². P and N denote the dimensionless plasma and vacuum coefficients. -/
theorem nonaxisymmetric_floor {s c β m κ ℓ D P N : ℝ}
    (hs : 0 < s) (hsmax : s ≤ 1 / 4) (hc : 0 < c) (hc2 : c ^ 2 = s)
    (hβ : 0 < β) (hβ2 : β ^ 2 = 1 - 3 * s / 4) (hm : 1 ≤ m) (hk : 0 ≤ κ)
    (hℓ : 0 < ℓ) (hD : 0 ≤ D) (hw : ℓ + s * D / β ^ 2 ≤ s / 8)
    (hp : κ ^ 2 / (m + κ ^ 2 / (2 * (m + 1))) ≤ P) (hn : 1 / (m ^ 2 * ℓ + κ ^ 2 * D) ≤ N)
    : s ^ 2 / 8 ≤ P + (m * c - κ * β) ^ 2 * N - s := by
  let A := m ^ 2 + κ ^ 2 / 2
  let B := m ^ 2 * ℓ + κ ^ 2 * D
  have hm0 : 0 < m := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hN : 0 ≤ N := le_trans (by positivity : 0 ≤ 1 / B) hn
  have hden : m + κ ^ 2 / (2 * (m + 1)) ≤ A := by
    have hfrac : κ ^ 2 / (2 * (m + 1)) ≤ κ ^ 2 / 2 := by gcongr; linarith
    dsimp [A]
    nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm)]
  have hP : κ ^ 2 / A ≤ P :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden).trans hp
  have hV : (m * c - κ * β) ^ 2 / B ≤ (m * c - κ * β) ^ 2 * N := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hn (sq_nonneg (m * c - κ * β))
  have budget : s + s ^ 2 / 8 ≤ P + (m * c - κ * β) ^ 2 * N := by
    rcases le_total (κ * β) (m * c) with low | high
    · have ks : κ ^ 2 * β ^ 2 ≤ m ^ 2 * s := by
        simpa [mul_pow, hc2] using pow_le_pow_left₀ (mul_nonneg hk hβ.le) low 2
      have hwall : s * D ≤ (s / 8 - ℓ) * β ^ 2 := (div_le_iff₀ (sq_pos_of_pos hβ)).mp (by linarith)
      have kb : κ ^ 2 * D ≤ m ^ 2 * (s / 8 - ℓ) := by
        apply le_of_mul_le_mul_right (a := β ^ 2) _ (sq_pos_of_pos hβ)
        nlinarith [mul_le_mul_of_nonneg_right ks hD,
          mul_le_mul_of_nonneg_left hwall (sq_nonneg m)]
      have hsum : β ^ 2 * A + B ≤ m ^ 2 * (1 - s / 8) := by
        dsimp [A, B]
        nlinarith [congrArg (m ^ 2 * ·) hβ2]
      have hmarg : (s + s ^ 2 / 8) * (β ^ 2 * A + B) ≤ (m * c) ^ 2 := by
        have hsplus : 0 ≤ s + s ^ 2 / 8 := by positivity
        have hcub : (s + s ^ 2 / 8) * (1 - s / 8) ≤ s := by nlinarith [pow_pos hs 3]
        calc
          _ ≤ (s + s ^ 2 / 8) * (m ^ 2 * (1 - s / 8)) := mul_le_mul_of_nonneg_left hsum hsplus
          _ = m ^ 2 * ((s + s ^ 2 / 8) * (1 - s / 8)) := by ring
          _ ≤ m ^ 2 * s := mul_le_mul_of_nonneg_left hcub (sq_nonneg m)
          _ = _ := by rw [mul_pow, hc2]
      have hd : 0 < β ^ 2 * A + B := by positivity
      have hca := weighted_square κ (m * c - κ * β) β A B hA hB
      rw [show β * κ + (m * c - κ * β) = m * c by ring] at hca
      linarith [(le_div_iff₀ hd).mpr hmarg]
    · have ks : m ^ 2 * s ≤ κ ^ 2 * β ^ 2 := by
        simpa [mul_pow, hc2] using pow_le_pow_left₀ (mul_nonneg hm0.le hc.le) high 2
      have hmarg : s + s ^ 2 / 8 ≤ κ ^ 2 / A := by
        apply (le_div_iff₀ hA).mpr
        dsimp [A]
        have hbound := mul_le_mul_of_nonneg_left ks (show 0 ≤ 1 + s / 8 by positivity)
        nlinarith [congrArg (fun b => κ ^ 2 * b * (1 + s / 8)) hβ2,
          mul_nonneg (sq_nonneg κ) (sq_nonneg s)]
      linarith [mul_nonneg (sq_nonneg (m * c - κ * β)) hN]
  linarith only [budget]

/-- Combining the close-wall floor with the high-frequency estimates gives an interface
gap uniform in the axial period. -/
theorem nonaxisymmetric_gap {s c β m κ ℓ D P N : ℝ}
    (hs : 0 < s) (hsmax : s ≤ 1 / 4) (hc : 0 < c) (hc2 : c ^ 2 = s)
    (hβ : 0 < β) (hβ2 : β ^ 2 = 1 - 3 * s / 4) (hm : 1 ≤ m) (hk : 0 ≤ κ)
    (hℓ : 0 < ℓ) (hD : 0 ≤ D) (hw : ℓ + s * D / β ^ 2 ≤ s / 8)
    (hp : κ ^ 2 / (m + κ ^ 2 / (2 * (m + 1))) ≤ P) (hn : 1 / (m ^ 2 * ℓ + κ ^ 2 * D) ≤ N)
    (hpHigh : κ ^ 2 / (m + κ) ≤ P) (hnHigh : 1 / (m + κ) ≤ N) :
    s ^ 2 / 8 ≤ P + (m * c - κ * β) ^ 2 * N - s ∧
    s ^ 2 / 80 * (1 + m + κ) ≤ P + (m * c - κ * β) ^ 2 * N - s := by
  have floor := nonaxisymmetric_floor hs hsmax hc hc2 hβ hβ2 hm hk hℓ hD hw hp hn
  have budget : s + s ^ 2 / 8 ≤ P + (m * c - κ * β) ^ 2 * N := by linarith only [floor]
  refine ⟨floor, ?_⟩
  by_cases small : m + κ ≤ 9
  · linarith only [budget, mul_le_mul_of_nonneg_left small (sq_nonneg s)]
  have hg : s * (m + κ) ^ 2 / 4 ≤ κ ^ 2 + (m * c - κ * β) ^ 2 := by
    have hid : 4 * (κ ^ 2 + (m * c - κ * β) ^ 2) - s * (m + κ) ^ 2 =
        2 * (m * c - 2 * κ * β) ^ 2 + s * (m - κ) ^ 2 + s * κ ^ 2 := by
      linear_combination 2 * m ^ 2 * hc2 - 4 * κ ^ 2 * hβ2
    linarith only [hid, sq_nonneg (m * c - 2 * κ * β), mul_nonneg hs.le (sq_nonneg (m - κ)),
      mul_nonneg hs.le (sq_nonneg κ)]
  have hsum : 0 < m + κ := by linarith
  have htail : s * (m + κ) / 4 ≤ P + (m * c - κ * β) ^ 2 * N := by
    have hbig := mul_le_mul_of_nonneg_left hnHigh (sq_nonneg (m * c - κ * β))
    have hd : (s * (m + κ) / 4) * (m + κ) ≤ κ ^ 2 + (m * c - κ * β) ^ 2 := by linarith only [hg]
    calc
      _ ≤ (κ ^ 2 + (m * c - κ * β) ^ 2) / (m + κ) := (le_div_iff₀ hsum).mpr hd
      _ ≤ _ := by rw [add_div]; simpa [div_eq_mul_inv] using add_le_add hpHigh hbig
  have hsq : s ^ 2 * (1 + m + κ) ≤ s * (1 + m + κ) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    nlinarith [mul_nonneg hs.le (show 0 ≤ 1 - s by linarith)]
  linarith only [htail, hsq, hs, mul_nonneg hs.le (show 0 ≤ m + κ - 9 by linarith)]

/-- Squaring the signed helicity selects its least favourable sign at opposite orientations. -/
theorem signed_helicity_lower (x y : ℝ) {N : ℝ} (hN : 0 ≤ N) :
    (|x| - |y|) ^ 2 * N ≤ (x + y) ^ 2 * N := by
  apply mul_le_mul_of_nonneg_right _ hN
  have hxy : -(x * y) ≤ |x| * |y| := by rw [← abs_mul]; exact neg_le_abs _
  nlinarith only [hxy, sq_abs x, sq_abs y]

/-- Azimuthally symmetric nonconstant modes use the Bessel and nonnegative vacuum estimates.
The k=0 mode also satisfies these hypotheses under the fixed-flux constant-mode formula. -/
theorem axisymmetric_gap {s κ F : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 4) (hk : 0 ≤ κ)
    (hbase : 2 - s ≤ F) (hhigh : κ - s ≤ F) : s ^ 2 / 80 * (1 + κ) ≤ F := by
  have hsq : s ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg s, mul_nonneg (show 0 ≤ 1 - s by linarith) (show 0 ≤ 1 + s by linarith)]
  have h₁ := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 1 + κ by linarith)
  linarith

/-- Fixed axial and azimuthal fluxes give a positive contribution in the uniform mode. -/
theorem fixed_flux_zero_mode {s γ β D ℓ : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 4)
    (hγ : 0 ≤ γ) (hD : 0 < D) (hℓ : 0 < ℓ) :
    s ^ 2 / 80 ≤ 2 - s + γ * s / 4 + β ^ 2 / D + s / ℓ := by
  have hb : 2 - s ≤ 2 - s + γ * s / 4 + β ^ 2 / D + s / ℓ := by
    linarith only [show 0 ≤ γ * s / 4 by positivity, show 0 ≤ β ^ 2 / D by positivity,
      show 0 ≤ s / ℓ by positivity]
  simpa using axisymmetric_gap (κ := 0) hs hsmax le_rfl hb (le_trans (by linarith) hb)

/-- The endpoint wall radius at s=1/4 satisfies the sufficient wall budget. -/
theorem endpoint_wall :
    Real.log (65 / 64) + (1 / 4) * (((65 / 64 : ℝ) ^ 2 - 1) / 2) /
      (1 - 3 * (1 / 4) / 4) ≤ (1 / 4) / 8 :=
  close_wall (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A wall at twice the plasma radius fails this sufficient window at every allowed s. -/
theorem distant_wall_fails {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 4) :
    s / 8 < Real.log 2 + s * (((2 : ℝ) ^ 2 - 1) / 2) / (1 - 3 * s / 4) := by
  have h : s / 8 < s * (((2 : ℝ) ^ 2 - 1) / 2) / (1 - 3 * s / 4) := by
    apply (lt_div_iff₀ (by linarith : 0 < 1 - 3 * s / 4)).mpr
    nlinarith [sq_nonneg s]
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end PlasmaLean.Stability.CylinderInterfaceGap
