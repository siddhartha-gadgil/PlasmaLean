/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamPoint
public import Mathlib.Analysis.Complex.Schwarz

/-!
# A Lipschitz bound for the real coil field near the torus

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). The sampled certificate
evaluates the coil field at dyadic points `ỹ` next to the (irrational) torus points; the transfer
uses a Lipschitz bound of the real field `Bc = tfField + polyCoilFieldC`, obtained from the
complex sup bound `Mcoil` of `Design/CoilFieldComplex` by the **Schwarz lemma** (Mathlib
`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) along the complex line `t ↦ y' + t v`:

* `lip_of_bound` (general): if `y' ∈ realTube w₀`, `w₀ + ρ₁ ≤ w`, `ρ₁ ≤ η < d`, `w + d ≤ 7/20` and
  `‖y - y'‖ < ρ₁`, then `|Bc y i - Bc y' i| ≤ (2 Mcoil w d η / ρ₁) ‖y - y'‖`;
* `Mcoil_lip_le`: `Mcoil (11/50) (13/100) (1/50) ≤ 19600`;
* **`coil_lip`**: on `realTube (1/5)`, for `‖y - y'‖ ≤ 1/100`,
  `|Bc y i - Bc y' i| ≤ 2·10⁶ ‖y - y'‖` (the constant used by the sampled certificate).

**Sanity.** `lip_self` (zero displacement).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open Complex Metric Set PlasmaLean.Fields PlasmaLean.Fields.BiotSavartComplex
  PlasmaLean.Design.CoilFieldComplex PlasmaLean.Design.PolygonCoil
  PlasmaLean.Design.RationalStellarator.CoilsTF

theorem ofRealV_add_smul (y : Space) (t : ℝ) (v : Space) :
    ofRealV y + (t : ℂ) • ofRealV v = ofRealV (y + t • v) := by
  ext i; simp [ofRealV]

theorem realTube_mono {w w' : ℝ} (h : w ≤ w') {x : Space} (hx : x ∈ realTube w) :
    x ∈ realTube w' := ⟨hx.1.trans h, hx.2.trans h⟩

/-- Points within `δ` of `realTube w₀` lie in `realTube (w₀ + δ)`. -/
theorem realTube_of_dist {w₀ δ : ℝ} {x y : Space} (hy : y ∈ realTube w₀) (hxy : ‖x - y‖ ≤ δ) :
    x ∈ realTube (w₀ + δ) := by
  refine ⟨?_, ?_⟩
  · have := abs_sqrt_sub_le x y
    have h1 := hy.1
    calc |Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 1|
        ≤ |Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)| +
          |Real.sqrt (y 0 ^ 2 + y 1 ^ 2) - 1| := by
          have := abs_add_le (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
            (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) - 1)
          simpa using this
      _ ≤ w₀ + δ := by linarith
  · have h2 : |x 2 - y 2| ≤ ‖x - y‖ := by
      have := PiLp.norm_apply_le (x - y) 2
      simpa using this
    have := hy.2
    calc |x 2| ≤ |x 2 - y 2| + |y 2| := by
          have := abs_add_le (x 2 - y 2) (y 2); simpa using this
      _ ≤ w₀ + δ := by linarith

/-- **Lipschitz bound from the complex sup bound** (Schwarz lemma on a complex line). -/
theorem lip_of_bound {w₀ w d η ρ₁ : ℝ} (hw₀ : 0 ≤ w₀) (hρ₁ : 0 < ρ₁) (hρη : ρ₁ ≤ η) (hηd : η < d)
    (hwd : w + d ≤ 7 / 20) (hw : w₀ + ρ₁ ≤ w) {y y' : Space} (hy' : y' ∈ realTube w₀)
    (hyy : ‖y - y'‖ < ρ₁) (i : Fin 3) :
    |Bc y i - Bc y' i| ≤ 2 * Mcoil w d η / ρ₁ * ‖y - y'‖ := by
  by_cases h0 : y = y'
  · subst h0; simp
  have hn : 0 < ‖y - y'‖ := norm_pos_iff.2 (sub_ne_zero.2 h0)
  set v : Space := ‖y - y'‖⁻¹ • (y - y')
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, norm_inv, norm_norm]; field_simp
  have hw0 : 0 ≤ w := by linarith
  set g : ℂ → ℂ := fun t => coilFieldCC (ofRealV y' + t • ofRealV v) i
  -- the complex line stays in the neighbourhood
  have hmem : ∀ t ∈ ball (0 : ℂ) ρ₁, ofRealV y' + t • ofRealV v ∈ coilNbhdP w η := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    have hre : reV (ofRealV y' + t • ofRealV v) = y' + t.re • v := by
      ext j; simp [reV, ofRealV]
    have him : imV (ofRealV y' + t • ofRealV v) = t.im • v := by
      ext j; simp [imV, ofRealV]
    have hd : ‖reV (ofRealV y' + t • ofRealV v) - y'‖ < ρ₁ := by
      rw [hre, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm t).trans_lt ht
    have ht2 := realTube_of_dist hy' hd.le
    refine ⟨?_, ?_, ?_⟩
    · have := abs_sqrt_sub_le (reV (ofRealV y' + t • ofRealV v)) y'
      have h1 := hy'.1
      have e : |Real.sqrt ((reV (ofRealV y' + t • ofRealV v)) 0 ^ 2 +
          (reV (ofRealV y' + t • ofRealV v)) 1 ^ 2) - 1| < w := by
        calc _ ≤ |Real.sqrt ((reV (ofRealV y' + t • ofRealV v)) 0 ^ 2 +
              (reV (ofRealV y' + t • ofRealV v)) 1 ^ 2) - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)| +
              |Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) - 1| := by
              have := abs_add_le (Real.sqrt ((reV (ofRealV y' + t • ofRealV v)) 0 ^ 2 +
                (reV (ofRealV y' + t • ofRealV v)) 1 ^ 2) - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2))
                (Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) - 1)
              simpa using this
          _ < ρ₁ + w₀ := by linarith
          _ ≤ w := by linarith
      simpa [reV] using e
    · have h2 : |(reV (ofRealV y' + t • ofRealV v)) 2 - y' 2| < ρ₁ := by
        have := PiLp.norm_apply_le (reV (ofRealV y' + t • ofRealV v) - y') 2
        simp only [PiLp.sub_apply] at this
        exact this.trans_lt hd
      have h3 := hy'.2
      have : |(reV (ofRealV y' + t • ofRealV v)) 2| < w := by
        calc _ ≤ |(reV (ofRealV y' + t • ofRealV v)) 2 - y' 2| + |y' 2| := by
              have h := abs_add_le ((reV (ofRealV y' + t • ofRealV v)) 2 - y' 2) (y' 2)
              rwa [sub_add_cancel] at h
          _ < ρ₁ + w₀ := by linarith
          _ ≤ w := by linarith
      simpa [reV, add_comm] using this
    · rw [him, norm_smul, hv, mul_one, Real.norm_eq_abs]
      exact ((Complex.abs_im_le_norm t).trans_lt ht).trans_le hρη
  -- holomorphy and the bound
  have hdiff : DifferentiableOn ℂ g (ball (0 : ℂ) ρ₁) := by
    have hcf := coilFieldCC_apply_differentiableOn hw0 (hρ₁.le.trans hρη) hηd hwd i
    have haff : Differentiable ℂ (fun t : ℂ => ofRealV y' + t • ofRealV v) := by fun_prop
    exact hcf.comp haff.differentiableOn hmem
  have hbound : ∀ t ∈ ball (0 : ℂ) ρ₁, ‖g t‖ ≤ Mcoil w d η := fun t ht =>
    norm_coilFieldCC_apply_le hw0 hηd hwd (hmem t ht) i
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) ρ₁ := mem_ball_self hρ₁
  have hmaps : MapsTo g (ball (0 : ℂ) ρ₁) (closedBall (g 0) (2 * Mcoil w d η)) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    have := hbound t ht
    have := hbound 0 h0mem
    calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ 2 * Mcoil w d η := by linarith
  set s : ℂ := (‖y - y'‖ : ℂ)
  have hs : s ∈ ball (0 : ℂ) ρ₁ := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hyy
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hs
  -- identify the endpoints
  have hpt : y' + ‖y - y'‖ • v = y := by
    simp only [v, smul_smul]; rw [mul_inv_cancel₀ hn.ne', one_smul]; abel
  have hyT : y ∈ realTube (w₀ + ρ₁) := realTube_of_dist hy' hyy.le
  have hwlt : w₀ + ρ₁ < 7 / 20 := by linarith
  have hw0lt : w₀ < 7 / 20 := by linarith
  have gs : g s = ((Bc y i : ℝ) : ℂ) := by
    simp only [g, s]
    rw [show ((‖y - y'‖ : ℝ) : ℂ) • ofRealV v = ((‖y - y'‖ : ℝ) : ℂ) • ofRealV v from rfl,
      ofRealV_add_smul, hpt, coilFieldCC_ofReal hwlt hyT]
    simp [ofRealV, Bc]
  have g0 : g 0 = ((Bc y' i : ℝ) : ℂ) := by
    simp only [g, zero_smul, add_zero]
    rw [coilFieldCC_ofReal hw0lt hy']
    simp [ofRealV, Bc]
  rw [gs, g0, dist_eq_norm, dist_zero_right, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hsch
  simpa [s, abs_of_nonneg (norm_nonneg _)] using hsch

/-- The concrete constant: `Mcoil (11/50) (13/100) (1/50) ≤ 19600`. -/
theorem Mcoil_lip_le : Mcoil (11 / 50) (13 / 100) (1 / 50) ≤ 19600 := by
  unfold Mcoil Tpoly Taxis κ0
  have hS : S32 = 4294967296 := rfl
  have hs1 : Real.sqrt ((4 + 2 * (11 / 50 : ℝ)) ^ 2 + (1 / 50) ^ 2) ≤ 4441 / 1000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hm : ((13 / 100 : ℝ) ^ 2 - (1 / 50) ^ 2) = 33 / 2000 := by norm_num
  have hs2 : (1284 / 10000 : ℝ) ≤ Real.sqrt (33 / 2000) := Real.le_sqrt_of_sq_le (by norm_num)
  have hden : (33 / 2000 : ℝ) * (1284 / 10000) ≤
      ((13 / 100 : ℝ) ^ 2 - (1 / 50) ^ 2) ^ (3 / 2 : ℝ) := by
    rw [hm, rpow_three_halves (by norm_num)]; gcongr
  have hP : 90485364 / S32 * (23 / 10) * Real.sqrt ((4 + 2 * (11 / 50 : ℝ)) ^ 2 + (1 / 50) ^ 2) /
      ((13 / 100 : ℝ) ^ 2 - (1 / 50) ^ 2) ^ (3 / 2 : ℝ) ≤
      90485364 / 4294967296 * (23 / 10) * (4441 / 1000) / ((33 / 2000) * (1284 / 10000)) := by
    rw [hS]; gcongr
  have hk0 : (1 - (1 / 50 : ℝ) ^ 2 / (1 - 11 / 50) ^ 2) = 1520 / 1521 := by norm_num
  have hsk : (9996 / 10000 : ℝ) ≤ Real.sqrt (1520 / 1521) := Real.le_sqrt_of_sq_le (by norm_num)
  have hA : (1 - (1 / 50 : ℝ) ^ 2 / (1 - 11 / 50) ^ 2) ^ (-(3 / 2) : ℝ) ≤
      ((1520 / 1521) * (9996 / 10000))⁻¹ := by
    rw [hk0, Real.rpow_neg (by norm_num), rpow_three_halves (by norm_num)]
    gcongr
  have hA0 : 0 ≤ (1 / (1 - 11 / 50) + (1 / 50 : ℝ) / (1 - 11 / 50) ^ 2) := by norm_num
  have hAx := mul_le_mul_of_nonneg_right hA hA0
  norm_num at hP hAx ⊢
  linarith

/-- **The Lipschitz bound of the sampled certificate**: for `y' ∈ realTube (1/5)` and
`‖y - y'‖ ≤ 1/100`, `|Bc y i - Bc y' i| ≤ 2·10⁶ ‖y - y'‖`. -/
theorem coil_lip {y y' : Space} (hy' : y' ∈ realTube (1 / 5)) (hyy : ‖y - y'‖ ≤ 1 / 100)
    (i : Fin 3) : |Bc y i - Bc y' i| ≤ 2000000 * ‖y - y'‖ := by
  have h := lip_of_bound (y := y) (y' := y') (w₀ := 1 / 5) (w := 11 / 50) (d := 13 / 100)
    (η := 1 / 50)
    (ρ₁ := 1 / 50) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    hy' (by linarith) i
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have := Mcoil_lip_le
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-! ## Sanity -/

/-- Zero displacement. -/
theorem lip_self (y : Space) (i : Fin 3) : |Bc y i - Bc y i| = 0 := by simp

end PlasmaLean.Design.CoilKam
