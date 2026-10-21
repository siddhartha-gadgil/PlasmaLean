/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2MercierData

/-!
# Family 2 (`ε = 1/4`, `S = 4`): certified shear `ι' > 0` and magnetic hill `V'' > 0`

On the Mercier-stable band `k ∈ [7/10, 9/10]` of `LandremanFamily2MercierStable`, the
certificate there only proves `D_Merc > 0`; the signs of its two ingredients were numerical
observations. Here a small validated checker (`signCheck`, reusing the one-dimensional
quadratures `oneD` and `mem_quad1` of `LandremanFamily2Quad`, no surface integrals) encloses
`Z' F₁ - Z F₁'` and `Z' E F₁ + Z E' F₁ - Z E F₁'` on ten `k`-cells of width `1/50`, run by
`decide +kernel`. Hence, for every `λ > 0` (`family2_shear_hill_general`) and in particular
`λ = 200` (`family2_shear_hill`):

* `ι' = dι/dψ_t > 0` (`iotaPrimeK`): positive magnetic shear;
* `V'' = d²V/dψ_t² > 0` (`VppK`): a **magnetic hill** (with `μ₀ p' < 0`, so the well term of
  the Mercier criterion is destabilizing); the band is stable because the shear wins.

Both numerators are independent of `λ`; `λ` only enters through the positive factor
`1/(k ψ_t')`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2SignCert

open Real PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.LandremanFamily2Labels PlasmaLean.Design.LandremanFamily2MercierData
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell mem_Ecell)
open FIv (mem_add mem_sub mem_mul)

/-- Enclosure of the shear numerator `Z' F₁ - Z F₁'` from the one-dimensional data. -/
@[expose] def shearIv (D : FIv × FIv × FIv × FIv × FIv × FIv) : FIv :=
  (D.2.2.2.1.mul D.1).sub (D.2.2.1.mul D.2.1)

/-- Enclosure of the hill numerator `Z' E F₁ + Z E' F₁ - Z E F₁'`. -/
@[expose] def hillIv (D : FIv × FIv × FIv × FIv × FIv × FIv) : FIv :=
  (((D.2.2.2.1.mul D.2.2.2.2.1).mul D.1).add ((D.2.2.1.mul D.2.2.2.2.2).mul D.1)).sub
    ((D.2.2.1.mul D.2.2.2.2.1).mul D.2.1)

/-- **The sign checker** on a `k`-cell `[k_a, k_b]` with `N1` one-dimensional cells. -/
@[expose] def signCheck (N1 : ℕ) (ka kb : ℚ) : Bool :=
  let D := oneD N1 (Ecell ka kb)
  decide (0 < ka) && decide (ka ≤ kb) && decide (kb ≤ 19 / 20) && decide (0 < N1) &&
    (shearIv D).ok && (hillIv D).ok && decide (0 < (shearIv D).lo) && decide (0 < (hillIv D).lo)

/-- **Soundness of the sign checker**: acceptance proves both numerators positive for every
real `k` in the cell. -/
theorem signCheck_sound {N1 : ℕ} {ka kb : ℚ} (h : signCheck N1 ka kb = true) {k : ℝ}
    (hk1 : (ka : ℝ) ≤ k) (hk2 : k ≤ kb) :
    0 < Zd (1 / 4) k * F1 (1 / 4) 4 k - Zint (1 / 4) k * F1d (1 / 4) 4 k ∧
      0 < Zd (1 / 4) k * Eint k * F1 (1 / 4) 4 k + Zint (1 / 4) k * Ed k * F1 (1 / 4) 4 k -
        Zint (1 / 4) k * Eint k * F1d (1 / 4) 4 k := by
  unfold signCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hka, hkab⟩, hkb⟩, hN1⟩, okS⟩, okH⟩, posS⟩, posH⟩ := h
  have hk0 : 0 < k := lt_of_lt_of_le (by exact_mod_cast hka) hk1
  have hkb'' : (kb : ℝ) ≤ 19 / 20 := by
    rw [show (19 / 20 : ℝ) = ((19 / 20 : ℚ) : ℝ) by norm_num]; exact_mod_cast hkb
  have hk : k ^ 2 < 1 := by nlinarith
  have hK : (Ecell ka kb).Mem k := mem_Ecell hk1 hk2
  have hK2 := FIv.mem_sq hK
  have hreg : ∀ y ∈ Set.Icc (-1 : ℝ) 1, (k, y) ∈ Kreg := fun _ _ => hk
  have hereg : ∀ y ∈ Set.Icc (-1 : ℝ) 1, (k, y) ∈ Ereg := fun y hy => ⟨hk, hy⟩
  have hF1 := mem_quad1 (f := fun y => fF1 (1 / 4) 4 k y) hN1
    (contOn_fix (continuousOn_fF1 (by norm_num)) hreg) (fun hY => mem_evF1 hK hK2 hY)
  have hF1d := mem_quad1 (f := fun y => fF1k (1 / 4) 4 k y) hN1
    (contOn_fix (continuousOn_fF1k (by norm_num)) hreg) (fun hY => mem_evF1k hK hK2 hY)
  have hZ := mem_quad1 (f := fun y => fZ (1 / 4) k y) hN1 (contOn_fix continuousOn_fZ hreg)
    (fun hY => mem_evZ hK2 hY)
  have hZd := mem_quad1 (f := fun y => fZk (1 / 4) k y) hN1 (contOn_fix continuousOn_fZk hreg)
    (fun hY => mem_evZk hK hK2 hY)
  have hE := mem_quad1 (f := fun y => fE k y) hN1 (contOn_fix continuousOn_fE hereg)
    (fun hY => mem_evE hK2 hY)
  have hEd := mem_quad1 (f := fun y => fEk k y) hN1 (contOn_fix continuousOn_fEk hereg)
    (fun hY => mem_evEk hK hK2 hY)
  have hS := mem_sub (mem_mul hZd hF1) (mem_mul hZ hF1d)
  have hH := mem_sub (mem_add (mem_mul (mem_mul hZd hE) hF1) (mem_mul (mem_mul hZ hEd) hF1))
    (mem_mul (mem_mul hZ hE) hF1d)
  exact ⟨lt_of_lt_of_le (fxVal_pos posS) (hS okS).1, lt_of_lt_of_le (fxVal_pos posH) (hH okH).1⟩

/-- Cover of a `k`-interval by accepted sign-checker cells. -/
inductive SignCovered : ℚ → ℚ → Prop where
  /-- A single accepted cell. -/
  | cell (a b : ℚ) (N1 : ℕ) : signCheck N1 a b = true → SignCovered a b
  /-- Two adjacent covered intervals. -/
  | join (a b c : ℚ) : SignCovered a b → SignCovered b c → SignCovered a c

/-- Soundness of a cover. -/
theorem SignCovered.sound {a b : ℚ} (h : SignCovered a b) {k : ℝ} (h1 : (a : ℝ) ≤ k)
    (h2 : k ≤ b) :
    0 < Zd (1 / 4) k * F1 (1 / 4) 4 k - Zint (1 / 4) k * F1d (1 / 4) 4 k ∧
      0 < Zd (1 / 4) k * Eint k * F1 (1 / 4) 4 k + Zint (1 / 4) k * Ed k * F1 (1 / 4) 4 k -
        Zint (1 / 4) k * Eint k * F1d (1 / 4) 4 k := by
  induction h with
  | cell a b N1 hc => exact signCheck_sound hc h1 h2
  | join a b c _ _ ih1 ih2 =>
    rcases le_total k b with hk | hk
    · exact ih1 h1 hk
    · exact ih2 hk h2

set_option maxRecDepth 100000 in
/-- Cell `[7/10, 18/25]`. -/
theorem sc0 : signCheck 16 (7 / 10) (18 / 25) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[18/25, 37/50]`. -/
theorem sc1 : signCheck 16 (18 / 25) (37 / 50) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[37/50, 19/25]`. -/
theorem sc2 : signCheck 16 (37 / 50) (19 / 25) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[19/25, 39/50]`. -/
theorem sc3 : signCheck 16 (19 / 25) (39 / 50) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[39/50, 4/5]`. -/
theorem sc4 : signCheck 16 (39 / 50) (4 / 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[4/5, 41/50]`. -/
theorem sc5 : signCheck 16 (4 / 5) (41 / 50) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[41/50, 21/25]`. -/
theorem sc6 : signCheck 16 (41 / 50) (21 / 25) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[21/25, 43/50]`. -/
theorem sc7 : signCheck 16 (21 / 25) (43 / 50) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[43/50, 22/25]`. -/
theorem sc8 : signCheck 16 (43 / 50) (22 / 25) = true := by decide +kernel
set_option maxRecDepth 100000 in
/-- Cell `[22/25, 9/10]`. -/
theorem sc9 : signCheck 16 (22 / 25) (9 / 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Rejected fixture (non-vacuity): the single coarse cell `k ∈ [1/20, 9/10]` with two
one-dimensional cells is not accepted (its enclosures are too wide). -/
theorem signCheck_rejects_coarse : signCheck 2 (1 / 20) (9 / 10) = false := by decide +kernel

/-- **The cover of `[7/10, 9/10]`** by ten kernel-checked cells. -/
theorem sign_cover : SignCovered (7 / 10) (9 / 10) :=
  .join _ _ _ (.cell _ _ _ sc0) (.join _ _ _ (.cell _ _ _ sc1) (.join _ _ _ (.cell _ _ _ sc2)
    (.join _ _ _ (.cell _ _ _ sc3) (.join _ _ _ (.cell _ _ _ sc4) (.join _ _ _ (.cell _ _ _ sc5)
    (.join _ _ _ (.cell _ _ _ sc6) (.join _ _ _ (.cell _ _ _ sc7) (.join _ _ _ (.cell _ _ _ sc8)
    (.cell _ _ _ sc9)))))))))

/-- **Shear and hill on the band, every `λ > 0`**: `ι' > 0` and `V'' > 0` (derivatives in the
toroidal-flux label) on every surface `ψ = k²/2`, `k ∈ [7/10, 9/10]`. -/
theorem family2_shear_hill_general {lam : ℝ} (hl : 0 < lam) {k : ℝ}
    (hk : k ∈ Set.Icc (7 / 10 : ℝ) (9 / 10)) : 0 < iotaPrimeK lam k ∧ 0 < VppK lam k := by
  have hk0 : 0 < k := by linarith [hk.1]
  have hk1 : k < 19 / 20 := by linarith [hk.2]
  obtain ⟨hS, hH⟩ := sign_cover.sound (k := k) (by push_cast; linarith [hk.1])
    (by push_cast; linarith [hk.2])
  have hF := F1_pos (S := 4) eps_ne (mem_Ioo1 hk0 hk1)
  have htp : 0 < tpR lam k := by unfold tpR; positivity
  refine ⟨?_, ?_⟩
  · rw [iotaPrimeK_eq hl.ne' hk0 hk1]
    unfold iotapR
    positivity
  · rw [VppK_eq hl.ne' hk0 hk1]
    positivity

/-- **Family 2 at `λ = 200`**: on the Mercier-stable band `k ∈ [7/10, 9/10]` the magnetic shear
is positive (`ι' > 0`) and the surfaces have a magnetic hill (`V'' > 0`). -/
theorem family2_shear_hill {k : ℝ} (hk : k ∈ Set.Icc (7 / 10 : ℝ) (9 / 10)) :
    0 < iotaPrimeK 200 k ∧ 0 < VppK 200 k :=
  family2_shear_hill_general (by norm_num) hk

end PlasmaLean.Design.LandremanFamily2SignCert
