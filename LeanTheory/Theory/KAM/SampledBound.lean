/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.StripPaleyWiener

/-!
# Strip norms from bounds on samples

Residual certificates for non-polynomial fields. `PaleyWiener.Bd_of_samples`
bounds `‖x‖_r` by the DFT of the samples on the frequency box plus the aliasing tail. Here the
DFT part is bounded by the **sum of the absolute values of the samples** (triangle inequality,
`|e^{-i(kθ+mψ)}| = 1`), so that a certificate only needs upper bounds on `|f|` at the grid
points:

* `norm_dft2_le`: `|dft_n| ≤ (N₁N₂)⁻¹ Σ_{j,l} |f(θ_j, ψ_l)|`;
* `sum_box_weight_le`: `Σ_{n ∈ box} e^{r|n|} ≤ (2K₁+1)(2K₂+1) E^{K₁+K₂}` for `e^r ≤ E`;
* `geoZ_mono`, `tailZ_mono`: monotonicity in `q` (for rational upper bounds of `e^{-(ρ-r)}`);
* **`Bd_of_sample_sum`**: with `Σ_{j,l} |f(θ_j, ψ_l)| ≤ S`,
  `‖x‖_r ≤ S/(N₁N₂) (2K₁+1)(2K₂+1) E^{K₁+K₂} + 2 M geoZ(Q) (tailZ(Q,K₁) + tailZ(Q,K₂))`
  for any `Q ∈ [e^{-(ρ-r)}, 1)`.

The triangle bound loses the cancellations of the DFT (a factor up to the box size); it is the
simplest sound choice and is exact in the dominant aliasing term. A sharper DFT enclosure would
need a validated table of the grid exponentials.

**Sanity.** `sum_box_weight_zero` (`r = 0`, `K = 0`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM.PaleyWiener

open Complex WEll1Z2

/-- **Triangle bound of the grid DFT.** -/
theorem norm_dft2_le (F : ℝ → ℝ → ℂ) {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) (n : ℤ × ℤ) :
    ‖dft2 F N₁ N₂ n‖ ≤ ((N₁ : ℝ) * N₂)⁻¹ * ∑ j₁ ∈ Finset.range N₁, ∑ j₂ ∈ Finset.range N₂,
      ‖F (samplePt N₁ j₁) (samplePt N₂ j₂)‖ := by
  unfold dft2
  rw [norm_mul]
  have hN : ‖((N₁ : ℂ) * N₂)⁻¹‖ = ((N₁ : ℝ) * N₂)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [hN]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₁ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₂ _ => ?_)
  rw [norm_mul, norm_fourierMode, mul_one]

theorem weight_le_box {r E : ℝ} (hr : 0 ≤ r) (hE : Real.exp r ≤ E) {K₁ K₂ : ℕ} {n : ℤ × ℤ}
    (hn : n ∈ box K₁ K₂) : weight r n ≤ E ^ (K₁ + K₂) := by
  rw [mem_box] at hn
  unfold weight modeSize
  have h1 : |(n.1 : ℝ)| + |(n.2 : ℝ)| ≤ ((K₁ + K₂ : ℕ) : ℝ) := by
    have a1 : |(n.1 : ℝ)| ≤ K₁ := by exact_mod_cast hn.1
    have a2 : |(n.2 : ℝ)| ≤ K₂ := by exact_mod_cast hn.2
    push_cast; linarith
  calc Real.exp (r * (|(n.1 : ℝ)| + |(n.2 : ℝ)|)) ≤ Real.exp (r * ((K₁ + K₂ : ℕ) : ℝ)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hr)
    _ = Real.exp r ^ (K₁ + K₂) := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ E ^ (K₁ + K₂) := pow_le_pow_left₀ (Real.exp_pos r).le hE _

theorem card_box (K₁ K₂ : ℕ) : (box K₁ K₂).card = (2 * K₁ + 1) * (2 * K₂ + 1) := by
  unfold box
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have e1 : ((K₁ : ℤ) + 1 - -(K₁ : ℤ)).toNat = 2 * K₁ + 1 := by omega
  have e2 : ((K₂ : ℤ) + 1 - -(K₂ : ℤ)).toNat = 2 * K₂ + 1 := by omega
  rw [e1, e2]

/-- `Σ_{n ∈ box} e^{r|n|} ≤ (2K₁+1)(2K₂+1) E^{K₁+K₂}`. -/
theorem sum_box_weight_le {r E : ℝ} (hr : 0 ≤ r) (hE : Real.exp r ≤ E) (K₁ K₂ : ℕ) :
    ∑ n ∈ box K₁ K₂, weight r n ≤ ((2 * K₁ + 1) * (2 * K₂ + 1) : ℕ) * E ^ (K₁ + K₂) := by
  calc ∑ n ∈ box K₁ K₂, weight r n ≤ ∑ _n ∈ box K₁ K₂, E ^ (K₁ + K₂) :=
        Finset.sum_le_sum fun n hn => weight_le_box hr hE hn
    _ = _ := by rw [Finset.sum_const, card_box, nsmul_eq_mul]

theorem geoZ_mono {q Q : ℝ} (hqQ : q ≤ Q) (hQ : Q < 1) : geoZ q ≤ geoZ Q := by
  unfold geoZ
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem tailZ_mono {q Q : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q < 1) (K : ℕ) :
    tailZ q K ≤ tailZ Q K := by
  unfold tailZ
  have h1 : q ^ (K + 1) ≤ Q ^ (K + 1) := pow_le_pow_left₀ hq hqQ _
  have h2 : 0 ≤ q ^ (K + 1) := pow_nonneg hq _
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **`Bd` from a bound on the sum of the samples.** -/
theorem Bd_of_sample_sum {f : ℂ → ℂ → ℂ} {ρ' ρ r M S E Q : ℝ} (x : FA)
    (hx : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = f θ ψ)
    (hper1 : ∀ θ ψ, f (θ + 2 * Real.pi) ψ = f θ ψ) (hper2 : ∀ θ ψ, f θ (ψ + 2 * Real.pi) = f θ ψ)
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    (hρ : 0 ≤ ρ) (hρρ : ρ < ρ') (hb : ∀ θ ψ : ℂ, |θ.im| ≤ ρ → |ψ.im| ≤ ρ → ‖f θ ψ‖ ≤ M)
    (hr0 : 0 ≤ r) (hr : r < ρ) {K₁ K₂ N₁ N₂ : ℕ} (h₁ : 2 * K₁ < N₁) (h₂ : 2 * K₂ < N₂)
    (hS : ∑ j₁ ∈ Finset.range N₁, ∑ j₂ ∈ Finset.range N₂,
      ‖f (samplePt N₁ j₁) (samplePt N₂ j₂)‖ ≤ S)
    (hE : Real.exp r ≤ E) (hQ1 : Real.exp (-(ρ - r)) ≤ Q) (hQ : Q < 1) :
    Bd r x (S / ((N₁ : ℝ) * N₂) * (((2 * K₁ + 1) * (2 * K₂ + 1) : ℕ) * E ^ (K₁ + K₂)) +
      2 * (M * geoZ Q * (tailZ Q K₁ + tailZ Q K₂))) := by
  have hB := Bd_of_samples x hx hper1 hper2 hd hρ hρρ hb hr0 hr h₁ h₂
  refine ⟨hB.1, hB.2.trans ?_⟩
  have hN₁ : 0 < N₁ := by omega
  have hN₂ : 0 < N₂ := by omega
  have hNN : (0 : ℝ) < (N₁ : ℝ) * N₂ := by positivity
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 0 (by simpa using hρ) (by simpa using hρ))
  set q := Real.exp (-(ρ - r))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  apply add_le_add
  · -- the DFT part
    have hdft : ∀ n, ‖dft2 (fun θ ψ : ℝ => f θ ψ) N₁ N₂ n‖ ≤ S / ((N₁ : ℝ) * N₂) := by
      intro n
      refine (norm_dft2_le _ hN₁ hN₂ n).trans ?_
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    have hS0 : 0 ≤ S / ((N₁ : ℝ) * N₂) := (norm_nonneg _).trans (hdft 0)
    calc ∑ n ∈ box K₁ K₂, ‖dft2 (fun θ ψ : ℝ => f θ ψ) N₁ N₂ n‖ * weight r n
        ≤ ∑ n ∈ box K₁ K₂, S / ((N₁ : ℝ) * N₂) * weight r n :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hdft n) (Real.exp_pos _).le
      _ = S / ((N₁ : ℝ) * N₂) * ∑ n ∈ box K₁ K₂, weight r n := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_box_weight_le hr0 hE K₁ K₂) hS0
  · -- the tail
    have hg := geoZ_mono hQ1 hQ
    have ht1 := tailZ_mono hq0 hQ1 hQ K₁
    have ht2 := tailZ_mono hq0 hQ1 hQ K₂
    have hq1 : q < 1 := lt_of_le_of_lt hQ1 hQ
    have hg0 : 0 ≤ geoZ q := by unfold geoZ; exact div_nonneg (by linarith) (by linarith)
    have ht0 : 0 ≤ tailZ q K₁ + tailZ q K₂ := by
      unfold tailZ; exact add_nonneg (div_nonneg (by positivity) (by linarith))
        (div_nonneg (by positivity) (by linarith))
    have hgQ : 0 ≤ geoZ Q := hg0.trans hg
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hg hM) (add_le_add ht1 ht2) ht0
      (mul_nonneg hM hgQ)

/-! ## Sanity -/

/-- `r = 0`, `K = 0`: the box is `{0}` with weight `1`. -/
theorem sum_box_weight_zero : ∑ n ∈ box 0 0, weight 0 n = 1 := by
  simp [box, weight]

end LeanTheory.Theory.KAM.PaleyWiener
