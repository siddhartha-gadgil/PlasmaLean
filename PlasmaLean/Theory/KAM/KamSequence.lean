/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp

/-!
# Convergence of KAM/Newton iterations with loss of analyticity

Lemma 1 (`kam_sequence`) of the K3 plan (`notes/theory/kam-k3-plan.md`, §2 and §4). This is pure
real analysis about the error sequence `e_j = ‖E(K_j)‖_{r_j}` of a Newton scheme that loses a
strip `2δ_j` per step.

**Scheme.** `δ_j = δ₀ 2^{−j}` (`kamDelta`), `r_{j+1} = r_j − c δ_j` (`kamRadius`, the plan uses
`c = 2`), so `r_j = r₀ − 2cδ₀(1 − 2^{−j}) ↓ r₀ − 2cδ₀` (`kamRadius_eq`, `kamRadius_gt`); for
`c = 2`, `δ₀ = r₀/8` the limit is `r₀/2`.

**Hypotheses.** `e_j ≥ 0`, the quadratic recursion `e_{j+1} ≤ κ e_j² / δ_j⁴` (`κ = Ĉ/γ⁴`), and the
smallness `32 κ e₀ / δ₀⁴ ≤ 1`.

**Conclusions (`kam_sequence`).** With `ε_j = 16 κ e_j / δ_j⁴` (`kamEps`) one has
`ε_{j+1} ≤ ε_j²` (`kamEps_succ_le`), hence `ε_j ≤ ε₀^{2^j}` and
* `e_j ≤ e₀ ε₀^{2^j − 1} / 16^j ≤ e₀ (1/2)^{2^j − 1} / 16^j` (super-exponential decay),
* `e_j → 0`,
* for `τ ≤ 4` and `C' ≥ 0`, the displacement series `∑_j C' e_j / δ_j^τ` converges with
  `∑_j C' e_j / δ_j^τ ≤ 2 C' e₀ / δ₀^τ`, and its tail from `n` is `≤ 2 C' e₀ / δ₀^τ · 2^{−n}`.

`kam_sequence_hat` restates this with `κ = Ĉ/γ⁴` and displacement constants `Ĉ'/γ²`, `τ = 2`,
exactly in the form of the plan: total displacement `≤ 2Ĉ' e₀/(γ²δ₀²)`. `kam_limit` turns a
summable displacement bound into a limit in any complete metric space with
`dist(K₀, K_∞) ≤ ∑ d_j` (this is where completeness of `ℓ¹_{r/2}` is used).

**Sanity.** `kam_sequence_zero` (the zero sequence), `kamExact` (the extremal sequence with
equality in the recursion satisfies the hypotheses at `κ = δ₀ = 1`, `e₀ = 1/32`), and the rejected
fixture `kamBad_not_tendsto`: without smallness (`κ = δ₀ = e₀ = 1`, equality in the recursion)
the errors never drop below `1`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

open Filter Topology

/-! ## The strip losses and radii -/

/-- The strip loss at step `j`: `δ_j = δ₀ / 2^j`. -/
def kamDelta (δ₀ : ℝ) (j : ℕ) : ℝ := δ₀ / 2 ^ j

/-- Positivity of the strip losses. -/
theorem kamDelta_pos {δ₀ : ℝ} (hδ : 0 < δ₀) (j : ℕ) : 0 < kamDelta δ₀ j := by
  unfold kamDelta; positivity

/-- `δ_{j+1} = δ_j / 2`. -/
theorem kamDelta_succ (δ₀ : ℝ) (j : ℕ) : kamDelta δ₀ (j + 1) = kamDelta δ₀ j / 2 := by
  unfold kamDelta; rw [pow_succ]; field_simp

/-- `δ_0 = δ₀`. -/
@[simp] theorem kamDelta_zero (δ₀ : ℝ) : kamDelta δ₀ 0 = δ₀ := by simp [kamDelta]

/-- The strip widths `r_{j+1} = r_j − c δ_j`. -/
def kamRadius (r₀ c δ₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | j + 1 => kamRadius r₀ c δ₀ j - c * kamDelta δ₀ j

/-- Closed form: `r_j = r₀ − 2cδ₀(1 − 2^{−j})`. -/
theorem kamRadius_eq (r₀ c δ₀ : ℝ) (j : ℕ) :
    kamRadius r₀ c δ₀ j = r₀ - 2 * c * δ₀ * (1 - 1 / 2 ^ j) := by
  induction j with
  | zero => simp [kamRadius]
  | succ j ih =>
    rw [kamRadius, ih, kamDelta, pow_succ]
    field_simp
    ring

/-- The strips stay above the limiting width `r₀ − 2cδ₀` (for `c, δ₀ ≥ 0`). -/
theorem kamRadius_ge {r₀ c δ₀ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ₀) (j : ℕ) :
    r₀ - 2 * c * δ₀ ≤ kamRadius r₀ c δ₀ j := by
  rw [kamRadius_eq]
  have : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
  have h2 : 0 ≤ 2 * c * δ₀ := by positivity
  nlinarith

/-- The strips are strictly wider than the limit `r₀ − 2cδ₀` when `c, δ₀ > 0`. -/
theorem kamRadius_gt {r₀ c δ₀ : ℝ} (hc : 0 < c) (hδ : 0 < δ₀) (j : ℕ) :
    r₀ - 2 * c * δ₀ < kamRadius r₀ c δ₀ j := by
  rw [kamRadius_eq]
  have : 0 < 1 / (2 : ℝ) ^ j := by positivity
  have h2 : 0 < 2 * c * δ₀ := by positivity
  nlinarith

/-- The strips decrease (for `c, δ₀ ≥ 0`). -/
theorem kamRadius_succ_le {r₀ c δ₀ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ₀) (j : ℕ) :
    kamRadius r₀ c δ₀ (j + 1) ≤ kamRadius r₀ c δ₀ j := by
  rw [kamRadius]
  have : 0 ≤ c * kamDelta δ₀ j := mul_nonneg hc (by unfold kamDelta; positivity)
  linarith

/-- Torus A normalization: with `c = 2` and `δ₀ = r₀/8` the strips stay above `r₀/2`. -/
theorem kamRadius_half {r₀ : ℝ} (hr : 0 < r₀) (j : ℕ) :
    r₀ / 2 < kamRadius r₀ 2 (r₀ / 8) j := by
  have := kamRadius_gt (r₀ := r₀) (c := 2) (δ₀ := r₀ / 8) (by norm_num) (by positivity) j
  linarith

/-! ## The normalized errors -/

/-- The normalized error `ε_j = 16 κ e_j / δ_j⁴`. -/
def kamEps (κ δ₀ : ℝ) (e : ℕ → ℝ) (j : ℕ) : ℝ := 16 * κ * e j / kamDelta δ₀ j ^ 4

/-- The normalized errors are nonnegative. -/
theorem kamEps_nonneg {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 ≤ κ) (he : ∀ j, 0 ≤ e j) (j : ℕ) :
    0 ≤ kamEps κ δ₀ e j := by
  unfold kamEps
  have := he j
  positivity

/-- **The squaring step** `ε_{j+1} ≤ ε_j²`. -/
theorem kamEps_succ_le {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 ≤ κ) (hδ : 0 < δ₀)
    (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4) (j : ℕ) :
    kamEps κ δ₀ e (j + 1) ≤ kamEps κ δ₀ e j ^ 2 := by
  have hd := kamDelta_pos hδ j
  unfold kamEps
  rw [kamDelta_succ]
  calc 16 * κ * e (j + 1) / (kamDelta δ₀ j / 2) ^ 4
      = 256 * κ * e (j + 1) / kamDelta δ₀ j ^ 4 := by field_simp; ring
    _ ≤ 256 * κ * (κ * e j ^ 2 / kamDelta δ₀ j ^ 4) / kamDelta δ₀ j ^ 4 := by
        gcongr; exact hrec j
    _ = (16 * κ * e j / kamDelta δ₀ j ^ 4) ^ 2 := by field_simp; ring

/-- Iterating the squaring step: `ε_j ≤ ε₀^{2^j}`. -/
theorem kamEps_le_pow {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 ≤ κ) (hδ : 0 < δ₀)
    (he : ∀ j, 0 ≤ e j) (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4) (j : ℕ) :
    kamEps κ δ₀ e j ≤ kamEps κ δ₀ e 0 ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc kamEps κ δ₀ e (j + 1) ≤ kamEps κ δ₀ e j ^ 2 := kamEps_succ_le hκ hδ hrec j
      _ ≤ (kamEps κ δ₀ e 0 ^ (2 ^ j)) ^ 2 := by
          gcongr; exact kamEps_nonneg hκ he j
      _ = kamEps κ δ₀ e 0 ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]

/-- Recovering the error from the normalized error: `e_j = ε_j δ₀⁴ / (16κ · 16^j)`. -/
theorem e_eq_kamEps {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀) (j : ℕ) :
    e j = kamEps κ δ₀ e j * δ₀ ^ 4 / (16 * κ * 16 ^ j) := by
  unfold kamEps kamDelta
  have h16 : (16 : ℝ) ^ j = (2 ^ j) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h16]
  field_simp

/-- **Super-exponential decay** `e_j ≤ e₀ ε₀^{2^j − 1} / 16^j`. -/
theorem e_le_eps_pow {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀)
    (he : ∀ j, 0 ≤ e j) (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4) (j : ℕ) :
    e j ≤ e 0 * kamEps κ δ₀ e 0 ^ (2 ^ j - 1) / 16 ^ j := by
  have hpow := kamEps_le_pow hκ.le hδ he hrec j
  have h0 := e_eq_kamEps (e := e) hκ hδ 0
  simp only [pow_zero, mul_one] at h0
  have hsplit : kamEps κ δ₀ e 0 ^ (2 ^ j) =
      kamEps κ δ₀ e 0 * kamEps κ δ₀ e 0 ^ (2 ^ j - 1) := by
    rw [← pow_succ']; congr 1; have := Nat.one_le_two_pow (n := j); omega
  rw [e_eq_kamEps (e := e) hκ hδ j]
  have hpos : 0 < 16 * κ * (16 : ℝ) ^ j := by positivity
  calc kamEps κ δ₀ e j * δ₀ ^ 4 / (16 * κ * 16 ^ j)
      ≤ kamEps κ δ₀ e 0 ^ (2 ^ j) * δ₀ ^ 4 / (16 * κ * 16 ^ j) := by gcongr
    _ = (kamEps κ δ₀ e 0 * δ₀ ^ 4 / (16 * κ)) * kamEps κ δ₀ e 0 ^ (2 ^ j - 1) / 16 ^ j := by
        rw [hsplit]; field_simp
    _ = e 0 * kamEps κ δ₀ e 0 ^ (2 ^ j - 1) / 16 ^ j := by rw [← h0]

/-- The smallness condition `32 κ e₀ / δ₀⁴ ≤ 1` says `ε₀ ≤ 1/2`. -/
theorem kamEps_zero_le_half {κ δ₀ : ℝ} {e : ℕ → ℝ}
    (hsmall : 32 * κ * e 0 / δ₀ ^ 4 ≤ 1) : kamEps κ δ₀ e 0 ≤ 1 / 2 := by
  unfold kamEps
  rw [kamDelta_zero]
  have : 16 * κ * e 0 / δ₀ ^ 4 = (32 * κ * e 0 / δ₀ ^ 4) / 2 := by ring
  rw [this]; linarith

/-- Decay under the smallness condition: `e_j ≤ e₀ (1/2)^{2^j − 1} / 16^j`. -/
theorem e_le_half_pow {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀)
    (he : ∀ j, 0 ≤ e j) (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4)
    (hsmall : 32 * κ * e 0 / δ₀ ^ 4 ≤ 1) (j : ℕ) :
    e j ≤ e 0 * (1 / 2) ^ (2 ^ j - 1) / 16 ^ j := by
  refine (e_le_eps_pow hκ hδ he hrec j).trans ?_
  have := he 0
  gcongr
  · exact kamEps_nonneg hκ.le he 0
  · exact kamEps_zero_le_half hsmall

/-- The displacement term at step `j` is at most `C' e₀ δ₀^{−τ} 2^{−j}` (for `τ ≤ 4`). -/
theorem disp_term_le {κ δ₀ C' : ℝ} {e : ℕ → ℝ} {τ : ℕ} (hτ : τ ≤ 4) (hC : 0 ≤ C') (hκ : 0 < κ)
    (hδ : 0 < δ₀) (he : ∀ j, 0 ≤ e j)
    (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4)
    (hsmall : 32 * κ * e 0 / δ₀ ^ 4 ≤ 1) (j : ℕ) :
    C' * e j / kamDelta δ₀ j ^ τ ≤ C' * e 0 / δ₀ ^ τ * (1 / 2) ^ j := by
  have hdec := e_le_half_pow hκ hδ he hrec hsmall j
  have he0 := he 0
  have hdj : kamDelta δ₀ j ^ τ = δ₀ ^ τ / (2 ^ τ) ^ j := by
    unfold kamDelta; rw [div_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hhalf : (1 / 2 : ℝ) ^ (2 ^ j - 1) ≤ (1 / 2) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by have := Nat.lt_two_pow_self (n := j); omega)
  have h2τ : ((2 : ℝ) ^ τ) ^ j ≤ 16 ^ j := by
    gcongr
    calc (2 : ℝ) ^ τ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hτ
      _ = 16 := by norm_num
  rw [hdj, div_div_eq_mul_div]
  calc C' * e j * ((2 : ℝ) ^ τ) ^ j / δ₀ ^ τ
      ≤ C' * (e 0 * (1 / 2) ^ (2 ^ j - 1) / 16 ^ j) * 16 ^ j / δ₀ ^ τ := by
        gcongr
    _ = C' * e 0 / δ₀ ^ τ * (1 / 2) ^ (2 ^ j - 1) := by field_simp
    _ ≤ C' * e 0 / δ₀ ^ τ * (1 / 2) ^ j := by gcongr

/-- **The KAM sequence lemma.** Let `κ > 0`, `δ₀ > 0`, `e_j ≥ 0` with
`e_{j+1} ≤ κ e_j² / δ_j⁴` (`δ_j = δ₀ 2^{−j}`) and `32 κ e₀ / δ₀⁴ ≤ 1`. Then
1. `e_j ≤ e₀ (1/2)^{2^j − 1} / 16^j` for all `j`;
2. `e_j → 0`;
3. for every `τ ≤ 4` and `C' ≥ 0`, the series `∑_j C' e_j / δ_j^τ` converges and
   `∑_j C' e_j / δ_j^τ ≤ 2 C' e₀ / δ₀^τ`;
4. its tails satisfy `∑_j C' e_{j+n} / δ_{j+n}^τ ≤ 2 C' e₀ / δ₀^τ · (1/2)^n`. -/
theorem kam_sequence {κ δ₀ : ℝ} {e : ℕ → ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀)
    (he : ∀ j, 0 ≤ e j) (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4)
    (hsmall : 32 * κ * e 0 / δ₀ ^ 4 ≤ 1) :
    (∀ j, e j ≤ e 0 * (1 / 2) ^ (2 ^ j - 1) / 16 ^ j) ∧
    Tendsto e atTop (𝓝 0) ∧
    (∀ (τ : ℕ) (C' : ℝ), τ ≤ 4 → 0 ≤ C' →
      Summable (fun j => C' * e j / kamDelta δ₀ j ^ τ) ∧
      ∑' j, C' * e j / kamDelta δ₀ j ^ τ ≤ 2 * C' * e 0 / δ₀ ^ τ ∧
      ∀ n, ∑' j, C' * e (j + n) / kamDelta δ₀ (j + n) ^ τ ≤
        2 * C' * e 0 / δ₀ ^ τ * (1 / 2) ^ n) := by
  have hdec := e_le_half_pow hκ hδ he hrec hsmall
  refine ⟨hdec, ?_, ?_⟩
  · -- `0 ≤ e_j ≤ e₀ (1/2)^j`
    have hle : ∀ j, e j ≤ e 0 * (1 / 2) ^ j := by
      intro j
      have h := disp_term_le (τ := 0) (C' := 1) (by norm_num) (by norm_num) hκ hδ he hrec
        hsmall j
      simpa using h
    have hlim : Tendsto (fun j => e 0 * (1 / 2 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (e 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim he hle
  · intro τ C' hτ hC
    have hterm := disp_term_le hτ hC hκ hδ he hrec hsmall
    have hnn : ∀ j, 0 ≤ C' * e j / kamDelta δ₀ j ^ τ := fun j => by
      have := he j; have := kamDelta_pos hδ j; positivity
    have hgeo : Summable fun j : ℕ => C' * e 0 / δ₀ ^ τ * (1 / 2 : ℝ) ^ j :=
      (summable_geometric_two).mul_left _
    have hs : Summable fun j => C' * e j / kamDelta δ₀ j ^ τ :=
      hgeo.of_nonneg_of_le hnn hterm
    refine ⟨hs, ?_, ?_⟩
    · calc ∑' j, C' * e j / kamDelta δ₀ j ^ τ
          ≤ ∑' j : ℕ, C' * e 0 / δ₀ ^ τ * (1 / 2 : ℝ) ^ j := hs.tsum_le_tsum hterm hgeo
        _ = 2 * C' * e 0 / δ₀ ^ τ := by rw [tsum_mul_left, tsum_geometric_two]; ring
    · intro n
      have hgeo' : Summable fun j : ℕ => C' * e 0 / δ₀ ^ τ * (1 / 2 : ℝ) ^ (j + n) :=
        (summable_nat_add_iff n).2 hgeo
      calc ∑' j, C' * e (j + n) / kamDelta δ₀ (j + n) ^ τ
          ≤ ∑' j : ℕ, C' * e 0 / δ₀ ^ τ * (1 / 2 : ℝ) ^ (j + n) :=
            ((summable_nat_add_iff n).2 hs).tsum_le_tsum (fun j => hterm (j + n)) hgeo'
        _ = 2 * C' * e 0 / δ₀ ^ τ * (1 / 2) ^ n := by
            simp_rw [pow_add, ← mul_assoc]
            rw [tsum_mul_right, tsum_mul_left, tsum_geometric_two]; ring

/-- **The KAM sequence lemma in the normalization of the plan.** With `κ = Ĉ/γ⁴` and smallness
`32 Ĉ e₀ / (γ⁴ δ₀⁴) ≤ 1`, the errors tend to `0` and the total displacement
`∑_j Ĉ' e_j / (γ² δ_j²)` converges with sum `≤ 2 Ĉ' e₀ / (γ² δ₀²)`. -/
theorem kam_sequence_hat {Ĉ Ĉ' γ δ₀ : ℝ} {e : ℕ → ℝ} (hC : 0 < Ĉ) (hC' : 0 ≤ Ĉ') (hγ : 0 < γ)
    (hδ : 0 < δ₀) (he : ∀ j, 0 ≤ e j)
    (hrec : ∀ j, e (j + 1) ≤ Ĉ * e j ^ 2 / (γ ^ 4 * kamDelta δ₀ j ^ 4))
    (hsmall : 32 * Ĉ * e 0 / (γ ^ 4 * δ₀ ^ 4) ≤ 1) :
    Tendsto e atTop (𝓝 0) ∧
    Summable (fun j => Ĉ' * e j / (γ ^ 2 * kamDelta δ₀ j ^ 2)) ∧
    ∑' j, Ĉ' * e j / (γ ^ 2 * kamDelta δ₀ j ^ 2) ≤ 2 * Ĉ' * e 0 / (γ ^ 2 * δ₀ ^ 2) := by
  have hκ : 0 < Ĉ / γ ^ 4 := by positivity
  have hrec' : ∀ j, e (j + 1) ≤ Ĉ / γ ^ 4 * e j ^ 2 / kamDelta δ₀ j ^ 4 := by
    intro j; convert hrec j using 1; field_simp
  have hsmall' : 32 * (Ĉ / γ ^ 4) * e 0 / δ₀ ^ 4 ≤ 1 := by
    convert hsmall using 1; field_simp
  obtain ⟨-, hlim, hdisp⟩ := kam_sequence hκ hδ he hrec' hsmall'
  obtain ⟨hs, hsum, -⟩ := hdisp 2 (Ĉ' / γ ^ 2) (by norm_num) (by positivity)
  have heq : (fun j => Ĉ' * e j / (γ ^ 2 * kamDelta δ₀ j ^ 2)) =
      fun j => Ĉ' / γ ^ 2 * e j / kamDelta δ₀ j ^ 2 := by
    funext j; field_simp
  refine ⟨hlim, heq ▸ hs, ?_⟩
  rw [heq]
  calc _ ≤ 2 * (Ĉ' / γ ^ 2) * e 0 / δ₀ ^ 2 := hsum
    _ = _ := by field_simp

/-- **Passing to the limit.** In a complete metric space, if consecutive iterates satisfy
`dist(K_j, K_{j+1}) ≤ d_j` with `d` summable, then `K_j` converges to some `K_∞` with
`dist(K₀, K_∞) ≤ ∑ d_j`. -/
theorem kam_limit {X : Type*} [MetricSpace X] [CompleteSpace X] (K : ℕ → X) (d : ℕ → ℝ)
    (hd : ∀ j, dist (K j) (K (j + 1)) ≤ d j) (hs : Summable d) :
    ∃ Kinf : X, Tendsto K atTop (𝓝 Kinf) ∧ dist (K 0) Kinf ≤ ∑' j, d j := by
  obtain ⟨Kinf, hK⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hd hs)
  exact ⟨Kinf, hK, dist_le_tsum_of_dist_le_of_tendsto₀ d hd hs hK⟩

/-! ## Sanity checks -/

/-- Sanity (degenerate case): the zero error sequence satisfies all hypotheses. -/
theorem kam_sequence_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) ∧
    ∑' j, (1 : ℝ) * (fun _ : ℕ => (0 : ℝ)) j / kamDelta 1 j ^ 2 ≤ 2 * 1 * 0 / 1 ^ 2 := by
  obtain ⟨-, h1, h2⟩ := kam_sequence (κ := 1) (δ₀ := 1) (e := fun _ => 0) one_pos one_pos
    (fun _ => le_rfl) (fun j => by simp) (by simp)
  exact ⟨h1, (h2 2 1 (by norm_num) zero_le_one).2.1⟩

/-- The extremal sequence: equality in the recursion, `e_{j+1} = κ e_j² / δ_j⁴`. -/
def kamExact (κ δ₀ e₀ : ℝ) : ℕ → ℝ
  | 0 => e₀
  | j + 1 => κ * kamExact κ δ₀ e₀ j ^ 2 / kamDelta δ₀ j ^ 4

/-- The extremal sequence is nonnegative for `κ, e₀ ≥ 0`. -/
theorem kamExact_nonneg {κ δ₀ e₀ : ℝ} (hκ : 0 ≤ κ) (he : 0 ≤ e₀) (j : ℕ) :
    0 ≤ kamExact κ δ₀ e₀ j := by
  induction j with
  | zero => exact he
  | succ j _ => simp only [kamExact]; positivity

/-- Sanity (accepted fixture): at the threshold `κ = δ₀ = 1`, `e₀ = 1/32`, the extremal sequence
satisfies `e_j ≤ (1/32)(1/2)^{2^j−1}/16^j` and tends to `0`. -/
theorem kamExact_fixture :
    (∀ j, kamExact 1 1 (1 / 32) j ≤ 1 / 32 * (1 / 2) ^ (2 ^ j - 1) / 16 ^ j) ∧
    Tendsto (kamExact 1 1 (1 / 32)) atTop (𝓝 0) := by
  obtain ⟨h1, h2, -⟩ := kam_sequence (κ := 1) (δ₀ := 1) (e := kamExact 1 1 (1 / 32)) one_pos
    one_pos (kamExact_nonneg zero_le_one (by norm_num)) (fun j => le_of_eq (by simp [kamExact]))
    (by simp [kamExact])
  exact ⟨fun j => by simpa [kamExact] using h1 j, h2⟩

/-- Sanity (rejected fixture): without smallness (`κ = δ₀ = e₀ = 1`, so `32κe₀/δ₀⁴ = 32 > 1`)
the extremal sequence satisfies `e_j ≥ 1` for all `j`. -/
theorem kamBad_ge_one (j : ℕ) : 1 ≤ kamExact 1 1 1 j := by
  induction j with
  | zero => simp [kamExact]
  | succ j ih =>
    simp only [kamExact, kamDelta, one_mul, one_div, inv_pow]
    rw [div_inv_eq_mul]
    have h1 : 1 ≤ kamExact 1 1 1 j ^ 2 := one_le_pow₀ ih
    have h2 : (1 : ℝ) ≤ ((2 : ℝ) ^ j) ^ 4 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    nlinarith

/-- Sanity (rejected fixture): without smallness the errors do not tend to `0`. -/
theorem kamBad_not_tendsto : ¬ Tendsto (kamExact 1 1 1) atTop (𝓝 0) := by
  intro h
  have := ge_of_tendsto h (Eventually.of_forall kamBad_ge_one)
  norm_num at this

end PlasmaLean.Theory.KAM
