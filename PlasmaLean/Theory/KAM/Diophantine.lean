/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.Irrational

/-!
# Diophantine frequencies, quadratic irrationals, and the rotation number of KAM torus A

Stage K3a of the KAM route (`notes/theory/kam-route.md`, `notes/theory/kam-k3-plan.md`).

**Convention.** A real `ω` is `(γ, τ)`-Diophantine (`Diophantine ω γ τ`) if
`|k ω − m| ≥ γ / |k|^τ` for all integers `k ≠ 0`, `m`. On the standard torus
`𝕋² = (ℝ/2πℤ)²` with angles `(θ, ψ)`, the linear flow operator `L_ω = ∂_ψ + ω ∂_θ` acts on the
Fourier mode `e^{i(kθ + mψ)}` by the symbol `i(m + kω)`; for `k ≠ 0` its modulus is
`|k ω − (−m)| ≥ γ/|k|^τ`, and for `k = 0, m ≠ 0` it is `|m| ≥ 1`
(`Diophantine.abs_divisor_ge`, `Diophantine.divisor_ne_zero`). This is the small-divisor
hypothesis H5 of Figueras–Haro–Luque (FoCM 17 (2017), Thm 2.5) in dimension one.

**Quadratic irrationals.** For `x = (a + √5)/b` and its conjugate `x' = (a − √5)/b`,
`(q x − p)(q x' − p) = ((q a − p b)² − 5 q²)/b²`, and the integer `(q a − p b)² − 5 q²` is
nonzero (√5 is irrational) and divisible by any `g` that divides it identically
(`one_le_mul_conj`). Hence `|q x − p| · |q x' − p| ≥ g/b²`. Combined with
`|q x' − p| ≤ |q x − p| + |q| |x − x'|` this gives a Diophantine bound with `τ = 1` for all
`|q| ≥ Q`, and the finitely many `|q| < Q` are checked directly (`diophantine_one_of_conj`).

**Results.**
* `goldenMean_diophantine`: `Diophantine ((1 + √5)/2) ((3 − √5)/2) 1`, the classical constant
  (FHL §6 calibrate on it).
* `torusA_rotation_diophantine`: the rotational transform of KAM torus A,
  `ι = (75 + √5)/562 = [0;7,3,1,1,…]` (`torusAIota`, equal to `KamTorusA.iota`), is
  `Diophantine ι (687/5000) 1`, i.e. `γ = 0.1374` (the optimum is `ι ≈ 0.137431`, attained at
  `k = 1`). For the field-period map (torus A is `π`-periodic in `φ`, `ψ = 2φ − π/2`, so
  `∂_φ + ι ∂_θ = 2 (∂_ψ + (ι/2) ∂_θ)`) the relevant frequency is `ω = ι/2`, and
  `torusA_period_diophantine : Diophantine (ι/2) (687/10000) 1`, `γ = 0.0687` (oracle: 0.069).

**The dyadic `ι_q`.** The K2 certificate (`Design/KamTorusA`) evaluates the residual with the
dyadic `ι_q`, `|ι − ι_q| ≤ 10⁻²⁹`. A dyadic rational is never Diophantine
(`not_diophantine_of_rat`), so the KAM step must use the true `ι`; the error made by replacing
`ι_q` by `ι` in the residual is `(ι − ι_q) · D · ∂_θ K`, which is added to `‖E‖_ρ`
(it is `≤ 10⁻²⁹ ‖D ∂_θ K‖_ρ`, negligible against `‖E‖_ρ ≈ 5.8 × 10⁻²²`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

/-- `ω` is `(γ, τ)`-Diophantine: `|k ω − m| ≥ γ / |k|^τ` for all integers `k ≠ 0` and `m`. -/
def Diophantine (ω γ : ℝ) (τ : ℕ) : Prop :=
  ∀ k m : ℤ, k ≠ 0 → γ / |(k : ℝ)| ^ τ ≤ |(k : ℝ) * ω - m|

namespace Diophantine

variable {ω γ γ' : ℝ} {τ : ℕ}

/-- Diophantine constants can be decreased. -/
theorem mono (h : Diophantine ω γ τ) (hγ : γ' ≤ γ) : Diophantine ω γ' τ := fun k m hk =>
  le_trans (div_le_div_of_nonneg_right hγ (by positivity)) (h k m hk)

/-- The Diophantine property only depends on `ω` modulo `1`. -/
theorem add_int (h : Diophantine ω γ τ) (n : ℤ) : Diophantine (ω + n) γ τ := fun k m hk => by
  have := h k (m - k * n) hk
  push_cast at this
  convert this using 2; ring

/-- The Diophantine property is symmetric under `ω ↦ −ω`. -/
theorem neg (h : Diophantine ω γ τ) : Diophantine (-ω) γ τ := fun k m hk => by
  have := h (-k) m (neg_ne_zero.2 hk)
  push_cast at this
  rw [abs_neg] at this
  convert this using 1; ring_nf

/-- The small divisor `m + k ω` of `∂_ψ + ω ∂_θ` on mode `(k, m)`, `k ≠ 0`, is at least
`γ / |k|^τ`. -/
theorem abs_divisor_ge (h : Diophantine ω γ τ) {k : ℤ} (hk : k ≠ 0) (m : ℤ) :
    γ / |(k : ℝ)| ^ τ ≤ |(m : ℝ) + k * ω| := by
  have := h k (-m) hk
  push_cast at this
  rwa [sub_neg_eq_add, add_comm] at this

/-- For `γ > 0` the divisor `m + k ω` vanishes only at the zero mode. -/
theorem divisor_ne_zero (h : Diophantine ω γ τ) (hγ : 0 < γ) {k m : ℤ} (hkm : (k, m) ≠ (0, 0)) :
    (m : ℝ) + k * ω ≠ 0 := by
  by_cases hk : k = 0
  · subst hk
    have hm : m ≠ 0 := fun hm => hkm (by simp [hm])
    simpa using hm
  · intro h0
    have := h.abs_divisor_ge hk m
    rw [h0, abs_zero] at this
    have : 0 < γ / |(k : ℝ)| ^ τ := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    linarith

/-- A Diophantine constant is at most `1/2` (take `k = 1` and `m` the nearest integer). -/
theorem le_half (h : Diophantine ω γ τ) : γ ≤ 1 / 2 := by
  have := h 1 (round ω) one_ne_zero
  simp only [Int.cast_one, abs_one, one_pow, div_one, one_mul] at this
  exact this.trans (abs_sub_round ω)

end Diophantine

/-- A rational number is not Diophantine for any `γ > 0` (the divisor vanishes at `k = q`). -/
theorem not_diophantine_of_rat (r : ℚ) {γ : ℝ} (hγ : 0 < γ) (τ : ℕ) :
    ¬ Diophantine (r : ℝ) γ τ := by
  intro h
  have hd : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_nz
  have := h r.den r.num hd
  have hr : ((r.den : ℤ) : ℝ) * (r : ℝ) - (r.num : ℝ) = 0 := by
    push_cast
    rw [Rat.cast_def]
    field_simp
    ring
  rw [hr, abs_zero] at this
  have : 0 < γ / |((r.den : ℤ) : ℝ)| ^ τ := by
    have : ((r.den : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd
    positivity
  linarith

/-- Sanity: `0` is not Diophantine (the trivial degenerate case). -/
theorem not_diophantine_zero {γ : ℝ} (hγ : 0 < γ) (τ : ℕ) : ¬ Diophantine 0 γ τ := by
  simpa using not_diophantine_of_rat 0 hγ τ

/-- Sanity: every `ω` is `(0, τ)`-Diophantine (the hypothesis is vacuous for `γ = 0`). -/
theorem diophantine_zero_gamma (ω : ℝ) (τ : ℕ) : Diophantine ω 0 τ := fun _ _ _ => by
  simp

/-! ## Quadratic irrationals -/

/-- `√5` is irrational. -/
theorem irrational_sqrt_five : Irrational (√5) := by norm_num

/-- No integer square equals `5` times a nonzero integer square. -/
theorem sq_ne_five_mul_sq {n q : ℤ} (hq : q ≠ 0) : n ^ 2 ≠ 5 * q ^ 2 := by
  intro h
  apply irrational_sqrt_five
  refine ⟨(|n| : ℚ) / |q|, ?_⟩
  have hq' : (0 : ℝ) < |(q : ℝ)| := by positivity
  have hsq : ((|n| : ℝ) / |(q : ℝ)|) ^ 2 = 5 := by
    rw [div_pow, sq_abs, sq_abs, div_eq_iff (by positivity)]
    exact_mod_cast h
  push_cast
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- **Norm bound for `(a + √5)/b`.** If `g > 0` divides `(q a − p b)² − 5 q²` for all integers
`p, q`, then `|q x − p| · |q x' − p| ≥ g / b²` for `x = (a + √5)/b`, `x' = (a − √5)/b`,
`q ≠ 0`. -/
theorem one_le_mul_conj {a b g : ℤ} (hb : b ≠ 0) (hg : 0 < g)
    (hdiv : ∀ p q : ℤ, g ∣ (q * a - p * b) ^ 2 - 5 * q ^ 2) {p q : ℤ} (hq : q ≠ 0) :
    1 ≤ ((b : ℝ) ^ 2 / g) *
      (|(q : ℝ) * ((a + √5) / b) - p| * |(q : ℝ) * ((a - √5) / b) - p|) := by
  set N : ℤ := (q * a - p * b) ^ 2 - 5 * q ^ 2 with hN
  have hN0 : N ≠ 0 := fun h0 =>
    sq_ne_five_mul_sq (n := q * a - p * b) hq (by rw [hN] at h0; linarith)
  have hgN : g ≤ |N| := Int.le_of_dvd (abs_pos.2 hN0) ((dvd_abs _ _).2 (hdiv p q))
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hprod : ((q : ℝ) * ((a + √5) / b) - p) * ((q : ℝ) * ((a - √5) / b) - p) =
      (N : ℝ) / b ^ 2 := by
    rw [hN]; push_cast
    field_simp
    linear_combination (-(q : ℝ) ^ 2) * hs
  rw [← abs_mul, hprod, abs_div, abs_of_pos (by positivity : (0 : ℝ) < b ^ 2)]
  have hgR : (g : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast hgN
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  rw [div_mul_div_comm, le_div_iff₀ (mul_pos hg' hb2), one_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left hgR hb2.le

/-- **Diophantine criterion with `τ = 1` from a conjugate norm bound.** Suppose
`A |q x − p| |q x' − p| ≥ 1` for all `q ≠ 0`, that `A (γ²/Q² + γ |x − x'|) ≤ 1`, and that the
finitely many denominators `0 < |q| < Q` satisfy the Diophantine bound directly. Then `x` is
`(γ, 1)`-Diophantine. -/
theorem diophantine_one_of_conj {x x' A γ : ℝ} {Q : ℕ} (hA : 0 < A) (hQ : 1 ≤ Q)
    (hnorm : ∀ p q : ℤ, q ≠ 0 → 1 ≤ A * (|(q : ℝ) * x - p| * |(q : ℝ) * x' - p|))
    (hsmall : A * (γ ^ 2 / (Q : ℝ) ^ 2 + γ * |x - x'|) ≤ 1)
    (hlow : ∀ q p : ℤ, q ≠ 0 → |q| < Q → γ / |(q : ℝ)| ≤ |(q : ℝ) * x - p|) :
    Diophantine x γ 1 := by
  intro k m hk
  rw [pow_one]
  by_cases hkQ : |k| < Q
  · exact hlow k m hk hkQ
  push Not at hkQ
  by_contra hlt
  push Not at hlt
  set X := |(k : ℝ) * x - m|
  set K := |(k : ℝ)|
  set d := |x - x'|
  have hQK : (Q : ℝ) ≤ K := by
    have : ((Q : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hkQ
    simpa [K] using this
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hK : 0 < K := by linarith
  have hX0 : 0 ≤ X := abs_nonneg _
  have hd0 : 0 ≤ d := abs_nonneg _
  have hconj : |(k : ℝ) * x' - m| ≤ X + K * d := by
    have : (k : ℝ) * x' - m = ((k : ℝ) * x - m) - k * (x - x') := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
  have h1 := hnorm m k hk
  have h2 : X * |(k : ℝ) * x' - m| ≤ X * (X + K * d) := mul_le_mul_of_nonneg_left hconj hX0
  have h3 : X * (X + K * d) < (γ / K) * (γ / K + K * d) := by
    have hγK : 0 < γ / K := lt_of_le_of_lt hX0 hlt
    calc X * (X + K * d) ≤ X * (γ / K + K * d) := by
          apply mul_le_mul_of_nonneg_left _ hX0; linarith
      _ < (γ / K) * (γ / K + K * d) := by
          apply mul_lt_mul_of_pos_right hlt; positivity
  have h4 : (γ / K) * (γ / K + K * d) ≤ γ ^ 2 / (Q : ℝ) ^ 2 + γ * d := by
    have : (γ / K) * (γ / K + K * d) = γ ^ 2 / K ^ 2 + γ * d := by
      field_simp
    rw [this]
    gcongr
  have : 1 < A * (γ ^ 2 / (Q : ℝ) ^ 2 + γ * d) := by
    calc (1 : ℝ) ≤ A * (X * |(k : ℝ) * x' - m|) := h1
      _ < A * ((γ / K) * (γ / K + K * d)) := by
          apply mul_lt_mul_of_pos_left (lt_of_le_of_lt h2 h3) hA
      _ ≤ A * (γ ^ 2 / (Q : ℝ) ^ 2 + γ * d) := mul_le_mul_of_nonneg_left h4 hA.le
  linarith

/-! ## The golden mean -/

/-- **Golden mean.** `(1 + √5)/2` is `((3 − √5)/2, 1)`-Diophantine, the classical constant:
`|q φ − p| ≥ (3 − √5)/(2|q|)` for all `q ≠ 0`. -/
theorem goldenMean_diophantine : Diophantine ((1 + √5) / 2) ((3 - √5) / 2) 1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs3 : √5 < 3 := by nlinarith [Real.sqrt_nonneg 5]
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  refine diophantine_one_of_conj (x' := (1 - √5) / 2) (A := 1) (Q := 1)
    one_pos le_rfl ?_ ?_ ?_
  · intro p q hq
    have := one_le_mul_conj (a := 1) (b := 2) (g := 4) (by norm_num) (by norm_num)
      (fun p q => ⟨p ^ 2 - p * q - q ^ 2, by ring⟩) (p := p) hq
    norm_num at this ⊢
    exact this
  · have : (1 + √5) / 2 - (1 - √5) / 2 = √5 := by ring
    rw [this, abs_of_nonneg hs0]
    nlinarith
  · intro q p hq hq1
    exfalso
    have : (1 : ℤ) ≤ |q| := Int.one_le_abs hq
    push_cast at hq1
    omega

/-! ## The rotational transform of KAM torus A -/

/-- The rotational transform of KAM torus A, `ι = (75 + √5)/562 = [0;7,3,1,1,1,…]`
(definitionally `KamTorusA.iota` of `Design/KamTorusA`). It is a root of `281 x² − 75 x + 5`. -/
def torusAIota : ℝ := (75 + √5) / 562

/-- Enclosure `0.1374 < ι < 0.1375`. -/
theorem torusAIota_bounds : 687 / 5000 < torusAIota ∧ torusAIota < 1375 / 10000 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlo : 2236 / 1000 < √5 := by nlinarith
  have hhi : √5 < 22361 / 10000 := by nlinarith
  unfold torusAIota
  constructor <;> linarith

/-- `ι` is a root of the primitive quadratic `281 x² − 75 x + 5` (discriminant `5`). -/
theorem torusAIota_root : 281 * torusAIota ^ 2 - 75 * torusAIota + 5 = 0 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold torusAIota
  linear_combination (281 / 562 ^ 2 : ℝ) * hs

/-- **The rotational transform of torus A is Diophantine:** `|k ι − m| ≥ 0.1374/|k|` for all
`k ≠ 0`. Proof: the conjugate norm bound `281 |qι − p||qι' − p| ≥ 1` (from
`(75q − 562p)² − 5q² = 1124 (281p² − 75pq + 5q²)`), `281 (γ²/9 + γ √5/281) ≈ 0.897 ≤ 1` for
`|q| ≥ 3`, and a direct check for `|q| ∈ {1, 2}`. The constant is within `3 × 10⁻⁵` of optimal
(`k = 1, m = 0` gives `|ι| ≈ 0.137431`). -/
theorem torusA_rotation_diophantine : Diophantine ((75 + √5) / 562) (687 / 5000) 1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hhi : √5 < 22361 / 10000 := by nlinarith
  obtain ⟨hιlo, hιhi⟩ := torusAIota_bounds
  unfold torusAIota at hιlo hιhi
  refine diophantine_one_of_conj (x' := (75 - √5) / 562) (A := 281) (Q := 3)
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · intro p q hq
    have := one_le_mul_conj (a := 75) (b := 562) (g := 1124) (by norm_num) (by norm_num)
      (fun p q => ⟨281 * p ^ 2 - 75 * p * q + 5 * q ^ 2, by ring⟩) (p := p) hq
    norm_num at this ⊢
    exact this
  · have : (75 + √5) / 562 - (75 - √5) / 562 = √5 / 281 := by ring
    rw [this, abs_of_nonneg (by positivity)]
    norm_num
    nlinarith
  · intro q p hq hq3
    push_cast at hq3
    rw [abs_lt] at hq3
    -- reduce to `q ∈ {1, 2}` using `|(-q) x - (-p)| = |q x - p|`
    have key : ∀ q' : ℤ, (q' = 1 ∨ q' = 2) → ∀ p' : ℤ,
        687 / 5000 / |(q' : ℝ)| ≤ |(q' : ℝ) * ((75 + √5) / 562) - p'| := by
      intro q' hq' p'
      rcases le_or_gt p' 0 with hp | hp
      · have hp' : (p' : ℝ) ≤ 0 := by exact_mod_cast hp
        rcases hq' with rfl | rfl <;> norm_num <;> rw [le_abs] <;> left <;> linarith
      · have hp' : (1 : ℝ) ≤ p' := by exact_mod_cast hp
        rcases hq' with rfl | rfl <;> norm_num <;> rw [le_abs] <;> right <;> linarith
    rcases (by omega : q = 1 ∨ q = 2 ∨ q = -1 ∨ q = -2) with h | h | h | h
    · exact key q (Or.inl h) p
    · exact key q (Or.inr h) p
    · have := key (-q) (Or.inl (by omega)) (-p)
      push_cast at this
      rwa [abs_neg, show -(q : ℝ) * ((75 + √5) / 562) - -(p : ℝ) =
        -((q : ℝ) * ((75 + √5) / 562) - p) by ring, abs_neg] at this
    · have := key (-q) (Or.inr (by omega)) (-p)
      push_cast at this
      rwa [abs_neg, show -(q : ℝ) * ((75 + √5) / 562) - -(p : ℝ) =
        -((q : ℝ) * ((75 + √5) / 562) - p) by ring, abs_neg] at this

/-- **Field-period form.** Torus A is `π`-periodic in `φ`; in the angle `ψ = 2φ − π/2` the flow
`∂_φ + ι ∂_θ = 2 (∂_ψ + (ι/2) ∂_θ)` has frequency `ω = ι/2`, which is `(0.0687, 1)`-Diophantine
(the oracle's period-map value is `γ ≈ 0.069`). -/
theorem torusA_period_diophantine : Diophantine (torusAIota / 2) (687 / 10000) 1 := by
  intro k m hk
  have := torusA_rotation_diophantine k (2 * m) hk
  unfold torusAIota
  push_cast at this
  rw [pow_one] at this ⊢
  have e : (k : ℝ) * ((75 + √5) / 562 / 2) - m = ((k : ℝ) * ((75 + √5) / 562) - 2 * m) / 2 := by
    ring
  rw [e, abs_div, abs_two]
  have e2 : (687 / 10000 : ℝ) / |(k : ℝ)| = 687 / 5000 / |(k : ℝ)| / 2 := by ring
  rw [e2]
  linarith

/-- The divisor bound in the exact form used by torus A's cohomological equation:
`|2m + kι| ≥ 0.1374/|k|` for `k ≠ 0` (the symbol of `∂_φ + ι ∂_θ` on `e^{i(kθ + mψ)}` is
`i(2m + kι)`). -/
theorem torusA_divisor_ge {k : ℤ} (hk : k ≠ 0) (m : ℤ) :
    687 / 5000 / |(k : ℝ)| ≤ |2 * (m : ℝ) + k * torusAIota| := by
  have := torusA_rotation_diophantine.abs_divisor_ge hk (2 * m)
  push_cast at this
  simpa [torusAIota] using this

/-- Sanity (rejected fixture): torus A's rotation number is not `(0.1375, 1)`-Diophantine, so
`γ = 0.1374` is essentially optimal. -/
theorem torusA_not_diophantine_large : ¬ Diophantine ((75 + √5) / 562) (1375 / 10000) 1 := by
  intro h
  have := h 1 0 one_ne_zero
  have hb := torusAIota_bounds.2
  unfold torusAIota at hb
  have hpos := torusAIota_bounds.1
  unfold torusAIota at hpos
  norm_num at this
  rw [abs_of_pos (by linarith)] at this
  linarith

end PlasmaLean.Theory.KAM
