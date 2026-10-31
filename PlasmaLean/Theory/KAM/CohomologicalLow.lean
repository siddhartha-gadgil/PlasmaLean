/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.Cohomological
public import PlasmaLean.Theory.KAM.StripAlgebra

/-!
# The cohomological equation with exact low small divisors

Module (2) of the Dommaschk KAM plan (`notes/theory/dommaschk-kam-certificate.md`, §3.3 and §6,
gap 3). The Rüssmann estimate `cohSol_estimate` bounds the small-divisor factor of every mode by
one Diophantine constant: `sup_k |k| e^{−δ|k|}/γ ≤ 1/(eγδ)`. When `γ` is attained only at the
lowest modes (for the Dommaschk torus A, `ω = |ι_A|/2 ≈ 0.1193` is attained at `k = 1`, while
`|k| ‖kω‖ ≥ 0.3645` for `|k| ≥ 2`) this is loose: the factor of the low modes is only
`e^{−δ}/|m + kω|`, which is bounded, not of order `1/δ`. This is the idea of
Figueras–Haro–Luque, *Rigorous computer-assisted application of KAM theory: a modern approach*,
FoCM 17 (2017), Lemma 4.3 (the finitely many low divisors are treated exactly, the tail by the
Diophantine constant).

**Hypothesis.** `DiophantineSplit ω d γ τ K`:
* (low modes) `|kω − m| ≥ d` for `0 < |k| ≤ K` and every `m`;
* (high modes) `|kω − m| ≥ γ/|k|^τ` for `|k| > K` and every `m`.
For `K = 0` the low part is vacuous and the hypothesis is `Diophantine ω γ τ`
(`diophantineSplit_zero_iff`).

**Estimate.** `cohSol_estimate_split`: `‖u‖_{r−δ} ≤ C ‖f‖_r` for `u = cohSol ω f` with
`C = max (max 1 (e^{−δ}/d)) ((τ/(eδ))^τ/γ)` (`russmannConstSplit`). For `τ = 1`, if
`eγδ ≤ d` (the low factor is below the tail factor) and `eγδ ≤ 1`, then `C = 1/(eγδ)`
(`russmannConstSplit_one_of_le`), so `cohSol_estimate_split_one` has **exactly the form of
`cohSol_estimate_one` with the high-mode constant `γ` in place of the global one**. For `K ≥ 1`,
`eγδ ≤ 1` follows from `eγδ ≤ d ≤ 1/2` (`DiophantineSplit.le_half`), so the only extra condition
is the loss threshold `δ ≤ d/(eγ)` (`cohSol_estimate_split_one_of_one_le`).

**Strip algebra.** `Bd.coh_split` is `Bd.coh` (the form consumed by `Design/KamFlowStep`) with the
split hypothesis; the qualitative facts (`Ana.coh`, `dS_coh`) need only *some* Diophantine
constant, supplied by `DiophantineSplit.toDiophantine` (constant `min d γ`).

**Reduction to the existing bound.** `Diophantine.toSplit`: a `(γ, τ)`-Diophantine `ω` is
`DiophantineSplit ω (γ/K^τ) γ τ K` for every `K ≥ 1`; `cohSol_estimate_one_of_split` re-derives
`cohSol_estimate_one` (same constant `1/(eγδ)`) through the split estimate with `K = 0`.

**Conjugate criterion.** `diophantineAbove_one_of_conj` is `diophantine_one_of_conj` for the high
modes only (`|q| > K`): the conjugate norm bound for `|q| ≥ Q`, a direct check for `K < |q| < Q`.

**Sanity.** `russmannConstSplit_one_le` (the constant is at least `1`, the `k = 0` modes), the
mode fixture `cohSol_split_single_mode` (equality case of the low bound: the single mode `(1, 0)`
has factor exactly `e^{−δ}/|ω|`), and the rejected fixture `not_diophantineSplit_of_rat`
(a rational `ω` satisfies no split hypothesis with `d, γ > 0`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

open Complex WEll1Z2

/-- **Split Diophantine hypothesis.** The low divisors (`0 < |k| ≤ K`) are bounded below by `d`,
the high ones (`|k| > K`) by `γ/|k|^τ`. -/
structure DiophantineSplit (ω d γ : ℝ) (τ K : ℕ) : Prop where
  /-- Low modes: `|kω − m| ≥ d` for `0 < |k| ≤ K`. -/
  low : ∀ k m : ℤ, k ≠ 0 → |k| ≤ (K : ℤ) → d ≤ |(k : ℝ) * ω - m|
  /-- High modes: `|kω − m| ≥ γ/|k|^τ` for `|k| > K`. -/
  high : ∀ k m : ℤ, (K : ℤ) < |k| → γ / |(k : ℝ)| ^ τ ≤ |(k : ℝ) * ω - m|

namespace DiophantineSplit

variable {ω d γ : ℝ} {τ K : ℕ}

/-- The split hypothesis is symmetric under `ω ↦ −ω` (as `Diophantine.neg`). -/
theorem neg (h : DiophantineSplit ω d γ τ K) : DiophantineSplit (-ω) d γ τ K where
  low k m hk hkK := by
    have := h.low (-k) m (neg_ne_zero.2 hk) (by rwa [abs_neg])
    push_cast at this
    convert this using 1; ring_nf
  high k m hk := by
    have := h.high (-k) m (by rwa [abs_neg])
    push_cast at this
    rw [abs_neg] at this
    convert this using 1; ring_nf

/-- Low divisor bound in the symbol form `|m + kω| ≥ d`. -/
theorem abs_divisor_ge_low (h : DiophantineSplit ω d γ τ K) {k : ℤ} (hk : k ≠ 0)
    (hkK : |k| ≤ (K : ℤ)) (m : ℤ) : d ≤ |(m : ℝ) + k * ω| := by
  have := h.low k (-m) hk hkK
  push_cast at this
  rwa [sub_neg_eq_add, add_comm] at this

/-- High divisor bound in the symbol form `|m + kω| ≥ γ/|k|^τ`. -/
theorem abs_divisor_ge_high (h : DiophantineSplit ω d γ τ K) {k : ℤ} (hkK : (K : ℤ) < |k|)
    (m : ℤ) : γ / |(k : ℝ)| ^ τ ≤ |(m : ℝ) + k * ω| := by
  have := h.high k (-m) hkK
  push_cast at this
  rwa [sub_neg_eq_add, add_comm] at this

/-- With at least one low mode, `d ≤ 1/2` (take `k = 1`, `m` the nearest integer). -/
theorem le_half (h : DiophantineSplit ω d γ τ K) (hK : 1 ≤ K) : d ≤ 1 / 2 := by
  have := h.low 1 (round ω) one_ne_zero (by rw [abs_one]; exact_mod_cast hK)
  simp only [Int.cast_one, one_mul] at this
  exact this.trans (abs_sub_round ω)

/-- **The split hypothesis gives a global Diophantine constant** `min d γ` (for `d, γ ≥ 0`): this
is what the qualitative facts `cohSol_spec`, `Ana.coh` and `dS_coh` need. -/
theorem toDiophantine (h : DiophantineSplit ω d γ τ K) (hd : 0 ≤ d) (hγ : 0 ≤ γ) :
    Diophantine ω (min d γ) τ := by
  intro k m hk
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| ^ τ := by
    have : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    exact one_le_pow₀ this
  have hmin : 0 ≤ min d γ := le_min hd hγ
  by_cases hkK : |k| ≤ (K : ℤ)
  · calc min d γ / |(k : ℝ)| ^ τ ≤ min d γ := div_le_self hmin hk1
      _ ≤ d := min_le_left _ _
      _ ≤ _ := h.low k m hk hkK
  · push Not at hkK
    calc min d γ / |(k : ℝ)| ^ τ ≤ γ / |(k : ℝ)| ^ τ :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ _ := h.high k m hkK

/-- Monotonicity in both constants. -/
theorem mono {d' γ' : ℝ} (h : DiophantineSplit ω d γ τ K) (hd : d' ≤ d) (hγ : γ' ≤ γ) :
    DiophantineSplit ω d' γ' τ K where
  low k m hk hkK := hd.trans (h.low k m hk hkK)
  high k m hk := le_trans (div_le_div_of_nonneg_right hγ (by positivity)) (h.high k m hk)

end DiophantineSplit

/-- **`K = 0`: the split hypothesis is the Diophantine hypothesis** (the low part is vacuous). -/
theorem diophantineSplit_zero_iff {ω d γ : ℝ} {τ : ℕ} :
    DiophantineSplit ω d γ τ 0 ↔ Diophantine ω γ τ := by
  constructor
  · intro h k m hk
    exact h.high k m (by simpa using abs_pos.2 hk)
  · intro h
    refine ⟨fun k m hk hkK => ?_, fun k m hkK => h k m (by simpa using hkK)⟩
    exact absurd (abs_pos.2 hk) (by simpa using hkK)

/-- **Reduction (`γ₁ = γ₂`).** A `(γ, τ)`-Diophantine `ω` satisfies the split hypothesis with the
low constant `γ/K^τ` (the Diophantine bound at the largest low mode). -/
theorem Diophantine.toSplit {ω γ : ℝ} {τ : ℕ} (h : Diophantine ω γ τ) (hγ : 0 ≤ γ) (K : ℕ) :
    DiophantineSplit ω (γ / (K : ℝ) ^ τ) γ τ K where
  low k m hk hkK := by
    refine le_trans ?_ (h k m hk)
    have hk1 : (0 : ℝ) < |(k : ℝ)| := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    have hkK' : |(k : ℝ)| ≤ K := by
      have : ((|k| : ℤ) : ℝ) ≤ ((K : ℤ) : ℝ) := by exact_mod_cast hkK
      simpa using this
    exact div_le_div_of_nonneg_left hγ (by positivity) (pow_le_pow_left₀ hk1.le hkK' τ)
  high k m hkK := h k m (by rintro rfl; rw [abs_zero] at hkK; omega)

/-! ## The split Rüssmann constant and the estimate -/

/-- The split Rüssmann constant `max (max 1 (e^{−δ}/d)) ((τ/(eδ))^τ/γ)`: `1` for the modes
`k = 0`, `e^{−δ}/d` for the low modes, the crude Rüssmann factor for the high modes. -/
def russmannConstSplit (d γ δ : ℝ) (τ : ℕ) : ℝ :=
  max (max 1 (Real.exp (-δ) / d)) (((τ : ℝ) / (Real.exp 1 * δ)) ^ τ / γ)

/-- Sanity: the split constant is at least `1`. -/
theorem russmannConstSplit_one_le (d γ δ : ℝ) (τ : ℕ) : 1 ≤ russmannConstSplit d γ δ τ :=
  (le_max_left _ _).trans (le_max_left _ _)

/-- **`τ = 1`: the split constant is `1/(eγδ)`** as soon as the low factor `e^{−δ}/d` is below it,
which holds if `eγδ ≤ d`, and `eγδ ≤ 1`. -/
theorem russmannConstSplit_one_of_le {d γ δ : ℝ} (hd : 0 < d) (hγ : 0 < γ) (hδ : 0 < δ)
    (hone : Real.exp 1 * γ * δ ≤ 1) (hlow : Real.exp 1 * γ * δ ≤ d) :
    russmannConstSplit d γ δ 1 = 1 / (Real.exp 1 * γ * δ) := by
  have he := Real.exp_pos 1
  have hp : 0 < Real.exp 1 * γ * δ := by positivity
  have e2 : (((1 : ℕ) : ℝ) / (Real.exp 1 * δ)) ^ 1 / γ = 1 / (Real.exp 1 * γ * δ) := by
    push_cast; field_simp
  unfold russmannConstSplit
  rw [e2, max_eq_right]
  refine max_le ?_ ?_
  · rw [le_div_iff₀ hp, one_mul]; exact hone
  · rw [div_le_div_iff₀ hd hp, one_mul]
    have : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith

/-- **Termwise split small-divisor bound.** Under `DiophantineSplit ω d γ τ K` with `d, γ, δ > 0`,
`|u_{k,m}| e^{(r−δ)(|k|+|m|)} ≤ C |f_{k,m}| e^{r(|k|+|m|)}` for `u = cohSol ω f`, with
`C = russmannConstSplit d γ δ τ`. -/
theorem cohSol_termwise_split {ω d γ δ : ℝ} {τ K : ℕ} (hD : DiophantineSplit ω d γ τ K)
    (hd : 0 < d) (hγ : 0 < γ) (hδ : 0 < δ) (r : ℝ) (f : ℤ × ℤ → ℂ) (km : ℤ × ℤ) :
    ‖cohSol ω f km‖ * weight (r - δ) km ≤
      russmannConstSplit d γ δ τ * (‖f km‖ * weight r km) := by
  obtain ⟨k, m⟩ := km
  rw [norm_cohSol, weight_sub]
  have hw := weight_pos r (k, m)
  have hfn := norm_nonneg (f (k, m))
  have hfw : 0 ≤ ‖f (k, m)‖ * weight r (k, m) := mul_nonneg hfn hw.le
  -- it suffices to bound the factor `e^{−δ(|k|+|m|)}/|m + kω|`
  suffices key : 1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m)) ≤
      russmannConstSplit d γ δ τ by
    calc ‖f (k, m)‖ / |divisor ω (k, m)| *
          (weight r (k, m) * Real.exp (-δ * modeSize (k, m)))
        = (1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m))) *
            (‖f (k, m)‖ * weight r (k, m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key hfw
  have hexp1 : Real.exp (-δ * modeSize (k, m)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [modeSize_nonneg (k, m)])
  have hkms : |(k : ℝ)| ≤ modeSize (k, m) := by
    simp only [modeSize]; linarith [abs_nonneg (m : ℝ)]
  by_cases hk : k = 0
  · -- `k = 0`: the divisor is the integer `m`
    subst hk
    refine le_trans ?_ (russmannConstSplit_one_le d γ δ τ)
    by_cases hm : m = 0
    · subst hm; simp [divisor]
    · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      simp only [divisor, Int.cast_zero, zero_mul, add_zero]
      calc 1 / |(m : ℝ)| * Real.exp (-δ * modeSize (0, m)) ≤ 1 * 1 := by
            apply mul_le_mul _ hexp1 (Real.exp_pos _).le zero_le_one
            rw [div_le_one (by positivity)]; exact hm1
        _ = 1 := one_mul 1
  have hK1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  by_cases hkK : |k| ≤ (K : ℤ)
  · -- low mode: `1/|d| ≤ 1/d` and `e^{−δ(|k|+|m|)} ≤ e^{−δ}`
    have hdiv : d ≤ |divisor ω (k, m)| := by
      simpa [divisor] using hD.abs_divisor_ge_low hk hkK m
    have hdpos : 0 < |divisor ω (k, m)| := lt_of_lt_of_le hd hdiv
    have hexpd : Real.exp (-δ * modeSize (k, m)) ≤ Real.exp (-δ) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc 1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m))
        ≤ 1 / d * Real.exp (-δ) :=
          mul_le_mul (one_div_le_one_div_of_le hd hdiv) hexpd (Real.exp_pos _).le
            (by positivity)
      _ = Real.exp (-δ) / d := by ring
      _ ≤ _ := (le_max_right _ _).trans (le_max_left _ _)
  · -- high mode: as in `cohSol_termwise`, with `γ`
    push Not at hkK
    have hKpos : 0 < |(k : ℝ)| := by linarith
    have hdiv := hD.abs_divisor_ge_high hkK m
    have hdiv' : γ / |(k : ℝ)| ^ τ ≤ |divisor ω (k, m)| := by simpa [divisor] using hdiv
    have hdpos : 0 < |divisor ω (k, m)| := lt_of_lt_of_le (by positivity) hdiv'
    have hinv : 1 / |divisor ω (k, m)| ≤ |(k : ℝ)| ^ τ / γ := by
      rw [div_le_div_iff₀ hdpos hγ, one_mul]
      have := (div_le_iff₀ (by positivity)).1 hdiv'
      linarith
    have hexpk : Real.exp (-δ * modeSize (k, m)) ≤ Real.exp (-δ * |(k : ℝ)|) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hsup := pow_mul_exp_neg_le (abs_nonneg (k : ℝ)) hδ τ
    calc 1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m))
        ≤ |(k : ℝ)| ^ τ / γ * Real.exp (-δ * |(k : ℝ)|) :=
          mul_le_mul hinv hexpk (Real.exp_pos _).le (by positivity)
      _ = (|(k : ℝ)| ^ τ * Real.exp (-δ * |(k : ℝ)|)) / γ := by ring
      _ ≤ ((τ : ℝ) / (Real.exp 1 * δ)) ^ τ / γ := by gcongr
      _ ≤ _ := le_max_right _ _

/-- **Rüssmann estimate with exact low divisors** (FHL 2017, Lemma 4.3). Under
`DiophantineSplit ω d γ τ K` (`d, γ, δ > 0`) and `‖f‖_r < ∞`, `u = cohSol ω f` satisfies
`‖u‖_{r−δ} < ∞` and `‖u‖_{r−δ} ≤ max (max 1 (e^{−δ}/d)) ((τ/(eδ))^τ/γ) · ‖f‖_r`. -/
theorem cohSol_estimate_split {ω d γ δ r : ℝ} {τ K : ℕ} (hD : DiophantineSplit ω d γ τ K)
    (hd : 0 < d) (hγ : 0 < γ) (hδ : 0 < δ) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ russmannConstSplit d γ δ τ * wnorm r f :=
  wnorm_le_of_termwise hf (cohSol_termwise_split hD hd hγ hδ r f)

/-- **The `τ = 1` form, same shape as `cohSol_estimate_one`:** if `eγδ ≤ d` and `eγδ ≤ 1`, then
`‖u‖_{r−δ} ≤ ‖f‖_r/(eγδ)` with the **high-mode** constant `γ`. -/
theorem cohSol_estimate_split_one {ω d γ δ r : ℝ} {K : ℕ} (hD : DiophantineSplit ω d γ 1 K)
    (hd : 0 < d) (hγ : 0 < γ) (hδ : 0 < δ) (hone : Real.exp 1 * γ * δ ≤ 1)
    (hlow : Real.exp 1 * γ * δ ≤ d) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ wnorm r f / (Real.exp 1 * γ * δ) := by
  obtain ⟨h1, h2⟩ := cohSol_estimate_split hD hd hγ hδ hf
  rw [russmannConstSplit_one_of_le hd hγ hδ hone hlow] at h2
  exact ⟨h1, by rw [div_eq_mul_one_div, mul_comm]; exact h2⟩

/-- **The `τ = 1` form with at least one low mode:** only the loss threshold `eγδ ≤ d` is needed
(`eγδ ≤ 1` follows from `d ≤ 1/2`). -/
theorem cohSol_estimate_split_one_of_one_le {ω d γ δ r : ℝ} {K : ℕ}
    (hD : DiophantineSplit ω d γ 1 K) (hK : 1 ≤ K) (hd : 0 < d) (hγ : 0 < γ) (hδ : 0 < δ)
    (hlow : Real.exp 1 * γ * δ ≤ d) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ wnorm r f / (Real.exp 1 * γ * δ) :=
  cohSol_estimate_split_one hD hd hγ hδ (by linarith [hD.le_half hK]) hlow hf

/-- **Reduction to the existing estimate.** `cohSol_estimate_one` (global constant `γ`) is the
split estimate with `K = 0` and the (vacuous) low constant `d = eγδ`. -/
theorem cohSol_estimate_one_of_split {ω γ δ r : ℝ} (hD : Diophantine ω γ 1) (hγ : 0 < γ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 2 / Real.exp 1) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ wnorm r f / (Real.exp 1 * γ * δ) := by
  have he := Real.exp_pos 1
  have hone : Real.exp 1 * γ * δ ≤ 1 := by
    have h1 : Real.exp 1 * δ ≤ 2 := by rw [le_div_iff₀ he] at hδ2; linarith
    nlinarith [hD.le_half]
  exact cohSol_estimate_split_one (d := Real.exp 1 * γ * δ) (K := 0)
    (diophantineSplit_zero_iff.2 hD) (by positivity) hγ hδ hone le_rfl hf

/-! ## The strip-algebra form (as consumed by the KAM step) -/

/-- **`Bd.coh` with exact low divisors:** `‖coh ω x‖_{ρ−δ} ≤ ‖x‖_ρ/(eγδ)` for `0 < δ ≤ ρ`, under
`DiophantineSplit ω d γ 1 K` with `K ≥ 1` and the loss threshold `eγδ ≤ d`. -/
theorem Bd.coh_split {ω d γ ρ δ B : ℝ} {K : ℕ} {x : FA} (hD : DiophantineSplit ω d γ 1 K)
    (hK : 1 ≤ K) (hd : 0 < d) (hγ : 0 < γ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hlow : Real.exp 1 * γ * δ ≤ d) (hx : Bd ρ x B) :
    Bd (ρ - δ) (KAM.coh ω x) (B / (Real.exp 1 * γ * δ)) := by
  obtain ⟨h1, h2⟩ := cohSol_estimate_split_one_of_one_le hD hK hd hγ hδ hlow hx.1
  have h0 : InWeighted 0 (cohSol ω (coeff x)) := h1.mono (by linarith)
  have hc : coeff (KAM.coh ω x) = cohSol ω (coeff x) := by
    funext n; simp [KAM.coh, h0]
  rw [Bd, hc]
  refine ⟨h1, h2.trans ?_⟩
  gcongr
  exact hx.2

/-! ## A conjugate-norm criterion for the high modes -/

/-- **High-mode Diophantine criterion from a conjugate norm bound** (`diophantine_one_of_conj`
restricted to `|q| > K`). If `A |q x − p| |q x' − p| ≥ 1` for `q ≠ 0`,
`A (γ²/Q² + γ |x − x'|) ≤ 1`, and the denominators `K < |q| < Q` satisfy the bound directly,
then `|q x − p| ≥ γ/|q|` for all `|q| > K`. -/
theorem diophantineAbove_one_of_conj {x x' A γ : ℝ} {K Q : ℕ} (hA : 0 < A) (hQ : 1 ≤ Q)
    (hnorm : ∀ p q : ℤ, q ≠ 0 → 1 ≤ A * (|(q : ℝ) * x - p| * |(q : ℝ) * x' - p|))
    (hsmall : A * (γ ^ 2 / (Q : ℝ) ^ 2 + γ * |x - x'|) ≤ 1)
    (hmid : ∀ q p : ℤ, (K : ℤ) < |q| → |q| < Q → γ / |(q : ℝ)| ≤ |(q : ℝ) * x - p|) :
    ∀ k m : ℤ, (K : ℤ) < |k| → γ / |(k : ℝ)| ^ 1 ≤ |(k : ℝ) * x - m| := by
  intro k m hkK
  have hk : k ≠ 0 := by rintro rfl; rw [abs_zero] at hkK; omega
  rw [pow_one]
  by_cases hkQ : |k| < Q
  · exact hmid k m hkK hkQ
  push Not at hkQ
  by_contra hlt
  push Not at hlt
  set X := |(k : ℝ) * x - m|
  set Kk := |(k : ℝ)|
  set dd := |x - x'|
  have hQK : (Q : ℝ) ≤ Kk := by
    have : ((Q : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hkQ
    simpa [Kk] using this
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hKk : 0 < Kk := by linarith
  have hX0 : 0 ≤ X := abs_nonneg _
  have hd0 : 0 ≤ dd := abs_nonneg _
  have hconj : |(k : ℝ) * x' - m| ≤ X + Kk * dd := by
    have : (k : ℝ) * x' - m = ((k : ℝ) * x - m) - k * (x - x') := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
  have h1 := hnorm m k hk
  have h2 : X * |(k : ℝ) * x' - m| ≤ X * (X + Kk * dd) := mul_le_mul_of_nonneg_left hconj hX0
  have h3 : X * (X + Kk * dd) < (γ / Kk) * (γ / Kk + Kk * dd) := by
    have hγK : 0 < γ / Kk := lt_of_le_of_lt hX0 hlt
    calc X * (X + Kk * dd) ≤ X * (γ / Kk + Kk * dd) := by
          apply mul_le_mul_of_nonneg_left _ hX0; linarith
      _ < (γ / Kk) * (γ / Kk + Kk * dd) := by
          apply mul_lt_mul_of_pos_right hlt; positivity
  have h4 : (γ / Kk) * (γ / Kk + Kk * dd) ≤ γ ^ 2 / (Q : ℝ) ^ 2 + γ * dd := by
    have : (γ / Kk) * (γ / Kk + Kk * dd) = γ ^ 2 / Kk ^ 2 + γ * dd := by
      field_simp
    rw [this]
    gcongr
  have : 1 < A * (γ ^ 2 / (Q : ℝ) ^ 2 + γ * dd) := by
    calc (1 : ℝ) ≤ A * (X * |(k : ℝ) * x' - m|) := h1
      _ < A * ((γ / Kk) * (γ / Kk + Kk * dd)) := by
          apply mul_lt_mul_of_pos_left (lt_of_le_of_lt h2 h3) hA
      _ ≤ A * (γ ^ 2 / (Q : ℝ) ^ 2 + γ * dd) := mul_le_mul_of_nonneg_left h4 hA.le
  linarith

/-! ## Sanity checks -/

/-- Sanity (equality case of the low bound): for the single mode `(1, 0)` the solution has
`|u_{1,0}| e^{(r−δ)} = (e^{−δ}/|ω|) |f_{1,0}| e^{r}`, so the low factor `e^{−δ}/d` of
`russmannConstSplit` is attained when `d = |ω|`. -/
theorem cohSol_split_single_mode (ω r δ : ℝ) (c : ℂ) :
    ‖cohSol ω (fun km => if km = (1, 0) then c else 0) (1, 0)‖ * weight (r - δ) (1, 0) =
      Real.exp (-δ) / |ω| * (‖c‖ * weight r (1, 0)) := by
  rw [norm_cohSol, weight_sub]
  simp only [↓reduceIte, divisor, Int.cast_zero, Int.cast_one, one_mul, zero_add, modeSize,
    abs_one, abs_zero, add_zero, mul_one]
  ring

/-- Sanity (rejected fixture): a rational `ω` satisfies no split hypothesis with `d, γ > 0`
(it would make `ω` Diophantine with constant `min d γ > 0`). -/
theorem not_diophantineSplit_of_rat (q : ℚ) {d γ : ℝ} (hd : 0 < d) (hγ : 0 < γ) (τ K : ℕ) :
    ¬ DiophantineSplit (q : ℝ) d γ τ K := fun h =>
  not_diophantine_of_rat q (lt_min hd hγ) τ (h.toDiophantine hd.le hγ.le)

end PlasmaLean.Theory.KAM
