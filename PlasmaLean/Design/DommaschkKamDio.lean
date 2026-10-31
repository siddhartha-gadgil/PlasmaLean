/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.CohomologicalLow
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Small divisors of the Dommaschk torus A

Module (4) of the Dommaschk KAM plan (`notes/theory/dommaschk-kam-certificate.md`, §6; oracle
`notes/theory/dommaschk-qa.md` §25). Torus A of the Dommaschk target has the noble rotational
transform `ι_A = −(19 + √5)/89 ≈ −0.238608`. In the field-period angle `ψ = 2φ` the flow
`∂_φ + ι ∂_θ = 2 (∂_ψ + (ι/2) ∂_θ)` has frequency `ι_A/2 = −ω_A` with

`ω_A = |ι_A|/2 = (19 + √5)/178 = [0; 8, 2, 1, 1, 1, …] ≈ 0.1193038`,

a root of the primitive quadratic `89 x² − 19 x + 1` (discriminant `5`; `dkOmegaA_root`).

**Small divisors.** `|kω_A − m|` is smallest at `k = 1` (`ω_A` itself), while for `|k| ≥ 2`,
`|k| ‖kω_A‖ ≥ 0.364559`, attained at `k = 8` (`1 − 8ω_A`; then `0.435` at `k = 25`, tending to
`1/√5`). Hence
* `dkOmegaA_split : DiophantineSplit ω_A 0.1193 0.3645 1 1` (low divisor `|ω_A − m| ≥ 0.1193`,
  high constant `γ₂ = 0.3645`), proved by the conjugate norm bound
  `89 |qω − p| |qω' − p| ≥ 1` (from `(19q − 178p)² − 5q² = 356 (89p² − 19pq + q²)`),
  `89 (γ₂²/81 + γ₂ √5/89) ≈ 0.961 ≤ 1` for `|q| ≥ 9`, and a direct check of `2 ≤ |q| ≤ 8`
  (where `qω_A ∈ (0, 1)`);
* `dkIotaA_period_split`: the same for the signed frequency `ι_A/2` used by the KAM step;
* `dkOmegaA_diophantine : Diophantine ω_A 0.1193 1` (the global constant, `k = 1`).

**Gain over `cohSol_estimate`.** `dkIotaA_cohSol_estimate`: for `0 < δ ≤ 3/25` the
cohomological solution obeys `‖u‖_{r−δ} ≤ ‖f‖_r/(e γ₂ δ)` with `γ₂ = 0.3645`, against
`‖f‖_r/(e · 0.1193 · δ)` from the global Diophantine constant: the Rüssmann factor shrinks by
`3645/1193 ≈ 3.055` (`dk_russmann_gain`). `dkIotaA_Bd_coh` is the strip-algebra form, a drop-in
for `Bd.coh` in `Design/KamFlowStep`.

**Sanity.** The rejected fixtures `dkOmegaA_not_split_low` (`d = 0.1194` fails at `k = 1`) and
`dkOmegaA_not_split_high` (`γ₂ = 0.3646` fails at `k = 8`, `m = 1`): both constants are within
`10⁻⁴` of optimal.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamDio

open PlasmaLean.Theory.KAM

/-- `ω_A = |ι_A|/2 = (19 + √5)/178 = [0; 8, 2, 1, 1, …]`. -/
def dkOmegaA : ℝ := (19 + √5) / 178

/-- The (signed) rotational transform of Dommaschk torus A, `ι_A = −(19 + √5)/89`. -/
def dkIotaA : ℝ := -((19 + √5) / 89)

/-- `ι_A/2 = −ω_A`. -/
theorem dkIotaA_half : dkIotaA / 2 = -dkOmegaA := by unfold dkIotaA dkOmegaA; ring

/-- `ω_A` is a root of the primitive quadratic `89 x² − 19 x + 1` (discriminant `5`). -/
theorem dkOmegaA_root : 89 * dkOmegaA ^ 2 - 19 * dkOmegaA + 1 = 0 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold dkOmegaA
  linear_combination (89 / 178 ^ 2 : ℝ) * hs

/-- Enclosure `0.1193 < ω_A < 0.11931`. -/
theorem dkOmegaA_bounds : 1193 / 10000 < dkOmegaA ∧ dkOmegaA < 11931 / 100000 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlo : 2236 / 1000 < √5 := by nlinarith
  have hhi : √5 < 22361 / 10000 := by nlinarith
  unfold dkOmegaA
  constructor <;> linarith

/-- `|(−q) x − (−p)| = |q x − p|`: the divisor bound for `−q` follows from the one for `q`. -/
theorem abs_neg_pair (x : ℝ) (q p : ℤ) :
    |((-q : ℤ) : ℝ) * x - ((-p : ℤ) : ℝ)| = |(q : ℝ) * x - p| := by
  push_cast
  rw [show -(q : ℝ) * x - -(p : ℝ) = -((q : ℝ) * x - p) by ring, abs_neg]

/-- **Split small-divisor hypothesis for `ω_A`:** `|ω_A − m| ≥ 0.1193` for `|k| = 1`, and
`|kω_A − m| ≥ 0.3645/|k|` for `|k| ≥ 2`. -/
theorem dkOmegaA_split : DiophantineSplit dkOmegaA (1193 / 10000) (3645 / 10000) 1 1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hhi : √5 < 22361 / 10000 := by nlinarith
  have hlo : 2236 / 1000 < √5 := by nlinarith
  obtain ⟨hωlo, hωhi⟩ := dkOmegaA_bounds
  refine ⟨fun k m hk hk1 => ?_, ?_⟩
  · -- the low mode `k = ±1`
    have key : ∀ m' : ℤ, 1193 / 10000 ≤ |(1 : ℝ) * dkOmegaA - m'| := by
      intro m'
      rcases le_or_gt m' 0 with hm | hm
      · have hm' : (m' : ℝ) ≤ 0 := by exact_mod_cast hm
        rw [le_abs]; left; linarith
      · have hm' : (1 : ℝ) ≤ m' := by exact_mod_cast hm
        rw [le_abs]; right; linarith
    have hk1' : |k| ≤ 1 := by exact_mod_cast hk1
    rw [abs_le] at hk1'
    rcases (by omega : k = 1 ∨ k = -1) with rfl | rfl
    · simpa using key m
    · have := key (-m)
      push_cast at this ⊢
      rw [show -1 * dkOmegaA - m = -(1 * dkOmegaA - -m) by ring, abs_neg]
      exact this
  · -- the high modes, by the conjugate norm bound
    unfold dkOmegaA at hωlo hωhi ⊢
    refine diophantineAbove_one_of_conj (x' := (19 - √5) / 178) (A := 89) (Q := 9)
      (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro p q hq
      have := one_le_mul_conj (a := 19) (b := 178) (g := 356) (by norm_num) (by norm_num)
        (fun p q => ⟨89 * p ^ 2 - 19 * p * q + q ^ 2, by ring⟩) (p := p) hq
      norm_num at this ⊢
      exact this
    · have : (19 + √5) / 178 - (19 - √5) / 178 = √5 / 89 := by ring
      rw [this, abs_of_nonneg (by positivity)]
      norm_num
      nlinarith
    · intro q p hq1 hq9
      push_cast at hq1 hq9
      -- for `2 ≤ q ≤ 8`, `q ω_A ∈ (0, 1)`, so `p ≤ 0` or `p ≥ 1` decides the sign
      have key : ∀ q' : ℤ, 2 ≤ q' → q' ≤ 8 → ∀ p' : ℤ,
          3645 / 10000 / |(q' : ℝ)| ≤ |(q' : ℝ) * ((19 + √5) / 178) - p'| := by
        intro q' h2 h8 p'
        rcases le_or_gt p' 0 with hp | hp
        · have hp' : (p' : ℝ) ≤ 0 := by exact_mod_cast hp
          interval_cases q' <;> norm_num <;> rw [le_abs] <;> left <;> linarith
        · have hp' : (1 : ℝ) ≤ p' := by exact_mod_cast hp
          interval_cases q' <;> norm_num <;> rw [le_abs] <;> right <;> linarith
      rcases le_or_gt 0 q with hq0 | hq0
      · exact key q (by rw [abs_of_nonneg hq0] at hq1; omega)
          (by rw [abs_of_nonneg hq0] at hq9; omega) p
      · have := key (-q) (by rw [abs_of_neg hq0] at hq1; omega)
          (by rw [abs_of_neg hq0] at hq9; omega) (-p)
        rwa [abs_neg_pair, show ((-q : ℤ) : ℝ) = -(q : ℝ) by push_cast; ring, abs_neg] at this

/-- **The KAM-step form:** the signed frequency `ι_A/2` satisfies the same split hypothesis. -/
theorem dkIotaA_period_split :
    DiophantineSplit (dkIotaA / 2) (1193 / 10000) (3645 / 10000) 1 1 := by
  rw [dkIotaA_half]; exact dkOmegaA_split.neg

/-- The global Diophantine constant of `ω_A`: `(0.1193, 1)` (attained at `k = 1`). -/
theorem dkOmegaA_diophantine : Diophantine dkOmegaA (1193 / 10000) 1 := by
  have := dkOmegaA_split.toDiophantine (by norm_num) (by norm_num)
  rwa [min_eq_left (by norm_num)] at this

/-- The global Diophantine constant of the signed frequency `ι_A/2`. -/
theorem dkIotaA_period_diophantine : Diophantine (dkIotaA / 2) (1193 / 10000) 1 := by
  rw [dkIotaA_half]; exact dkOmegaA_diophantine.neg

/-- The loss threshold `e γ₂ δ ≤ 0.1193` holds for `δ ≤ 3/25`. -/
theorem dk_low_threshold {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 3 / 25) :
    Real.exp 1 * (3645 / 10000) * δ ≤ 1193 / 10000 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  nlinarith

/-- **Cohomological estimate for Dommaschk torus A with the exact low divisor:** for
`0 < δ ≤ 3/25`, `‖cohSol (ι_A/2) f‖_{r−δ} ≤ ‖f‖_r/(e · 0.3645 · δ)`. -/
theorem dkIotaA_cohSol_estimate {δ r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 3 / 25) {f : ℤ × ℤ → ℂ}
    (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol (dkIotaA / 2) f) ∧
      wnorm (r - δ) (cohSol (dkIotaA / 2) f) ≤
        wnorm r f / (Real.exp 1 * (3645 / 10000) * δ) :=
  cohSol_estimate_split_one_of_one_le dkIotaA_period_split le_rfl (by norm_num) (by norm_num) hδ
    (dk_low_threshold hδ hδ1) hf

/-- **Strip-algebra form for torus A** (drop-in for `Bd.coh` with `γ = 0.3645`). -/
theorem dkIotaA_Bd_coh {ρ δ B : ℝ} {x : FA} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 3 / 25)
    (hx : Bd ρ x B) :
    Bd (ρ - δ) (PlasmaLean.Theory.KAM.coh (dkIotaA / 2) x)
      (B / (Real.exp 1 * (3645 / 10000) * δ)) :=
  Bd.coh_split dkIotaA_period_split le_rfl (by norm_num) (by norm_num) hδ hδρ
    (dk_low_threshold hδ hδ1) hx

/-- **The gain:** the split Rüssmann factor is `1193/3645 ≈ 0.327` times the factor
`1/(e · 0.1193 · δ)` of `cohSol_estimate_one` with the global constant. -/
theorem dk_russmann_gain (δ : ℝ) :
    1 / (Real.exp 1 * (3645 / 10000) * δ) =
      (1193 / 3645) * (1 / (Real.exp 1 * (1193 / 10000) * δ)) := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp
  · have := Real.exp_pos 1
    field_simp

/-- Sanity (rejected fixture): the low constant `0.1194` fails (`k = 1`, `m = 0`). -/
theorem dkOmegaA_not_split_low (γ : ℝ) : ¬ DiophantineSplit dkOmegaA (1194 / 10000) γ 1 1 := by
  intro h
  have := h.low 1 0 one_ne_zero le_rfl
  obtain ⟨hlo, hhi⟩ := dkOmegaA_bounds
  norm_num at this
  rw [abs_of_pos (by linarith)] at this
  linarith

/-- Sanity (rejected fixture): the high constant `0.3646` fails (`k = 8`, `m = 1`:
`|8ω_A − 1| ≈ 0.04557 < 0.3646/8`). -/
theorem dkOmegaA_not_split_high (d : ℝ) : ¬ DiophantineSplit dkOmegaA d (3646 / 10000) 1 1 := by
  intro h
  have := h.high 8 1 (by norm_num)
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlo : 223606 / 100000 < √5 := by nlinarith
  have hhi : √5 < 3 := by nlinarith
  unfold dkOmegaA at this
  norm_num at this
  rw [abs_of_neg (by linarith)] at this
  linarith

end PlasmaLean.Design.DommaschkKamDio
