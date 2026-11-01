/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamDio
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Small divisors of the Dommaschk torus C

The torus-C analogue of `Design/DommaschkKamDio` (N-33 plan, certification torus C; oracle
`notes/theory/dommaschk-qa.md` §§25–27). Torus C of the Dommaschk target has the noble rotational
transform `ι_C = −(85 + √5)/361 ≈ −0.2416512`. In the field-period angle `ψ = 2φ` the flow
`∂_φ + ι ∂_θ = 2 (∂_ψ + (ι/2) ∂_θ)` has frequency `ι_C/2 = −ω_C` with

`ω_C = |ι_C|/2 = (85 + √5)/722 = [0; 8, 3, 1, 1, 1, …] ≈ 0.1208256`,

a root of the primitive quadratic `361 x² − 85 x + 5` (discriminant `5`; `dkOmegaC_root`), between
the resonances `3/25` and `1/8`.

**Small divisors.** `|kω_C − m|` is smallest at `k = 1` (`ω_C` itself), while for `|k| ≥ 2`,
`|k| ‖kω_C‖ ≥ 0.26716`, attained at `k = 8` (`1 − 8ω_C = (42 − 8√5)/722`). Hence
* `dkOmegaC_split : DiophantineSplit ω_C 0.1208 0.2671 1 1` (low divisor `|ω_C − m| ≥ 0.1208`,
  high constant `γ₂ = 0.2671`), proved by the conjugate norm bound
  `361 |qω − p| |qω' − p| ≥ 1` (from `(85q − 722p)² − 5q² = 1444 (361p² − 85pq + 5q²)`),
  `361 (γ₂²/81 + γ₂ √5/361) ≈ 0.915 ≤ 1` for `|q| ≥ 9`, and a direct check of `2 ≤ |q| ≤ 8`
  (where `qω_C ∈ (0, 1)`);
* `dkIotaC_period_split`: the same for the signed frequency `ι_C/2` used by the KAM step
  (`FlowFieldG.GlobalHG.dio` with `dlow = 0.1208`, `γ = 0.2671`, `Klow = 1`);
* `dkOmegaC_diophantine : Diophantine ω_C 0.1208 1` (the global constant, `k = 1`).

**Loss threshold.** `dkC_low_threshold`: `e γ₂ δ ≤ 0.1208` for `δ ≤ 4/25` (the hypothesis
`GlobalHG.hlow : exp 1 * γ * δ₀ ≤ dlow`; every `δ₀ = r/7` with `r ≤ 1` qualifies), and the
concrete `dkC_low_δ0 : exp 1 · 0.2671 · (9/1400) ≤ 0.1208` for the recommended `δ₀ = 0.045/7`.
`dkIotaC_Bd_coh` is the strip-algebra form, a drop-in for `Bd.coh`.

**Sanity.** The rejected fixtures `dkOmegaC_not_split_low` (`d = 0.1209` fails at `k = 1`) and
`dkOmegaC_not_split_high` (`γ₂ = 0.2672` fails at `k = 8`, `m = 1`): both constants are within
`10⁻⁴` of optimal; `dkC_russmann_gain` (the split Rüssmann factor is `1208/2671 ≈ 0.452` times the
global one).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamDio

open PlasmaLean.Theory.KAM

/-- `ω_C = |ι_C|/2 = (85 + √5)/722 = [0; 8, 3, 1, 1, …]`. -/
def dkOmegaC : ℝ := (85 + √5) / 722

/-- The (signed) rotational transform of Dommaschk torus C, `ι_C = −(85 + √5)/361`. -/
def dkIotaC : ℝ := -((85 + √5) / 361)

/-- `ι_C/2 = −ω_C`. -/
theorem dkIotaC_half : dkIotaC / 2 = -dkOmegaC := by unfold dkIotaC dkOmegaC; ring

/-- `ω_C` is a root of the primitive quadratic `361 x² − 85 x + 5` (discriminant `5`). -/
theorem dkOmegaC_root : 361 * dkOmegaC ^ 2 - 85 * dkOmegaC + 5 = 0 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold dkOmegaC
  linear_combination (361 / 722 ^ 2 : ℝ) * hs

/-- Enclosure `0.1208 < ω_C < 0.120826`. -/
theorem dkOmegaC_bounds : 1208 / 10000 < dkOmegaC ∧ dkOmegaC < 120826 / 1000000 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlo : 2236 / 1000 < √5 := by nlinarith
  have hhi : √5 < 22361 / 10000 := by nlinarith
  unfold dkOmegaC
  constructor <;> linarith

/-- **Split small-divisor hypothesis for `ω_C`:** `|ω_C − m| ≥ 0.1208` for `|k| = 1`, and
`|kω_C − m| ≥ 0.2671/|k|` for `|k| ≥ 2`. -/
theorem dkOmegaC_split : DiophantineSplit dkOmegaC (1208 / 10000) (2671 / 10000) 1 1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hhi : √5 < 22361 / 10000 := by nlinarith
  have hlo : 2236 / 1000 < √5 := by nlinarith
  obtain ⟨hωlo, hωhi⟩ := dkOmegaC_bounds
  refine ⟨fun k m hk hk1 => ?_, ?_⟩
  · -- the low mode `k = ±1`
    have key : ∀ m' : ℤ, 1208 / 10000 ≤ |(1 : ℝ) * dkOmegaC - m'| := by
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
      rw [show -1 * dkOmegaC - m = -(1 * dkOmegaC - -m) by ring, abs_neg]
      exact this
  · -- the high modes, by the conjugate norm bound
    unfold dkOmegaC at hωlo hωhi ⊢
    refine diophantineAbove_one_of_conj (x' := (85 - √5) / 722) (A := 361) (Q := 9)
      (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro p q hq
      have := one_le_mul_conj (a := 85) (b := 722) (g := 1444) (by norm_num) (by norm_num)
        (fun p q => ⟨361 * p ^ 2 - 85 * p * q + 5 * q ^ 2, by ring⟩) (p := p) hq
      norm_num at this ⊢
      exact this
    · have : (85 + √5) / 722 - (85 - √5) / 722 = √5 / 361 := by ring
      rw [this, abs_of_nonneg (by positivity)]
      norm_num
      nlinarith
    · intro q p hq1 hq9
      push_cast at hq1 hq9
      -- for `2 ≤ q ≤ 8`, `q ω_C ∈ (0, 1)`, so `p ≤ 0` or `p ≥ 1` decides the sign
      have key : ∀ q' : ℤ, 2 ≤ q' → q' ≤ 8 → ∀ p' : ℤ,
          2671 / 10000 / |(q' : ℝ)| ≤ |(q' : ℝ) * ((85 + √5) / 722) - p'| := by
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

/-- **The KAM-step form:** the signed frequency `ι_C/2` satisfies the same split hypothesis. -/
theorem dkIotaC_period_split :
    DiophantineSplit (dkIotaC / 2) (1208 / 10000) (2671 / 10000) 1 1 := by
  rw [dkIotaC_half]; exact dkOmegaC_split.neg

/-- The global Diophantine constant of `ω_C`: `(0.1208, 1)` (attained at `k = 1`). -/
theorem dkOmegaC_diophantine : Diophantine dkOmegaC (1208 / 10000) 1 := by
  have := dkOmegaC_split.toDiophantine (by norm_num) (by norm_num)
  rwa [min_eq_left (by norm_num)] at this

/-- The global Diophantine constant of the signed frequency `ι_C/2`. -/
theorem dkIotaC_period_diophantine : Diophantine (dkIotaC / 2) (1208 / 10000) 1 := by
  rw [dkIotaC_half]; exact dkOmegaC_diophantine.neg

/-- The loss threshold `e γ₂ δ ≤ 0.1208` holds for `δ ≤ 4/25`. -/
theorem dkC_low_threshold {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 4 / 25) :
    Real.exp 1 * (2671 / 10000) * δ ≤ 1208 / 10000 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  nlinarith

/-- The loss threshold for the recommended initial loss `δ₀ = r/7`, `r = 0.045`
(`GlobalHG.hlow`). -/
theorem dkC_low_δ0 : Real.exp 1 * (2671 / 10000) * (9 / 1400) ≤ 1208 / 10000 :=
  dkC_low_threshold (by norm_num) (by norm_num)

/-- **Cohomological estimate for Dommaschk torus C with the exact low divisor:** for
`0 < δ ≤ 4/25`, `‖cohSol (ι_C/2) f‖_{r−δ} ≤ ‖f‖_r/(e · 0.2671 · δ)`. -/
theorem dkIotaC_cohSol_estimate {δ r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 4 / 25) {f : ℤ × ℤ → ℂ}
    (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol (dkIotaC / 2) f) ∧
      wnorm (r - δ) (cohSol (dkIotaC / 2) f) ≤
        wnorm r f / (Real.exp 1 * (2671 / 10000) * δ) :=
  cohSol_estimate_split_one_of_one_le dkIotaC_period_split le_rfl (by norm_num) (by norm_num) hδ
    (dkC_low_threshold hδ hδ1) hf

/-- **Strip-algebra form for torus C** (drop-in for `Bd.coh` with `γ = 0.2671`). -/
theorem dkIotaC_Bd_coh {ρ δ B : ℝ} {x : FA} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 4 / 25)
    (hx : Bd ρ x B) :
    Bd (ρ - δ) (PlasmaLean.Theory.KAM.coh (dkIotaC / 2) x)
      (B / (Real.exp 1 * (2671 / 10000) * δ)) :=
  Bd.coh_split dkIotaC_period_split le_rfl (by norm_num) (by norm_num) hδ hδρ
    (dkC_low_threshold hδ hδ1) hx

/-- **The gain:** the split Rüssmann factor is `1208/2671 ≈ 0.452` times the factor
`1/(e · 0.1208 · δ)` of `cohSol_estimate_one` with the global constant. -/
theorem dkC_russmann_gain (δ : ℝ) :
    1 / (Real.exp 1 * (2671 / 10000) * δ) =
      (1208 / 2671) * (1 / (Real.exp 1 * (1208 / 10000) * δ)) := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp
  · have := Real.exp_pos 1
    field_simp

/-- Sanity (rejected fixture): the low constant `0.1209` fails (`k = 1`, `m = 0`). -/
theorem dkOmegaC_not_split_low (γ : ℝ) : ¬ DiophantineSplit dkOmegaC (1209 / 10000) γ 1 1 := by
  intro h
  have := h.low 1 0 one_ne_zero le_rfl
  obtain ⟨hlo, hhi⟩ := dkOmegaC_bounds
  norm_num at this
  rw [abs_of_pos (by linarith)] at this
  linarith

/-- Sanity (rejected fixture): the high constant `0.2672` fails (`k = 8`, `m = 1`:
`|8ω_C − 1| ≈ 0.033395 < 0.2672/8 = 0.0334`). -/
theorem dkOmegaC_not_split_high (d : ℝ) : ¬ DiophantineSplit dkOmegaC d (2672 / 10000) 1 1 := by
  intro h
  have := h.high 8 1 (by norm_num)
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlo : 2236 / 1000 < √5 := by nlinarith
  have hhi : √5 < 3 := by nlinarith
  unfold dkOmegaC at this
  norm_num at this
  rw [abs_of_neg (by linarith)] at this
  linarith

end PlasmaLean.Design.DommaschkKamDio
