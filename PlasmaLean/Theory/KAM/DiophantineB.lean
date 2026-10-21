/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.Diophantine

/-!
# The rotational transform `ι_B` of the guiding-centre torus with `v∥ < 0`

The guiding-centre torus at `ρ_s = −1/256` (`notes/theory/robust-alpha-confinement.md`, §2) uses
the noble rotational transform

`ι_B = (161 − √5)/1178 = [0;7,2,2,1,1,1,…] ≈ 0.134774`,

a root of the primitive quadratic `589 x² − 161 x + 11` (discriminant `5`). This file proves the
small-divisor hypothesis of the KAM theorem for it, by the conjugate-norm argument of
`Theory/KAM/Diophantine` (`diophantine_one_of_conj`):

* `(161 q − 1178 p)² − 5 q² = 2356 (589 p² − 161 p q + 11 q²)`, so
  `589 |q ι_B − p| |q ι_B' − p| ≥ 1` for the conjugate `ι_B' = (161 + √5)/1178`;
* `589 (γ²/16 + γ |ι_B − ι_B'|) ≈ 0.97 ≤ 1` for `γ = 0.1346` and `|q| ≥ 4`;
* the denominators `|q| ∈ {1, 2, 3}` are checked directly.

**Results.**
* `iotaB_rotation_diophantine : Diophantine ((161 − √5)/1178) (673/5000) 1` (`γ = 0.1346`; the
  optimum `≈ 0.134774` is attained at `k = 1`);
* **`iotaB_period_diophantine : Diophantine (iotaB/2) (673/10000) 1`**, the field-period form used
  by `FlowFieldS.GlobalH.dio` (the flow `∂_φ + ι ∂_θ = 2(∂_ψ + (ι/2) ∂_θ)`).

**Sanity.** `iotaB_root` (the quadratic), `iotaB_bounds`, and the rejected fixture
`iotaB_not_diophantine_large` (`γ = 0.1348` fails at `k = 1`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

/-- The rotational transform of the `v∥ < 0` guiding-centre torus,
`ι_B = (161 − √5)/1178 = [0;7,2,2,1,1,…]`. It is a root of `589 x² − 161 x + 11`. -/
def iotaB : ℝ := (161 - √5) / 1178

/-- Enclosure `0.13477 < ι_B < 0.13478`. -/
theorem iotaB_bounds : 13477 / 100000 < iotaB ∧ iotaB < 13478 / 100000 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlo : 22360 / 10000 < √5 := by nlinarith
  have hhi : √5 < 22361 / 10000 := by nlinarith
  unfold iotaB
  constructor <;> linarith

/-- `ι_B` is a root of the primitive quadratic `589 x² − 161 x + 11` (discriminant `5`). -/
theorem iotaB_root : 589 * iotaB ^ 2 - 161 * iotaB + 11 = 0 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold iotaB
  linear_combination (589 / 1178 ^ 2 : ℝ) * hs

/-- **`ι_B` is Diophantine:** `|k ι_B − m| ≥ 0.1346/|k|` for all `k ≠ 0`. Proof: the conjugate
norm bound `589 |q ι_B − p| |q ι_B' − p| ≥ 1` (from
`(161q − 1178p)² − 5q² = 2356 (589p² − 161pq + 11q²)`), `589 (γ²/16 + γ √5/589) ≤ 1` for
`|q| ≥ 4`, and a direct check of `|q| ∈ {1, 2, 3}`. -/
theorem iotaB_rotation_diophantine : Diophantine ((161 - √5) / 1178) (673 / 5000) 1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hhi : √5 < 22361 / 10000 := by nlinarith
  obtain ⟨hιlo, hιhi⟩ := iotaB_bounds
  unfold iotaB at hιlo hιhi
  refine diophantine_one_of_conj (x' := (161 + √5) / 1178) (A := 589) (Q := 4)
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · intro p q hq
    have := one_le_mul_conj (a := 161) (b := 1178) (g := 2356) (by norm_num) (by norm_num)
      (fun p q => ⟨589 * p ^ 2 - 161 * p * q + 11 * q ^ 2, by ring⟩) (p := p) hq
    norm_num at this ⊢
    rw [mul_comm |(q : ℝ) * ((161 + √5) / 1178) - p|] at this
    exact this
  · have : (161 - √5) / 1178 - (161 + √5) / 1178 = -(√5 / 589) := by ring
    rw [this, abs_neg, abs_of_nonneg (by positivity)]
    norm_num
    nlinarith
  · intro q p hq hq4
    push_cast at hq4
    rw [abs_lt] at hq4
    -- reduce to `q ∈ {1, 2, 3}` using `|(-q) x - (-p)| = |q x - p|`
    have key : ∀ q' : ℤ, (q' = 1 ∨ q' = 2 ∨ q' = 3) → ∀ p' : ℤ,
        673 / 5000 / |(q' : ℝ)| ≤ |(q' : ℝ) * ((161 - √5) / 1178) - p'| := by
      intro q' hq' p'
      rcases le_or_gt p' 0 with hp | hp
      · have hp' : (p' : ℝ) ≤ 0 := by exact_mod_cast hp
        rcases hq' with rfl | rfl | rfl <;> norm_num <;> rw [le_abs] <;> left <;> linarith
      · have hp' : (1 : ℝ) ≤ p' := by exact_mod_cast hp
        rcases hq' with rfl | rfl | rfl <;> norm_num <;> rw [le_abs] <;> right <;> linarith
    have hneg : ∀ q' : ℤ, (q' = 1 ∨ q' = 2 ∨ q' = 3) → q = -q' →
        673 / 5000 / |(q : ℝ)| ≤ |(q : ℝ) * ((161 - √5) / 1178) - p| := by
      intro q' hq' hqq
      have := key q' hq' (-p)
      subst hqq
      push_cast at this ⊢
      rwa [abs_neg, show -(q' : ℝ) * ((161 - √5) / 1178) - p =
        -((q' : ℝ) * ((161 - √5) / 1178) - -(p : ℝ)) by ring, abs_neg]
    rcases (by omega : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = -1 ∨ q = -2 ∨ q = -3) with
      h | h | h | h | h | h
    · exact key q (Or.inl h) p
    · exact key q (Or.inr (Or.inl h)) p
    · exact key q (Or.inr (Or.inr h)) p
    · exact hneg 1 (Or.inl rfl) h
    · exact hneg 2 (Or.inr (Or.inl rfl)) h
    · exact hneg 3 (Or.inr (Or.inr rfl)) h

/-- **Field-period form** (module M1 of the robust-confinement plan): the frequency
`ω = ι_B/2` of `∂_ψ + ω ∂_θ` is `(0.0673, 1)`-Diophantine (optimum `≈ 0.067387`). -/
theorem iotaB_period_diophantine : Diophantine (iotaB / 2) (673 / 10000) 1 := by
  intro k m hk
  have := iotaB_rotation_diophantine k (2 * m) hk
  unfold iotaB
  push_cast at this
  rw [pow_one] at this ⊢
  have e : (k : ℝ) * ((161 - √5) / 1178 / 2) - m =
      ((k : ℝ) * ((161 - √5) / 1178) - 2 * m) / 2 := by ring
  rw [e, abs_div, abs_two]
  have e2 : (673 / 10000 : ℝ) / |(k : ℝ)| = 673 / 5000 / |(k : ℝ)| / 2 := by ring
  rw [e2]
  linarith

/-- Sanity (rejected fixture): `ι_B` is not `(0.1348, 1)`-Diophantine (`k = 1`, `m = 0`), so
`γ = 0.1346` is within `2 × 10⁻⁴` of optimal. -/
theorem iotaB_not_diophantine_large : ¬ Diophantine ((161 - √5) / 1178) (1348 / 10000) 1 := by
  intro h
  have := h 1 0 one_ne_zero
  obtain ⟨hlo, hhi⟩ := iotaB_bounds
  unfold iotaB at hlo hhi
  norm_num at this
  rw [abs_of_pos (by linarith)] at this
  linarith

end PlasmaLean.Theory.KAM
