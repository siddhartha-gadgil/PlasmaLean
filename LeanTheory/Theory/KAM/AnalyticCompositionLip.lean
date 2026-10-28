/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.AnalyticComposition

/-!
# Strip-norm Lipschitz bounds for analytic composition

KAM for non-polynomial (analytic) fields: the `Bd ρ` forms of
the Banach-algebra Lipschitz bounds `norm_comp_sub_le`, `norm_d1_sub_le`, `norm_d2_sub_le` of
`Theory/KAM/AnalyticComposition`. The proofs lift all data to `ℓ¹_ρ(ℤ²)` through `toFA`
(as in `bd_comp_taylor`).

With `Bd ρ hᵢ bᵢ`, `Bd ρ kᵢ tᵢ`, `bᵢ + tᵢ ≤ s < d` and Cauchy majorants
`Bd ρ c_α (C/d^{|α|})`:
* `bd_comp_sub`: `Bd ρ (X(K₀+h+k) − X(K₀+h)) (C/(d(1 − s/d)³) · (t₁ + t₂))`;
* `bd_d1_sub`, `bd_d2_sub`: `Bd ρ (∂ᵢX(K₀+h+k) − ∂ᵢX(K₀+h)) (2C/(d²(1 − s/d)⁴) · (t₁ + t₂))`.

**Sanity.** `bd_comp_sub_zero`: for `k = 0` the bound degenerates to `Bd ρ 0 0`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM.AnalyticComposition

open WEll1Z2

variable {ρ : ℝ} {c : ℕ × ℕ → FA} {C d s : ℝ}

/-- Nonnegativity of the Lipschitz prefactor `K/(dⁿ(1 − s/d)^m)` for `K ≥ 0`, `0 < d`, `s < d`. -/
theorem lip_factor_nonneg (hd : 0 < d) (hsd : s < d) {K : ℝ} (hK : 0 ≤ K) (n m : ℕ) :
    0 ≤ K / (d ^ n * (1 - s / d) ^ m) := by
  have := (show 0 < 1 - s / d by rw [sub_pos, div_lt_one hd]; exact hsd)
  positivity

section BdLip

variable (hρ : 0 ≤ ρ) (hd : 0 < d) (hc : ∀ α : ℕ × ℕ, Bd ρ (c α) (C / d ^ (α.1 + α.2)))
  (hs0 : 0 ≤ s) (hsd : s < d)
include hρ hd hc hs0 hsd

/-- **Strip Lipschitz bound for the composition**: with `Bd ρ hᵢ bᵢ`, `Bd ρ kᵢ tᵢ`,
`bᵢ + tᵢ ≤ s < d`, `Bd ρ (X(K₀ + h + k) − X(K₀ + h)) (C/(d(1 − s/d)³) · (t₁ + t₂))`. -/
theorem bd_comp_sub {h₁ h₂ k₁ k₂ : FA} {b₁ b₂ t₁ t₂ : ℝ} (h1 : Bd ρ h₁ b₁) (h2 : Bd ρ h₂ b₂)
    (k1 : Bd ρ k₁ t₁) (k2 : Bd ρ k₂ t₂) (hb₁ : b₁ + t₁ ≤ s) (hb₂ : b₂ + t₂ ≤ s) :
    Bd ρ (comp c (h₁ + k₁, h₂ + k₂) - comp c (h₁, h₂))
      (C / (d * (1 - s / d) ^ 3) * (t₁ + t₂)) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨m₁, rfl, o₁⟩ := exists_lift hρ k1
  obtain ⟨m₂, rfl, o₂⟩ := exists_lift hρ k2
  have q1 : ‖(l₁, l₂).1‖ + ‖(m₁, m₂).1‖ ≤ s := by simp only; linarith
  have q2 : ‖(l₁, l₂).2‖ + ‖(m₁, m₂).2‖ ≤ s := by simp only; linarith
  have hZ1 : ‖l₁‖ ≤ s := by linarith [norm_nonneg m₁]
  have hZ2 : ‖l₂‖ ≤ s := by linarith [norm_nonneg m₂]
  have hW1 : ‖l₁ + m₁‖ ≤ s := (norm_add_le _ _).trans q1
  have hW2 : ‖l₂ + m₂‖ ≤ s := (norm_add_le _ _).trans q2
  obtain ⟨sW, -⟩ := comp_summable_and_le (h := (l₁ + m₁, l₂ + m₂)) hd hcl hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := comp_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd hZ1 hZ2
  have e : comp (fun α => toFA hρ (cl α)) (toFA hρ l₁ + toFA hρ m₁, toFA hρ l₂ + toFA hρ m₂) -
      comp (fun α => toFA hρ (cl α)) (toFA hρ l₁, toFA hρ l₂) =
      toFA hρ (comp cl ((l₁, l₂) + (m₁, m₂)) - comp cl (l₁, l₂)) := by
    rw [map_sub, toFA_comp hρ cl _ sZ, Prod.mk_add_mk, toFA_comp hρ cl _ sW, map_add, map_add]
  rw [e]
  refine (Bd_toFA hρ _).le ((norm_comp_sub_le hd hcl hs0 hsd q1 q2).trans ?_)
  have hK : 0 ≤ C / (d * (1 - s / d) ^ 3) := by
    have := lip_factor_nonneg hd hsd hcl.C_nonneg 1 3
    simpa using this
  refine mul_le_mul_of_nonneg_left ?_ hK
  simp only; linarith

/-- **Strip Lipschitz bound for `∂₁X`**: under the hypotheses of `bd_comp_sub`,
`Bd ρ (∂₁X(K₀ + h + k) − ∂₁X(K₀ + h)) (2C/(d²(1 − s/d)⁴) · (t₁ + t₂))`. -/
theorem bd_d1_sub {h₁ h₂ k₁ k₂ : FA} {b₁ b₂ t₁ t₂ : ℝ} (h1 : Bd ρ h₁ b₁) (h2 : Bd ρ h₂ b₂)
    (k1 : Bd ρ k₁ t₁) (k2 : Bd ρ k₂ t₂) (hb₁ : b₁ + t₁ ≤ s) (hb₂ : b₂ + t₂ ≤ s) :
    Bd ρ (d1 c (h₁ + k₁, h₂ + k₂) - d1 c (h₁, h₂))
      (2 * C / (d ^ 2 * (1 - s / d) ^ 4) * (t₁ + t₂)) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨m₁, rfl, o₁⟩ := exists_lift hρ k1
  obtain ⟨m₂, rfl, o₂⟩ := exists_lift hρ k2
  have q1 : ‖(l₁, l₂).1‖ + ‖(m₁, m₂).1‖ ≤ s := by simp only; linarith
  have q2 : ‖(l₁, l₂).2‖ + ‖(m₁, m₂).2‖ ≤ s := by simp only; linarith
  have hZ1 : ‖l₁‖ ≤ s := by linarith [norm_nonneg m₁]
  have hZ2 : ‖l₂‖ ≤ s := by linarith [norm_nonneg m₂]
  have hW1 : ‖l₁ + m₁‖ ≤ s := (norm_add_le _ _).trans q1
  have hW2 : ‖l₂ + m₂‖ ≤ s := (norm_add_le _ _).trans q2
  obtain ⟨sW, -⟩ := d1_summable_and_le (h := (l₁ + m₁, l₂ + m₂)) hd hcl hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := d1_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd hZ1 hZ2
  have e : d1 (fun α => toFA hρ (cl α)) (toFA hρ l₁ + toFA hρ m₁, toFA hρ l₂ + toFA hρ m₂) -
      d1 (fun α => toFA hρ (cl α)) (toFA hρ l₁, toFA hρ l₂) =
      toFA hρ (d1 cl ((l₁, l₂) + (m₁, m₂)) - d1 cl (l₁, l₂)) := by
    rw [map_sub, toFA_d1 hρ cl _ sZ, Prod.mk_add_mk, toFA_d1 hρ cl _ sW, map_add, map_add]
  rw [e]
  refine (Bd_toFA hρ _).le ((norm_d1_sub_le hd hcl hs0 hsd q1 q2).trans ?_)
  have hK := lip_factor_nonneg hd hsd (mul_nonneg zero_le_two hcl.C_nonneg) 2 4
  refine mul_le_mul_of_nonneg_left ?_ hK
  simp only; linarith

/-- **Strip Lipschitz bound for `∂₂X`**: under the hypotheses of `bd_comp_sub`,
`Bd ρ (∂₂X(K₀ + h + k) − ∂₂X(K₀ + h)) (2C/(d²(1 − s/d)⁴) · (t₁ + t₂))`. -/
theorem bd_d2_sub {h₁ h₂ k₁ k₂ : FA} {b₁ b₂ t₁ t₂ : ℝ} (h1 : Bd ρ h₁ b₁) (h2 : Bd ρ h₂ b₂)
    (k1 : Bd ρ k₁ t₁) (k2 : Bd ρ k₂ t₂) (hb₁ : b₁ + t₁ ≤ s) (hb₂ : b₂ + t₂ ≤ s) :
    Bd ρ (d2 c (h₁ + k₁, h₂ + k₂) - d2 c (h₁, h₂))
      (2 * C / (d ^ 2 * (1 - s / d) ^ 4) * (t₁ + t₂)) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨m₁, rfl, o₁⟩ := exists_lift hρ k1
  obtain ⟨m₂, rfl, o₂⟩ := exists_lift hρ k2
  have q1 : ‖(l₁, l₂).1‖ + ‖(m₁, m₂).1‖ ≤ s := by simp only; linarith
  have q2 : ‖(l₁, l₂).2‖ + ‖(m₁, m₂).2‖ ≤ s := by simp only; linarith
  have hZ1 : ‖l₁‖ ≤ s := by linarith [norm_nonneg m₁]
  have hZ2 : ‖l₂‖ ≤ s := by linarith [norm_nonneg m₂]
  have hW1 : ‖l₁ + m₁‖ ≤ s := (norm_add_le _ _).trans q1
  have hW2 : ‖l₂ + m₂‖ ≤ s := (norm_add_le _ _).trans q2
  obtain ⟨sW, -⟩ := d2_summable_and_le (h := (l₁ + m₁, l₂ + m₂)) hd hcl hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := d2_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd hZ1 hZ2
  have e : d2 (fun α => toFA hρ (cl α)) (toFA hρ l₁ + toFA hρ m₁, toFA hρ l₂ + toFA hρ m₂) -
      d2 (fun α => toFA hρ (cl α)) (toFA hρ l₁, toFA hρ l₂) =
      toFA hρ (d2 cl ((l₁, l₂) + (m₁, m₂)) - d2 cl (l₁, l₂)) := by
    rw [map_sub, toFA_d2 hρ cl _ sZ, Prod.mk_add_mk, toFA_d2 hρ cl _ sW, map_add, map_add]
  rw [e]
  refine (Bd_toFA hρ _).le ((norm_d2_sub_le hd hcl hs0 hsd q1 q2).trans ?_)
  have hK := lip_factor_nonneg hd hsd (mul_nonneg zero_le_two hcl.C_nonneg) 2 4
  refine mul_le_mul_of_nonneg_left ?_ hK
  simp only; linarith

/-- Sanity (degenerate case): with `k = 0` the Lipschitz bound gives `Bd ρ 0 0`. -/
theorem bd_comp_sub_zero {h₁ h₂ : FA} {b : ℝ} (h1 : Bd ρ h₁ b) (h2 : Bd ρ h₂ b) (hb : b ≤ s) :
    Bd ρ (comp c (h₁ + 0, h₂ + 0) - comp c (h₁, h₂)) 0 := by
  have h := bd_comp_sub hρ hd hc hs0 hsd h1 h2 (Bd_zero ρ) (Bd_zero ρ) (by linarith)
    (by linarith)
  simpa using h

end BdLip

end LeanTheory.Theory.KAM.AnalyticComposition
