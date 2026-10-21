/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusCommon

/-!
# A sharper node step for the `μ > 0` certificate (`vstep2`)

The node step `vstep` (`Design/RationalStellaratorGCTorusCommon`) bounds `‖V₀⁻² − 1‖` by
`b² ‖V₀² − 1‖` with `b ≥ ‖V₀⁻¹‖`. For a node whose value is far from `1` (the node
`(1 − λ|B|)^{−1/2}` of the `μ > 0` passing field, `‖V₀ − 1‖ ≈ 0.3` on the strip) this exceeds `1`.
Here `V₀⁻² − 1 = E − V₀⁻² (V₀²(1 + E) − 1)`, so `‖V₀⁻² − 1‖ ≤ ‖E‖ + b² η` with the tiny Newton
defect `η = ‖V₀²(1 + E) − 1‖`; no bound on `‖V₀² − 1‖` is needed.

**Sanity.** `vstep2_exact`: an exact square root (`η = 0`) has radius `0`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM WEll1Z2

/-- **The sharper node step.** From `‖V₀ − 1‖ ≤ a`, `‖V₀²(1 + E) − 1‖ ≤ η`, `‖E‖ ≤ e` and rational
choices `b ≥ 1/(1 − a)`, `m ≥ e + b² η`, `g ≥ (1 − m)^{−1/2}` with `g³/2 · m + a < 2`:
`‖(1 + E)^{−1/2} − V₀‖ ≤ ½ g³ b² η ≤ ε`. -/
theorem vstep2 {r : ℝ} (hr : 0 ≤ r) {E V0 : FA} {a η b m g ε e : ℝ}
    (h1 : Bd r (V0 - 1) a) (h3 : Bd r (V0 ^ 2 * (1 + E) - 1) η) (hE : Bd r E e) (ha : a < 1)
    (hb : 1 / (1 - a) ≤ b) (hm1 : e + b ^ 2 * η ≤ m) (hm : m < 1) (hg0 : 0 ≤ g)
    (hg : 1 ≤ g ^ 2 * (1 - m)) (hsmall : g ^ 3 / 2 * m + a < 2)
    (heps : g ^ 3 / 2 * (b ^ 2 * η) ≤ ε) :
    Bd r (invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + E) - V0) ε := by
  have h1' : Bd r (V0 - algebraMap ℂ FA 1) a := by rwa [map_one]
  obtain ⟨hu, hVi⟩ := Bd.inverse hr h1' (by rw [norm_one]; exact ha)
  rw [norm_one] at hVi
  have hinv : V0 * Ring.inverse V0 = 1 := Ring.mul_inverse_cancel _ hu
  have hb' : Bd r (Ring.inverse V0) b := hVi.le hb
  have hη0 : 0 ≤ η := h3.nonneg
  have hVi2 : Bd r (Ring.inverse V0 ^ 2 - 1) m := by
    have e1 : Ring.inverse V0 ^ 2 - 1 = E - Ring.inverse V0 ^ 2 * (V0 ^ 2 * (1 + E) - 1) := by
      linear_combination (Ring.inverse V0 * V0 + 1) * (1 + E) * hinv
    rw [e1]
    exact (hE.sub ((hb'.pow hr 2).mul hr h3)).le (by linarith)
  have hm0 : 0 ≤ m := (hE.nonneg.trans (le_add_of_nonneg_right (by positivity))).trans hm1
  have hx : Bd r (algebraMap ℂ FA ((1 : ℝ) : ℂ) + E - 1) m := by
    rw [Complex.ofReal_one, map_one, add_sub_cancel_left]
    exact hE.le ((le_add_of_nonneg_right (by positivity)).trans hm1)
  have hg' : isqG 1 m ≤ g := isqG_le hm hg0 hg
  have hgn : 0 ≤ isqG 1 m := isqG_nonneg 1 m
  have hsm : isqG 1 m ^ 3 / 2 * m + a < 2 := by
    have : isqG 1 m ^ 3 ≤ g ^ 3 := pow_le_pow_left₀ hgn hg' 3
    nlinarith
  have hη : Bd r (V0 ^ 2 * (algebraMap ℂ FA ((1 : ℝ) : ℂ) + E) - 1) η := by
    rw [Complex.ofReal_one, map_one]; exact h3
  have h := invSqrt_approx_bound hr hinv hx hVi2 hm h1 hsm hb' hη
  refine h.le (le_trans ?_ heps)
  have : isqG 1 m ^ 3 ≤ g ^ 3 := pow_le_pow_left₀ hgn hg' 3
  have hb2 : 0 ≤ b ^ 2 * η := by positivity
  nlinarith

/-- **Sanity**: an exact inverse square root has radius `0` (`V₀ = 1`, `E = 0`). -/
theorem vstep2_exact {r : ℝ} (hr : 0 ≤ r) :
    Bd r (invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + 0) - 1) 0 := by
  have h := vstep2 (r := r) (E := 0) (V0 := 1) (a := 0) (η := 0) (b := 1) (m := 0) (g := 1)
    (ε := 0) (e := 0) hr (by rw [sub_self]; exact Bd_zero r)
    (by rw [one_pow, add_zero, mul_one, sub_self]; exact Bd_zero r) (Bd_zero r) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact h

end PlasmaLean.Design.RationalStellaratorGC
