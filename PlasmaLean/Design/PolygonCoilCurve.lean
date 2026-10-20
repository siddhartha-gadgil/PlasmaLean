/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSegment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Closed polygonal filaments as `C¹` closed curves

The vacuum-field theorem for filaments (`Coils.filaments_vacuumField`) needs closed `C¹` curves.
A closed polygon with vertices `V 0, …, V (N - 1)` (`V N = V 0`) is traversed by the `C¹` curve

`polyC N V t = V 0 + Σₖ ψ(N t - k) (V (k+1) - V k)`,

where `ψ` is a `C¹` smoothstep (`ψ = 0` on `(-∞, 0]`, `ψ = 1` on `[1, ∞)`,
`ψ' = 6 max(0, τ(1 - τ))`): on `[k/N, (k+1)/N]` it runs along the segment `V k → V (k+1)` with
zero speed at the corners.

* `hasDerivAt_polyC`, `continuous_polyCD`: `polyC` is `C¹` with derivative `polyCD`.
* `polyC_zero`, `polyC_one`: it is closed.
* `polyC_on_piece`: on the `k`-th piece it is `seg (V k) (V (k+1)) (ψ(N t - k))`.
* `filamentField_polyC` (**the filament field of the polygon is the sum of its segment
  fields**) at every point off the polygon, by splitting the integral and substituting
  `s = ψ(N t - k)` on each piece.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator.CoilsTF Set Finset

/-! ## The smoothstep -/

/-- The derivative profile `6 max(0, τ(1 - τ))` of the smoothstep. -/
@[expose] def psiD (τ : ℝ) : ℝ := 6 * max 0 (τ * (1 - τ))

/-- The `C¹` smoothstep `ψ(τ) = ∫₀^τ ψ'`. -/
@[expose] def psi (τ : ℝ) : ℝ := ∫ s in (0 : ℝ)..τ, psiD s

/-- `ψ'` is continuous. -/
theorem continuous_psiD : Continuous psiD := by
  unfold psiD; fun_prop

/-- `ψ' ≥ 0`. -/
theorem psiD_nonneg (τ : ℝ) : 0 ≤ psiD τ := by
  unfold psiD; positivity

/-- `ψ'` vanishes off `(0, 1)`. -/
theorem psiD_eq_zero {τ : ℝ} (h : τ ≤ 0 ∨ 1 ≤ τ) : psiD τ = 0 := by
  unfold psiD
  have : τ * (1 - τ) ≤ 0 := by
    rcases h with h | h
    · nlinarith
    · nlinarith
  simp [max_eq_left this]

/-- `ψ' = 6τ(1 - τ)` on `[0, 1]`. -/
theorem psiD_eq {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : psiD τ = 6 * (τ * (1 - τ)) := by
  unfold psiD
  rw [max_eq_right (by nlinarith)]

/-- `ψ` has derivative `ψ'`. -/
theorem hasDerivAt_psi (τ : ℝ) : HasDerivAt psi (psiD τ) τ :=
  intervalIntegral.integral_hasDerivAt_right (continuous_psiD.intervalIntegrable _ _)
    (continuous_psiD.stronglyMeasurableAtFilter _ _) continuous_psiD.continuousAt

/-- `ψ = 0` on `(-∞, 0]`. -/
theorem psi_of_nonpos {τ : ℝ} (h : τ ≤ 0) : psi τ = 0 := by
  unfold psi
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => ?_)]
  · simp
  · rw [uIcc_of_ge h] at hs
    exact psiD_eq_zero (Or.inl hs.2)

/-- `ψ(1) = 1`. -/
theorem psi_one : psi 1 = 1 := by
  unfold psi
  rw [intervalIntegral.integral_congr (g := fun s => 6 * (s * (1 - s))) (fun s hs => ?_)]
  · have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3)
        (6 * (x * (1 - x))) x := by
      intro x _
      have := (((hasDerivAt_id' x).pow 2).const_mul 3).sub (((hasDerivAt_id' x).pow 3).const_mul 2)
      convert this using 1; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous fun s : ℝ => 6 * (s * (1 - s))).intervalIntegrable _ _)]
    norm_num
  · rw [Set.uIcc_of_le zero_le_one] at hs
    exact psiD_eq hs.1 hs.2

/-- `ψ = 1` on `[1, ∞)`. -/
theorem psi_of_one_le {τ : ℝ} (h : 1 ≤ τ) : psi τ = 1 := by
  have : psi τ = psi 1 + ∫ s in (1 : ℝ)..τ, psiD s := by
    unfold psi
    rw [intervalIntegral.integral_add_adjacent_intervals (continuous_psiD.intervalIntegrable _ _)
      (continuous_psiD.intervalIntegrable _ _)]
  rw [this, psi_one, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => ?_)]
  · simp
  · rw [uIcc_of_le h] at hs
    exact psiD_eq_zero (Or.inr hs.1)

/-- `ψ` is monotone. -/
theorem psi_mono : Monotone psi :=
  monotone_of_deriv_nonneg (fun x => (hasDerivAt_psi x).differentiableAt)
    (fun x => by rw [(hasDerivAt_psi x).deriv]; exact psiD_nonneg x)

/-- `0 ≤ ψ ≤ 1`. -/
theorem psi_mem (τ : ℝ) : psi τ ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rcases le_total τ 0 with h | h
    · rw [psi_of_nonpos h]
    · rw [← psi_of_nonpos le_rfl]; exact psi_mono h
  · rcases le_total τ 1 with h | h
    · rw [← psi_one]; exact psi_mono h
    · rw [psi_of_one_le h]

/-! ## The polygon curve -/

/-- The `C¹` closed curve traversing the polygon `V 0 → V 1 → ⋯ → V N` (`V N = V 0`). -/
@[expose] def polyC (N : ℕ) (V : ℕ → Space) (t : ℝ) : Space :=
  V 0 + ∑ k ∈ range N, psi (N * t - k) • (V (k + 1) - V k)

/-- Its velocity. -/
@[expose] def polyCD (N : ℕ) (V : ℕ → Space) (t : ℝ) : Space :=
  ∑ k ∈ range N, ((N : ℝ) * psiD (N * t - k)) • (V (k + 1) - V k)

/-- **The polygon curve is differentiable** with velocity `polyCD`. -/
theorem hasDerivAt_polyC (N : ℕ) (V : ℕ → Space) (t : ℝ) :
    HasDerivAt (polyC N V) (polyCD N V t) t := by
  unfold polyC polyCD
  apply HasDerivAt.const_add
  apply HasDerivAt.fun_sum
  intro k _
  have h1 : HasDerivAt (fun t : ℝ => (N : ℝ) * t - k) (N : ℝ) t := by
    simpa using ((hasDerivAt_id' t).const_mul (N : ℝ)).sub_const (k : ℝ)
  have h2 := (hasDerivAt_psi ((N : ℝ) * t - k)).comp t h1
  have := h2.smul_const (V (k + 1) - V k)
  rw [show psiD (↑N * t - ↑k) * ↑N = ↑N * psiD (↑N * t - ↑k) from mul_comm _ _] at this
  exact this

/-- The velocity is continuous. -/
theorem continuous_polyCD (N : ℕ) (V : ℕ → Space) : Continuous (polyCD N V) := by
  unfold polyCD
  refine continuous_finsetSum _ fun k _ => ?_
  exact (continuous_const.mul (continuous_psiD.comp (by fun_prop))).smul continuous_const

/-- `deriv (polyC N V) = polyCD N V`. -/
theorem deriv_polyC (N : ℕ) (V : ℕ → Space) : deriv (polyC N V) = polyCD N V :=
  funext fun t => (hasDerivAt_polyC N V t).deriv

/-- The curve starts at `V 0`. -/
theorem polyC_zero (N : ℕ) (V : ℕ → Space) : polyC N V 0 = V 0 := by
  unfold polyC
  rw [Finset.sum_eq_zero]
  · simp
  · intro k _
    rw [psi_of_nonpos (by simp), zero_smul]

/-- Telescoping. -/
theorem sum_range_sub' (V : ℕ → Space) (n : ℕ) :
    ∑ k ∈ range n, (V (k + 1) - V k) = V n - V 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; abel

/-- The curve is closed when `V N = V 0`. -/
theorem polyC_one (N : ℕ) (V : ℕ → Space) (hV : V N = V 0) : polyC N V 1 = V 0 := by
  unfold polyC
  rw [Finset.sum_congr rfl (g := fun k => V (k + 1) - V k) fun k hk => ?_]
  · rw [sum_range_sub', hV]; abel
  · rw [Finset.mem_range] at hk
    rw [psi_of_one_le, one_smul]
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    linarith

/-- On the `k`-th piece `[k/N, (k+1)/N]` the curve runs along the `k`-th segment. -/
theorem polyC_on_piece (N : ℕ) (V : ℕ → Space) {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) / N) ((k + 1) / N)) :
    polyC N V t = seg (V k) (V (k + 1)) (psi (N * t - k)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have h1 : (k : ℝ) ≤ N * t := by
    have := ht.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : N * t ≤ k + 1 := by
    have := ht.2; rw [le_div_iff₀ hN] at this; linarith
  unfold polyC seg
  have hsplit : ∑ j ∈ range N, psi (N * t - j) • (V (j + 1) - V j) =
      ∑ j ∈ range k, (V (j + 1) - V j) + psi (N * t - k) • (V (k + 1) - V k) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ N by omega), sum_range_succ]
    rw [Finset.sum_eq_zero (s := Finset.Ico (k + 1) N) fun j hj => ?_]
    · rw [add_zero]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [psi_of_one_le, one_smul]
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      linarith
    · rw [Finset.mem_Ico] at hj
      rw [psi_of_nonpos, zero_smul]
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj.1
      linarith
  rw [hsplit, sum_range_sub']
  abel

/-- On the `k`-th piece the velocity is `N ψ'(N t - k) (V (k+1) - V k)`. -/
theorem polyCD_on_piece (N : ℕ) (V : ℕ → Space) {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) / N) ((k + 1) / N)) :
    polyCD N V t = ((N : ℝ) * psiD (N * t - k)) • (V (k + 1) - V k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have h1 : (k : ℝ) ≤ N * t := by
    have := ht.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : N * t ≤ k + 1 := by
    have := ht.2; rw [le_div_iff₀ hN] at this; linarith
  unfold polyCD
  rw [Finset.sum_eq_single k]
  · intro j _ hj
    rw [psiD_eq_zero, mul_zero, zero_smul]
    rcases lt_or_gt_of_ne hj with h | h
    · right
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith
    · left
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith
  · intro h; exact absurd (Finset.mem_range.mpr hk) h

/-! ## The field of the polygon -/

/-- Points of the closed polygon. -/
@[expose] def onPolygon (N : ℕ) (V : ℕ → Space) (y : Space) : Prop :=
  ∃ k < N, ∃ s ∈ Icc (0 : ℝ) 1, y = seg (V k) (V (k + 1)) s

/-- Off the polygon, `y - polyC t ≠ 0` for `t ∈ [0, 1]`. -/
theorem sub_polyC_ne {N : ℕ} {V : ℕ → Space} {y : Space} (hy : ¬ onPolygon N V y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hN : 0 < N) : y - polyC N V t ≠ 0 := by
  intro h
  apply hy
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- the piece containing `t`
  set k := min (⌊(N : ℝ) * t⌋₊) (N - 1) with hk
  have hkN : k < N := by omega
  have hk1 : (k : ℝ) ≤ N * t := by
    have h0 : 0 ≤ (N : ℝ) * t := by nlinarith [ht.1]
    have := Nat.floor_le h0
    have hmin : (k : ℝ) ≤ ⌊(N : ℝ) * t⌋₊ := by exact_mod_cast min_le_left _ _
    linarith
  have hk2 : (N : ℝ) * t ≤ k + 1 := by
    rcases le_total (⌊(N : ℝ) * t⌋₊) (N - 1) with hle | hle
    · rw [hk, min_eq_left hle]
      exact (Nat.lt_floor_add_one _).le
    · rw [hk, min_eq_right hle]
      have : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; nlinarith [ht.2]
  have htk : t ∈ Icc ((k : ℝ) / N) ((k + 1) / N) := by
    constructor
    · rw [div_le_iff₀ hNr]; linarith
    · rw [le_div_iff₀ hNr]; linarith
  refine ⟨k, hkN, psi (N * t - k), psi_mem _, ?_⟩
  rw [← polyC_on_piece N V hkN htk]
  exact sub_eq_zero.mp h

/-- **The Biot–Savart field of the polygon curve is the sum of its segment fields** at every
point off the polygon. -/
theorem filamentField_polyC (μ₀ I : ℝ) {N : ℕ} (hN : 0 < N) (V : ℕ → Space) {y : Space}
    (hy : ¬ onPolygon N V y) :
    filamentField μ₀ I (polyC N V) 0 1 y =
      ∑ k ∈ range N, filamentField μ₀ I (seg (V k) (V (k + 1))) 0 1 y := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold filamentField
  rw [← Finset.smul_sum]
  congr 1
  -- split `[0, 1]` into the `N` pieces
  set a : ℕ → ℝ := fun k => (k : ℝ) / N with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a N = 1 := by simp [ha, hNr.ne']
  have hcontK : ContinuousOn (fun t => filamentKernel (polyC N V) t y) (Icc 0 1) := by
    refine filamentKernel_continuousOn _ _ _
      (fun t _ => (hasDerivAt_polyC N V t).continuousAt.continuousWithinAt) ?_
      fun t ht => sub_polyC_ne hy ht hN
    · rw [deriv_polyC]; exact (continuous_polyCD N V).continuousOn
  have hsub : ∀ k < N, Icc (a k) (a (k + 1)) ⊆ Icc 0 1 := by
    intro k hk t ht
    constructor
    · exact le_trans (by simp only [ha]; positivity) ht.1
    · refine ht.2.trans ?_
      simp only [ha]; rw [div_le_one hNr]; exact_mod_cast hk
  have hint : ∀ k < N, IntervalIntegrable (fun t => filamentKernel (polyC N V) t y)
      MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    have hle : a k ≤ a (k + 1) := by simp only [ha]; gcongr; linarith
    exact ((hcontK.mono (hsub k hk)).mono (by rw [Set.uIcc_of_le hle])).intervalIntegrable
  rw [show (∫ t in (0 : ℝ)..1, filamentKernel (polyC N V) t y) =
      ∫ t in a 0..a N, filamentKernel (polyC N V) t y by rw [ha0, haN],
    ← intervalIntegral.sum_integral_adjacent_intervals hint]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  -- substitution on the `k`-th piece
  set f : ℝ → ℝ := fun t => psi (N * t - k)
  set f' : ℝ → ℝ := fun t => (N : ℝ) * psiD (N * t - k)
  have hle : a k ≤ a (k + 1) := by simp only [ha]; gcongr; linarith
  have hf : ∀ t ∈ uIcc (a k) (a (k + 1)), HasDerivAt f (f' t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (N : ℝ) * t - k) (N : ℝ) t := by
      simpa using ((hasDerivAt_id' t).const_mul (N : ℝ)).sub_const (k : ℝ)
    have := (hasDerivAt_psi ((N : ℝ) * t - k)).comp t h1
    rw [show psiD (↑N * t - ↑k) * ↑N = f' t from mul_comm _ _] at this
    exact this
  have hf' : ContinuousOn f' (uIcc (a k) (a (k + 1))) :=
    (continuous_const.mul (continuous_psiD.comp (by fun_prop))).continuousOn
  have hg : ContinuousOn (fun s => filamentKernel (seg (V k) (V (k + 1))) s y)
      (f '' uIcc (a k) (a (k + 1))) := by
    have hdc : deriv (seg (V k) (V (k + 1))) = fun _ => V (k + 1) - V k :=
      funext (deriv_seg _ _)
    refine filamentKernel_continuousOn _ _ _ (continuous_seg _ _).continuousOn
      (by rw [hdc]; exact continuousOn_const) fun s hs => ?_
    obtain ⟨t, -, rfl⟩ := hs
    intro h0
    exact hy ⟨k, hk, psi (N * t - k), psi_mem _, (sub_eq_zero.mp h0)⟩
  have hfa : f (a k) = 0 := by
    change psi (N * ((k : ℝ) / N) - k) = 0
    rw [mul_div_cancel₀ _ hNr.ne', sub_self]; exact psi_of_nonpos le_rfl
  have hfb : f (a (k + 1)) = 1 := by
    change psi (N * (((k + 1 : ℕ) : ℝ) / N) - k) = 1
    rw [mul_div_cancel₀ _ hNr.ne']; push_cast; exact psi_of_one_le (by linarith)
  have hsubst := intervalIntegral.integral_deriv_smul_comp' hf hf' hg
  rw [hfa, hfb] at hsubst
  rw [← hsubst]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hle] at ht
  have ht' : t ∈ Icc ((k : ℝ) / N) ((k + 1) / N) := by
    simpa [ha] using ht
  simp only [Function.comp, f, f']
  unfold filamentKernel
  rw [deriv_polyC, polyCD_on_piece N V hk ht', polyC_on_piece N V hk ht', deriv_seg,
    cross_smul_left, smul_comm]

end PlasmaLean.Design.PolygonCoil
