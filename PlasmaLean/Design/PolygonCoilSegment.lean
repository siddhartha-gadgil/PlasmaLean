/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorCoilsTF

/-!
# The Biot–Savart field of a straight segment in closed form

For a straight filament `p → q` (parametrised by `seg p q t = p + t (q - p)`, `t ∈ [0, 1]`)
carrying current `I`, with `a = p - y`, `b = q - y`,

`filamentField μ₀ I (seg p q) 0 1 y = (μ₀I/4π) · (|a| + |b|)/(|a||b|(|a||b| + a·b)) · (a × b)`

at **every** point `y` (`segField_eq_closed`); on the line of the segment both sides vanish
(Lean's `0⁻¹ = 0`). This extends `CoilsTF.axisSeg_eq` (the axis segment) to arbitrary segments.

Method: the kernel is `|a + t v|⁻³ (a × b)` (`v = q - p`); the scalar integrand has the
antiderivative `(t|v|² + a·v)/((|a|²|v|² - (a·v)²)|a + t v|)` (`hasDerivAt_segG`), and the
endpoint values simplify to the closed form by `|a|²|v|² - (a·v)² = |a|²|b|² - (a·b)²`.

Also: the factor `segFac` is antitone in `|a|`, `|b|` and changes by a relative amount `≤ 7u`
when `|a|`, `|b|` grow by a relative amount `u ≤ 1/100` (`segFac'_mono`, `segFac'_ratio`), which
justifies the square-root brackets of the checker `Design/PolygonCoilCheck`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator.CoilsTF
open scoped RealInnerProductSpace

/-- The scalar factor `f(α, β; c) = (α + β)/(αβ(αβ + c))`. -/
@[expose] def segFac' (α β c : ℝ) : ℝ := (α + β) / (α * β * (α * β + c))

/-- The closed-form field of the segment `p → q` with current factor `κ = μ₀I/4π`. -/
@[expose] def segClosed (κ : ℝ) (p q y : Space) : Space :=
  (κ * segFac' ‖p - y‖ ‖q - y‖ ⟪p - y, q - y⟫) • cross (p - y) (q - y)

/-- Cross product with itself vanishes. -/
theorem cross_self' (u : Space) : cross u u = 0 := by
  unfold cross; simp [cross_self]

/-- Cross product is antisymmetric. -/
theorem cross_anticomm' (u v : Space) : cross u v = -cross v u := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

/-- Cross product is additive in the second slot. -/
theorem cross_add_right (u v w : Space) : cross u (v + w) = cross u v + cross u w := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

/-- Cross product is homogeneous in the second slot. -/
theorem cross_smul_right (u v : Space) (t : ℝ) : cross u (t • v) = t • cross u v := by
  ext i; fin_cases i <;> simp [cross, crossProduct] 

/-- Cross product is additive in the first slot. -/
theorem cross_add_left (u v w : Space) : cross (u + v) w = cross u w + cross v w := by
  ext i; fin_cases i <;> simp [cross, crossProduct] 

/-- Cross product is homogeneous in the first slot. -/
theorem cross_smul_left (u v : Space) (t : ℝ) : cross (t • u) v = t • cross u v := by
  ext i; fin_cases i <;> simp [cross, crossProduct] 

/-- Cross product with a negation in the second slot. -/
theorem cross_neg_right (u v : Space) : cross u (-v) = -cross u v := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

/-- The segment kernel: `|a + t v|⁻³ (a × b)` with `a = p - y`, `b = q - y`, `v = q - p`. -/
theorem seg_kernel (p q y : Space) (t : ℝ) :
    filamentKernel (seg p q) t y =
      (‖(p - y) + t • (q - p)‖ ^ 3)⁻¹ • cross (p - y) (q - y) := by
  unfold filamentKernel
  rw [deriv_seg]
  have e1 : y - seg p q t = -((p - y) + t • (q - p)) := by unfold seg; abel
  have e2 : cross (q - p) (-((p - y) + t • (q - p))) = cross (p - y) (q - y) := by
    rw [cross_neg_right, cross_add_right, cross_smul_right, cross_self', smul_zero, add_zero,
      cross_anticomm' (q - p)]
    have : q - y = (p - y) + (q - p) := by abel
    rw [neg_neg, this, cross_add_right, cross_self', zero_add]
  rw [e1, e2, norm_neg]

/-- `|a + t v|² = |a|² + 2t a·v + t²|v|²`. -/
theorem norm_add_smul_sq (a v : Space) (t : ℝ) :
    ‖a + t • v‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * ⟪a, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The Gram determinant `|a|²|v|² - (a·v)²`. -/
@[expose] def gram (a v : Space) : ℝ := ‖a‖ ^ 2 * ‖v‖ ^ 2 - ⟪a, v⟫ ^ 2

/-- The antiderivative of `|a + t v|⁻³`. -/
@[expose] def segG (a v : Space) (t : ℝ) : ℝ :=
  (t * ‖v‖ ^ 2 + ⟪a, v⟫) / (gram a v * ‖a + t • v‖)

/-- `segG' = |a + t v|⁻³` when `a + t v ≠ 0` and the Gram determinant is positive. -/
theorem hasDerivAt_segG {a v : Space} (hg : 0 < gram a v) (t : ℝ) (ht : a + t • v ≠ 0) :
    HasDerivAt (segG a v) ((‖a + t • v‖ ^ 3)⁻¹) t := by
  set Q : ℝ → ℝ := fun s => ‖a‖ ^ 2 + 2 * s * ⟪a, v⟫ + s ^ 2 * ‖v‖ ^ 2 with hQ
  have hQe : ∀ s, ‖a + s • v‖ = Real.sqrt (Q s) := fun s => by
    rw [show Q s = ‖a‖ ^ 2 + 2 * s * ⟪a, v⟫ + s ^ 2 * ‖v‖ ^ 2 from rfl, ← norm_add_smul_sq,
      Real.sqrt_sq (norm_nonneg _)]
  have hQpos : 0 < Q t := by
    rw [show Q t = ‖a‖ ^ 2 + 2 * t * ⟪a, v⟫ + t ^ 2 * ‖v‖ ^ 2 from rfl, ← norm_add_smul_sq]
    exact pow_pos (norm_pos_iff.mpr ht) 2
  have hQd : HasDerivAt Q (2 * ⟪a, v⟫ + 2 * t * ‖v‖ ^ 2) t := by
    have h := (((hasDerivAt_id t).const_mul (2 * ⟪a, v⟫)).const_add (‖a‖ ^ 2)).add
      (((hasDerivAt_id t).pow 2).mul_const (‖v‖ ^ 2))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [Q, id, Pi.add_apply, Pi.pow_apply]; ring
    · simp
  have hs := hQd.sqrt hQpos.ne'
  have hN : HasDerivAt (fun s => s * ‖v‖ ^ 2 + ⟪a, v⟫) (‖v‖ ^ 2) t := by
    simpa using ((hasDerivAt_id t).mul_const (‖v‖ ^ 2)).add_const ⟪a, v⟫
  have hden := hs.const_mul (gram a v)
  have hsq : 0 < Real.sqrt (Q t) := Real.sqrt_pos.mpr hQpos
  have hd := hN.div hden (by positivity)
  have hfun : segG a v = fun s => (s * ‖v‖ ^ 2 + ⟪a, v⟫) / (gram a v * Real.sqrt (Q s)) := by
    funext s; unfold segG; rw [hQe]
  rw [hfun]
  convert hd using 1
  rw [hQe]
  have h2 : Real.sqrt (Q t) ^ 2 = Q t := Real.sq_sqrt hQpos.le
  have hgram : gram a v = ‖v‖ ^ 2 * Q t - (t * ‖v‖ ^ 2 + ⟪a, v⟫) ^ 2 := by
    simp only [gram, hQ]; ring
  have hgne : gram a v ≠ 0 := hg.ne'
  generalize Real.sqrt (Q t) = S at h2 hsq ⊢
  rw [← h2] at hgram
  generalize gram a v = g at hgram hgne ⊢
  have hS : S ≠ 0 := hsq.ne'
  field_simp
  rw [hgram]
  ring

/-- If `a × b ≠ 0` then `a + t (b - a) ≠ 0` for every `t`. -/
theorem add_smul_ne_zero {a b : Space} (h : cross a b ≠ 0) (t : ℝ) : a + t • (b - a) ≠ 0 := by
  intro h0
  apply h
  have ha : a = -(t • (b - a)) := eq_neg_of_add_eq_zero_left h0
  have : cross a b = cross a (b - a) := by
    rw [show b - a = b + (-a) by abel, cross_add_right, cross_neg_right, cross_self', neg_zero,
      add_zero]
  rw [this, congrArg (cross · (b - a)) ha]
  rw [cross_anticomm', cross_neg_right, cross_smul_right, cross_self', smul_zero, neg_zero,
    neg_zero]

/-- Lagrange's identity `|a × b|² = |a|²|b|² - (a·b)²`. -/
theorem norm_cross_sq (a b : Space) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  simp only [cross, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_three,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp [crossProduct]
  ring

/-- The Gram determinants of `(a, b - a)` and `(a, b)` agree. -/
theorem gram_sub (a b : Space) : gram a (b - a) = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  unfold gram
  rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm a b]
  ring

/-- **Closed form of the Biot–Savart field of a straight segment**, valid at every point. -/
theorem segField_eq_closed (μ₀ I : ℝ) (p q y : Space) :
    filamentField μ₀ I (seg p q) 0 1 y = segClosed (μ₀ * I / (4 * Real.pi)) p q y := by
  unfold filamentField segClosed
  simp_rw [seg_kernel]
  rw [intervalIntegral.integral_smul_const, smul_smul]
  set a := p - y
  set b := q - y
  have hv : q - p = b - a := by simp [a, b]
  by_cases hc : cross a b = 0
  · simp [hc]
  congr 2
  have hg : 0 < gram a (b - a) := by
    rw [gram_sub, ← norm_cross_sq]
    exact pow_pos (norm_pos_iff.mpr hc) 2
  have hne : ∀ t, a + t • (b - a) ≠ 0 := add_smul_ne_zero hc
  have hcont : Continuous (fun t : ℝ => (‖a + t • (b - a)‖ ^ 3)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun t => pow_ne_zero _ (norm_ne_zero_iff.mpr (hne t))
  rw [hv, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_segG hg t (hne t)) (hcont.intervalIntegrable 0 1)]
  -- evaluate the antiderivative
  unfold segG segFac'
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, zero_add]
  have hab : a + (b - a) = b := by abel
  rw [hab]
  have hα : 0 < ‖a‖ := norm_pos_iff.mpr (by simpa using hne 0)
  have hβ : 0 < ‖b‖ := norm_pos_iff.mpr (by simpa [hab] using hne 1)
  have hcs : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by rw [← norm_cross_sq]; positivity
  have hpos : 0 < ‖a‖ * ‖b‖ + ⟪a, b⟫ := by
    have : |⟪a, b⟫| < ‖a‖ * ‖b‖ := by
      have h2 : ⟪a, b⟫ ^ 2 < (‖a‖ * ‖b‖) ^ 2 := by nlinarith
      exact abs_lt_of_sq_lt_sq' h2 (by positivity) |>.2 |> fun h => by
        rw [abs_lt]; exact ⟨by nlinarith [abs_lt_of_sq_lt_sq' h2 (by positivity)], h⟩
    linarith [neg_abs_le ⟪a, b⟫]
  have hneg : 0 < ‖a‖ * ‖b‖ - ⟪a, b⟫ := by
    have : ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 = (‖a‖ * ‖b‖ - ⟪a, b⟫) * (‖a‖ * ‖b‖ + ⟪a, b⟫) := by ring
    rw [this] at hcs
    exact pos_of_mul_pos_left hcs hpos.le |> fun h => by nlinarith
  rw [gram_sub]
  have hvv : ‖b - a‖ ^ 2 = ‖b‖ ^ 2 - 2 * ⟪a, b⟫ + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hav : ⟪a, b - a⟫ = ⟪a, b⟫ - ‖a‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hvv, hav]
  have hfac : ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 =
      (‖a‖ * ‖b‖ - ⟪a, b⟫) * (‖a‖ * ‖b‖ + ⟪a, b⟫) := by ring
  have hG : ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 ≠ 0 := hcs.ne'
  rw [div_sub_div _ _ (mul_ne_zero hG hβ.ne') (mul_ne_zero hG hα.ne'),
    div_eq_div_iff (by positivity) (by positivity), hfac]
  ring

/-! ## Monotonicity of the factor -/

/-- The factor is antitone: larger lengths give a smaller factor (`c` fixed, `αβ + c > 0`). -/
theorem segFac'_mono {α β α' β' c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαα : α ≤ α') (hββ : β ≤ β')
    (hc : 0 < α * β + c) : segFac' α' β' c ≤ segFac' α β c := by
  unfold segFac'
  have hα' : 0 < α' := lt_of_lt_of_le hα hαα
  have hβ' : 0 < β' := lt_of_lt_of_le hβ hββ
  have hab : α * β ≤ α' * β' := mul_le_mul hαα hββ hβ.le hα'.le
  have hc' : 0 < α' * β' + c := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- (α' + β') αβ(αβ + c) ≤ (α + β) α'β'(α'β' + c)
  have h1 : (α' + β') * (α * β) ≤ (α + β) * (α' * β') := by
    nlinarith [mul_nonneg (mul_nonneg hα.le hα'.le) (sub_nonneg.2 hββ),
      mul_nonneg (mul_nonneg hβ.le hβ'.le) (sub_nonneg.2 hαα)]
  have h2 : α * β + c ≤ α' * β' + c := by linarith
  calc (α' + β') * (α * β * (α * β + c)) = ((α' + β') * (α * β)) * (α * β + c) := by ring
    _ ≤ ((α + β) * (α' * β')) * (α' * β' + c) :=
        mul_le_mul h1 h2 hc.le (by positivity)
    _ = (α + β) * (α' * β' * (α' * β' + c)) := by ring

/-- Relative change of the factor: if `α ≤ α' ≤ α(1+u)`, `β ≤ β' ≤ β(1+u)`, `0 ≤ u ≤ 1/100`
and `αβ + 2c ≥ 0`, then `f(α', β') ≥ (1 - 7u) f(α, β)`. -/
theorem segFac'_ratio {α β α' β' c u : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαα : α ≤ α')
    (hββ : β ≤ β') (hα' : α' ≤ α * (1 + u)) (hβ' : β' ≤ β * (1 + u)) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 100) (hc : 0 ≤ α * β + 2 * c) :
    (1 - 7 * u) * segFac' α β c ≤ segFac' α' β' c := by
  unfold segFac'
  have hαp : 0 < α' := lt_of_lt_of_le hα hαα
  have hβp : 0 < β' := lt_of_lt_of_le hβ hββ
  have hpos : 0 < α * β + c := by nlinarith [mul_pos hα hβ]
  have hab : α * β ≤ α' * β' := mul_le_mul hαα hββ hβ.le hαp.le
  have hab' : α' * β' ≤ α * β * (1 + u) ^ 2 := by
    calc α' * β' ≤ (α * (1 + u)) * (β * (1 + u)) :=
          mul_le_mul hα' hβ' hβp.le (by positivity)
      _ = α * β * (1 + u) ^ 2 := by ring
  have hc' : 0 < α' * β' + c := by linarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [← sub_nonneg]
  -- key: α'β'(α'β' + c) ≤ αβ(αβ + c)(1+u)²(1 + 4u + 2u²) ≤ αβ(αβ+c)/(1-7u)
  have hk : α' * β' + c ≤ (α * β + c) * (1 + 4 * u + 2 * u ^ 2) := by
    have : α * β * ((1 + u) ^ 2 - 1) ≤ 2 * (α * β + c) * ((1 + u) ^ 2 - 1) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by nlinarith)
    nlinarith
  have hP : α' * β' * (α' * β' + c) ≤
      α * β * (α * β + c) * ((1 + u) ^ 2 * (1 + 4 * u + 2 * u ^ 2)) := by
    calc α' * β' * (α' * β' + c) ≤ (α * β * (1 + u) ^ 2) * ((α * β + c) * (1 + 4 * u + 2 * u ^ 2))
        :=
          mul_le_mul hab' hk hc'.le (by positivity)
      _ = _ := by ring
  have hpoly : (1 - 7 * u) * ((1 + u) ^ 2 * (1 + 4 * u + 2 * u ^ 2)) ≤ 1 := by
    nlinarith [pow_nonneg hu0 2, pow_nonneg hu0 3, pow_nonneg hu0 4, pow_nonneg hu0 5]
  have hsum : α + β ≤ α' + β' := by linarith
  have hX : 0 < α * β * (α * β + c) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hP (show 0 ≤ (1 - 7 * u) * (α + β) by nlinarith),
    mul_le_mul_of_nonneg_right hsum hX.le, mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ (α + β) * (α * β * (α * β + c)) by positivity)]

/-! ## Sanity checks -/

/-- Degenerate case: a point on the line of the segment sees no field. -/
theorem segClosed_on_line (κ : ℝ) (p q : Space) (t : ℝ) :
    segClosed κ p q (p + t • (q - p)) = 0 := by
  unfold segClosed
  have : cross (p - (p + t • (q - p))) (q - (p + t • (q - p))) = 0 := by
    have e1 : p - (p + t • (q - p)) = -(t • (q - p)) := by abel
    have e2 : q - (p + t • (q - p)) = (1 - t) • (q - p) := by
      rw [sub_smul, one_smul]; abel
    rw [e1, e2, cross_smul_right]
    rw [show -(t • (q - p)) = (-t) • (q - p) by rw [neg_smul], cross_smul_left, cross_self']
    simp
  rw [this, smul_zero]

/-- Zero current gives zero closed-form field. -/
theorem segClosed_zero (p q y : Space) : segClosed 0 p q y = 0 := by simp [segClosed]

end PlasmaLean.Design.PolygonCoil
