/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.LogNormTrajectory

/-!
# Backward distance estimates from a lower one-sided bound

A lower bound `-ℓ‖d‖² ≤ ⟪d, J d⟫` on the quadratic form of the spatial Jacobian limits
the rate at which two solutions of the same equation can approach each other. The
separation at the start of a time slab is then at most `exp (ℓ (b - a))` times the
separation at its end. The coefficient may have either sign. Slabs with different
coefficients compose by adding the exponents.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Fields.BackwardDistance

open Set Filter Real
open scoped Topology RealInnerProductSpace
open PlasmaLean.Fields.LogNormTrajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Signed lower one-sided Lipschitz coefficient on a spatial slice. -/
def LowerOneSidedOn (F : E → E) (s : Set E) (ℓ : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, -ℓ * ‖x - y‖ ^ 2 ≤ ⟪x - y, F x - F y⟫

/-- The lower bound for a field is the upper one-sided bound for the reversed field. -/
theorem lowerOneSidedOn_iff_neg {F : E → E} {s : Set E} {ℓ : ℝ} :
    LowerOneSidedOn F s ℓ ↔ OneSidedOn (-F) s ℓ := by
  have key (x y : E) : ⟪x - y, (-F) x - (-F) y⟫ = -⟪x - y, F x - F y⟫ := by
    rw [← inner_neg_right]
    congr 1
    simp only [Pi.neg_apply]
    abel
  constructor
  · intro h x hx y hy
    rw [key]
    linarith only [h x hx y hy]
  · intro h x hx y hy
    have h' := h x hx y hy
    rw [key] at h'
    linarith only [h']

/-- A weaker coefficient is still a lower one-sided bound. -/
theorem LowerOneSidedOn.mono {F : E → E} {s u : Set E} {ℓ ℓ' : ℝ}
    (h : LowerOneSidedOn F s ℓ) (hu : u ⊆ s) (hℓ : ℓ ≤ ℓ') : LowerOneSidedOn F u ℓ' := by
  intro x hx y hy
  have h' := h x (hu hx) y (hu hy)
  nlinarith only [h', mul_le_mul_of_nonneg_right hℓ (sq_nonneg ‖x - y‖)]

/-- A pointwise lower bound for the Jacobian quadratic form gives the lower one-sided
inequality on the whole convex slice. -/
theorem lowerOneSidedOn_of_jacobian {F : E → E} {J : E → E →L[ℝ] E} {s : Set E} {ℓ : ℝ}
    (hs : Convex ℝ s) (hF : ∀ z ∈ s, HasFDerivAt F (J z) z)
    (hJ : ∀ z ∈ s, ∀ d : E, -ℓ * ‖d‖ ^ 2 ≤ ⟪d, J z d⟫) : LowerOneSidedOn F s ℓ := by
  rw [lowerOneSidedOn_iff_neg]
  apply oneSidedOn_of_jacobian (J := fun z => -J z) hs (fun z hz => (hF z hz).neg)
  intro z hz d
  have h := hJ z hz d
  simp only [neg_apply, inner_neg_right]
  linarith only [h]

/-- Backward distance estimate at every time of the slab. Two solutions of the same
equation that stay in slices carrying the lower one-sided coefficient `ℓ` were, at the
start, no further apart than `exp (ℓ (t - a))` times their separation at time `t`. -/
theorem norm_sub_le_exp_mul_of_lower {F : ℝ → E → E} {s : ℝ → Set E} {x y : ℝ → E}
    {a b ℓ : ℝ} (hℓ : ∀ t ∈ Ico a b, LowerOneSidedOn (F t) (s t) ℓ)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (F t (y t)) (Ici t) t)
    (hxs : ∀ t ∈ Ico a b, x t ∈ s t) (hys : ∀ t ∈ Ico a b, y t ∈ s t) :
    ∀ t ∈ Icc a b, ‖x a - y a‖ ≤ exp (ℓ * (t - a)) * ‖x t - y t‖ := by
  let e := fun t => x t - y t
  let g := fun t => exp (2 * ℓ * t) * ‖e t‖ ^ 2
  let g' := fun t => 2 * ℓ * exp (2 * ℓ * t) * ‖e t‖ ^ 2 +
    exp (2 * ℓ * t) * (2 * ⟪e t, F t (x t) - F t (y t)⟫)
  have hgc : ContinuousOn g (Icc a b) :=
    (Continuous.continuousOn (by fun_prop)).mul ((hx.sub hy).norm.pow 2)
  have hgd (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt g (g' t) (Ici t) t := by
    have h₁ : HasDerivWithinAt (fun t => exp (2 * ℓ * t)) (2 * ℓ * exp (2 * ℓ * t)) (Ici t) t := by
      have h := ((hasDerivAt_id t).const_mul (2 * ℓ)).exp
      simp only [id_eq, mul_one] at h
      convert h.hasDerivWithinAt using 1
      ring
    exact h₁.mul ((hxd t ht).sub (hyd t ht)).norm_sq
  have hpos (t : ℝ) (ht : t ∈ Ico a b) : 0 ≤ g' t := by
    have h := hℓ t ht (x t) (hxs t ht) (y t) (hys t ht)
    have hfac : g' t = 2 * exp (2 * ℓ * t) *
        (⟪e t, F t (x t) - F t (y t)⟫ - -ℓ * ‖e t‖ ^ 2) := by
      simp only [g']
      ring
    rw [hfac]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr h)
  intro t ht
  have hmono : g a ≤ g t :=
    image_le_of_deriv_right_le_deriv_boundary (f := fun _ => g a) (f' := fun _ => 0)
      continuousOn_const (fun u _ => hasDerivWithinAt_const u (Ici u) (g a)) le_rfl hgc hgd
      hpos ht
  have hsq : ‖e a‖ ^ 2 ≤ (exp (ℓ * (t - a)) * ‖e t‖) ^ 2 := by
    have hsplit : exp (2 * ℓ * t) = exp (2 * ℓ * a) * exp (ℓ * (t - a)) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have h : exp (2 * ℓ * a) * ‖e a‖ ^ 2 ≤
        exp (2 * ℓ * a) * ((exp (ℓ * (t - a)) * ‖e t‖) ^ 2) := by
      calc exp (2 * ℓ * a) * ‖e a‖ ^ 2 ≤ exp (2 * ℓ * t) * ‖e t‖ ^ 2 := hmono
        _ = exp (2 * ℓ * a) * ((exp (ℓ * (t - a)) * ‖e t‖) ^ 2) := by rw [hsplit]; ring
    exact le_of_mul_le_mul_left h (exp_pos _)
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- Backward distance estimate over a slab: the initial separation is at most
`exp (ℓ (b - a))` times the final separation. -/
theorem norm_sub_le_exp_mul_of_lower_endpoint {F : ℝ → E → E} {s : ℝ → Set E}
    {x y : ℝ → E} {a b ℓ : ℝ} (hab : a ≤ b)
    (hℓ : ∀ t ∈ Ico a b, LowerOneSidedOn (F t) (s t) ℓ)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (F t (y t)) (Ici t) t)
    (hxs : ∀ t ∈ Ico a b, x t ∈ s t) (hys : ∀ t ∈ Ico a b, y t ∈ s t) :
    ‖x a - y a‖ ≤ exp (ℓ * (b - a)) * ‖x b - y b‖ :=
  norm_sub_le_exp_mul_of_lower hℓ hx hy hxd hyd hxs hys b (right_mem_Icc.mpr hab)

/-- Two backward estimates compose by adding their exponents. The exponents are
arbitrary reals, so a list of slabs can be chained by induction. -/
theorem le_exp_add_mul_of_le {p q r A B : ℝ} (h₁ : p ≤ exp A * q) (h₂ : q ≤ exp B * r) :
    p ≤ exp (A + B) * r := by
  rw [Real.exp_add, mul_assoc]
  exact h₁.trans (mul_le_mul_of_nonneg_left h₂ (exp_pos A).le)

/-- Backward distance estimate over two consecutive slabs with their own coefficients. -/
theorem norm_sub_le_exp_mul_of_lower_two {F : ℝ → E → E} {s : ℝ → Set E} {x y : ℝ → E}
    {a b c ℓ₁ ℓ₂ : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hℓ₁ : ∀ t ∈ Ico a b, LowerOneSidedOn (F t) (s t) ℓ₁)
    (hℓ₂ : ∀ t ∈ Ico b c, LowerOneSidedOn (F t) (s t) ℓ₂)
    (hx : ContinuousOn x (Icc a c)) (hy : ContinuousOn y (Icc a c))
    (hxd : ∀ t ∈ Ico a c, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a c, HasDerivWithinAt y (F t (y t)) (Ici t) t)
    (hxs : ∀ t ∈ Ico a c, x t ∈ s t) (hys : ∀ t ∈ Ico a c, y t ∈ s t) :
    ‖x a - y a‖ ≤ exp (ℓ₁ * (b - a) + ℓ₂ * (c - b)) * ‖x c - y c‖ := by
  have h₁ : Ico a b ⊆ Ico a c := Ico_subset_Ico_right hbc
  have h₂ : Ico b c ⊆ Ico a c := Ico_subset_Ico_left hab
  exact le_exp_add_mul_of_le
    (norm_sub_le_exp_mul_of_lower_endpoint hab hℓ₁ (hx.mono (Icc_subset_Icc_right hbc))
      (hy.mono (Icc_subset_Icc_right hbc)) (fun t ht => hxd t (h₁ ht))
      (fun t ht => hyd t (h₁ ht)) (fun t ht => hxs t (h₁ ht)) (fun t ht => hys t (h₁ ht)))
    (norm_sub_le_exp_mul_of_lower_endpoint hbc hℓ₂ (hx.mono (Icc_subset_Icc_left hab))
      (hy.mono (Icc_subset_Icc_left hab)) (fun t ht => hxd t (h₂ ht))
      (fun t ht => hyd t (h₂ ht)) (fun t ht => hxs t (h₂ ht)) (fun t ht => hys t (h₂ ht)))

/-- Chain of slab estimates along nodes `τ 0, τ 1, …, τ n`. Each step may come from
`norm_sub_le_exp_mul_of_lower_endpoint` with its own coefficient `ℓ i`. -/
theorem le_exp_sum_mul_of_steps {d : ℕ → ℝ} {τ ℓ : ℕ → ℝ} {n : ℕ}
    (h : ∀ i < n, d i ≤ exp (ℓ i * (τ (i + 1) - τ i)) * d (i + 1)) :
    d 0 ≤ exp (∑ i ∈ Finset.range n, ℓ i * (τ (i + 1) - τ i)) * d n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_exp_add_mul_of_le (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n n.lt_succ_self)

/-- Backward distance estimate over a chain of slabs with nodes `τ 0 ≤ τ 1 ≤ … ≤ τ n`
and a lower one-sided coefficient `ℓ i` on the slab from `τ i` to `τ (i + 1)`. -/
theorem norm_sub_le_exp_sum_mul_of_lower {F : ℝ → E → E} {s : ℝ → Set E} {x y : ℝ → E}
    {τ ℓ : ℕ → ℝ} {n : ℕ} (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hℓ : ∀ i < n, ∀ t ∈ Ico (τ i) (τ (i + 1)), LowerOneSidedOn (F t) (s t) (ℓ i))
    (hx : ∀ i < n, ContinuousOn x (Icc (τ i) (τ (i + 1))))
    (hy : ∀ i < n, ContinuousOn y (Icc (τ i) (τ (i + 1))))
    (hxd : ∀ i < n, ∀ t ∈ Ico (τ i) (τ (i + 1)), HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ i < n, ∀ t ∈ Ico (τ i) (τ (i + 1)), HasDerivWithinAt y (F t (y t)) (Ici t) t)
    (hxs : ∀ i < n, ∀ t ∈ Ico (τ i) (τ (i + 1)), x t ∈ s t)
    (hys : ∀ i < n, ∀ t ∈ Ico (τ i) (τ (i + 1)), y t ∈ s t) :
    ‖x (τ 0) - y (τ 0)‖ ≤
      exp (∑ i ∈ Finset.range n, ℓ i * (τ (i + 1) - τ i)) * ‖x (τ n) - y (τ n)‖ :=
  le_exp_sum_mul_of_steps (d := fun i => ‖x (τ i) - y (τ i)‖) fun i hi =>
    norm_sub_le_exp_mul_of_lower_endpoint (hτ i hi) (hℓ i hi) (hx i hi) (hy i hi) (hxd i hi)
      (hyd i hi) (hxs i hi) (hys i hi)

/-- The linear field `x ↦ c • x` has lower one-sided coefficient `-c` on the whole space. -/
theorem lowerOneSidedOn_smul (c : ℝ) : LowerOneSidedOn (fun x : E => c • x) univ (-c) := by
  intro x _ y _
  rw [← smul_sub, inner_smul_right, real_inner_self_eq_norm_sq, neg_neg]

/-- The path `t ↦ exp (c t) • v` solves the linear equation `x' = c • x`. -/
theorem hasDerivAt_exp_smul (c : ℝ) (v : E) (t : ℝ) :
    HasDerivAt (fun t => exp (c * t) • v) (c • exp (c * t) • v) t := by
  have h := (((hasDerivAt_id t).const_mul c).exp).smul_const v
  simp only [id_eq, mul_one] at h
  convert h using 1
  rw [smul_smul, mul_comm]

/-- The backward estimate is attained by the linear field: for the solutions
`exp (c t) • v` and `0` of `x' = c • x`, with coefficient `ℓ = -c`, equality holds. -/
theorem norm_exp_smul_sub_zero_eq (c a b : ℝ) (v : E) :
    ‖exp (c * a) • v - 0‖ = exp (-c * (b - a)) * ‖exp (c * b) • v - 0‖ := by
  simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end PlasmaLean.Fields.BackwardDistance
