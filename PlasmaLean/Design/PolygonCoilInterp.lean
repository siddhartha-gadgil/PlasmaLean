/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSegment
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Interpolation-error bounds for Biot–Savart fields of segments along curves

The frontier certificate (`Design/PolygonCoilSoundA`-`D`) bounds the field error on a grid cell by
its values at the four corners plus a bilinear-interpolation remainder. This module supplies the
analytic ingredients.

* `lin_interp_bound` (**linear interpolation**): if `|g''| ≤ M` on `[a, b]` then
  `|(b - a) g(x) - ((b - x) g(a) + (x - a) g(b))| ≤ M (x - a)(b - x)(b - a)/2`
  (convexity of `±(g - L) - M(x - a)(b - x)/2`).
* `kg`, `kg1`, `kg2`, `hasDerivAt_kg`, `hasDerivAt_kg1`: the scalar kernel
  `g(τ) = ⟨m, u(τ)⟩/|u(τ)|³` along a `C²` curve `u` and its first two derivatives, and
  `abs_kg2_le` (**sharp kernel bound**): `|g''| ≤ |m| (6|u'|²/|u|⁴ + 2|u''|/|u|³)`. The constant
  `6` (instead of the naive `18`) comes from the exact identity
  `|W|²|u|¹⁰ = 45c⁴/|u|² - 18c²|u'|² + 9|u'|⁴|u|²`, `c = ⟨u, u'⟩`, for the `u'`-quadratic part
  `W` of `g''`, together with `c² ≤ |u|²|u'|²`.
* `segField_interp_bound`: the integrated statement for the field of a straight segment
  `p → q` (current factor `κ`) along a `C²` curve `σ` staying at distance `≥ d` from the
  segment, with `|σ'| ≤ S₁`, `|σ''| ≤ S₂`:
  `|(b - a)G(x) - ((b - x)G(a) + (x - a)G(b))| ≤ |κ||n||q - p|(6S₁²/d⁴ + 2S₂/d³)(x-a)(b-x)(b-a)/2`
  for `G(τ) = ⟨n, F(σ(τ))⟩`.
* `bilinear_cell_bound`: corner values plus the two one-dimensional interpolation bounds give a
  bound on a whole cell.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator.CoilsTF Set
open scoped RealInnerProductSpace

/-! ## Linear interpolation -/

/-- **Linear interpolation error** in multiplied form. -/
theorem lin_interp_bound {g g' g'' : ℝ → ℝ} {a b M x : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b)
    (hg : ∀ y ∈ Icc a b, HasDerivAt g (g' y) y) (hg' : ∀ y ∈ Icc a b, HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Icc a b, |g'' y| ≤ M) :
    |(b - a) * g x - ((b - x) * g a + (x - a) * g b)| ≤ M * (x - a) * (b - x) * (b - a) / 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    have : x = a := le_antisymm hx.2 hx.1
    subst this; simp
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ε * ((b - a) * g x - ((b - x) * g a + (x - a) * g b)) ≤
        M * (x - a) * (b - x) * (b - a) / 2 := by
    intro ε hε
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    set ψ : ℝ → ℝ := fun y => ε * ((b - a) * g y - ((b - y) * g a + (y - a) * g b)) -
      M * (y - a) * (b - y) * (b - a) / 2 with hψ
    set ψ' : ℝ → ℝ := fun y => ε * ((b - a) * g' y + g a - g b) -
      M * (b - a) * (a + b - 2 * y) / 2 with hψ'
    set ψ'' : ℝ → ℝ := fun y => ε * ((b - a) * g'' y) + M * (b - a) with hψ''
    have hd1 : ∀ y ∈ Icc a b, HasDerivAt ψ (ψ' y) y := by
      intro y hy
      have h1 := (((hg y hy).const_mul (b - a)).sub
        ((((hasDerivAt_id y).const_sub b).mul_const (g a)).add
          (((hasDerivAt_id y).sub_const a).mul_const (g b)))).const_mul ε
      have h2 := ((((hasDerivAt_id y).sub_const a).mul_const M |>.const_mul 1).mul
        ((hasDerivAt_id y).const_sub b)).mul_const ((b - a) / 2)
      convert h1.sub h2 using 1
      · funext z; simp only [hψ, id, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; ring
      · simp only [hψ', id]; ring
    have hd2 : ∀ y ∈ Icc a b, HasDerivAt ψ' (ψ'' y) y := by
      intro y hy
      have h1 := ((((hg' y hy).const_mul (b - a)).add_const (g a)).sub_const (g b)).const_mul ε
      have h2 := (((hasDerivAt_id y).const_mul 2).const_sub (a + b)).const_mul (M * (b - a) / 2)
      convert h1.sub h2 using 1
      · funext z; simp only [hψ', id, Pi.sub_apply]; ring
      · simp only [hψ'']; ring
    have hconv : ConvexOn ℝ (Icc a b) ψ := by
      refine convexOn_of_hasDerivWithinAt2_nonneg (f' := ψ') (f'' := ψ'') (convex_Icc a b) ?_ ?_ ?_
          ?_
      · exact fun y hy => (hd1 y hy).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact (hd1 y (Ioo_subset_Icc_self hy)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact (hd2 y (Ioo_subset_Icc_self hy)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hb := hM y (Ioo_subset_Icc_self hy)
        have hba : 0 < b - a := by linarith
        simp only [hψ'']
        have : -(M * (b - a)) ≤ ε * ((b - a) * g'' y) := by
          have habs := abs_le.mp hb
          rcases hε with rfl | rfl
          · nlinarith
          · nlinarith
        linarith
    have hseg : x ∈ segment ℝ a b := by rw [segment_eq_Icc hab]; exact hx
    have hle := hconv.le_on_segment (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hseg
    have ha : ψ a = 0 := by simp only [hψ]; ring
    have hb' : ψ b = 0 := by simp only [hψ]; ring
    rw [ha, hb', max_self] at hle
    simp only [hψ] at hle
    linarith
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-! ## The scalar kernel along a curve -/

/-- The scalar kernel `⟨m, u⟩/|u|³`. -/
@[expose] def kg (m u : Space) : ℝ := ⟪m, u⟫ * (‖u‖ ^ 3)⁻¹

/-- First derivative of the kernel along a curve with velocity `u₁`. -/
@[expose] def kg1 (m u u1 : Space) : ℝ :=
  ⟪m, u1⟫ * (‖u‖ ^ 3)⁻¹ - 3 * ⟪m, u⟫ * ⟪u, u1⟫ * (‖u‖ ^ 5)⁻¹

/-- Second derivative of the kernel along a curve with velocity `u₁` and acceleration `u₂`. -/
@[expose] def kg2 (m u u1 u2 : Space) : ℝ :=
  ⟪m, u2⟫ * (‖u‖ ^ 3)⁻¹ - 6 * ⟪m, u1⟫ * ⟪u, u1⟫ * (‖u‖ ^ 5)⁻¹ -
    3 * ⟪m, u⟫ * (‖u1‖ ^ 2 + ⟪u, u2⟫) * (‖u‖ ^ 5)⁻¹ + 15 * ⟪m, u⟫ * ⟪u, u1⟫ ^ 2 * (‖u‖ ^ 7)⁻¹

/-- Derivative of `|u(τ)|`. -/
theorem hasDerivAt_norm_curve {u : ℝ → Space} {u1 : Space} {τ : ℝ} (hu : HasDerivAt u u1 τ)
    (h0 : u τ ≠ 0) : HasDerivAt (fun s => ‖u s‖) (⟪u τ, u1⟫ / ‖u τ‖) τ := by
  have hsq := hu.norm_sq
  have hpos : 0 < ‖u τ‖ ^ 2 := by positivity
  have hs := hsq.sqrt hpos.ne'
  have e : (fun s => Real.sqrt (‖u s‖ ^ 2)) = fun s => ‖u s‖ :=
    funext fun s => Real.sqrt_sq (norm_nonneg _)
  rw [e, Real.sqrt_sq (norm_nonneg _)] at hs
  convert hs using 1
  field_simp

/-- Derivative of `|u(τ)|^{-(j+1)}`. -/
theorem hasDerivAt_norm_inv_pow {u : ℝ → Space} {u1 : Space} {τ : ℝ} (hu : HasDerivAt u u1 τ)
    (h0 : u τ ≠ 0) (j : ℕ) :
    HasDerivAt (fun s => (‖u s‖ ^ (j + 1))⁻¹)
      (-((j : ℝ) + 1) * ⟪u τ, u1⟫ * (‖u τ‖ ^ (j + 3))⁻¹) τ := by
  have hn := hasDerivAt_norm_curve hu h0
  have hpos : 0 < ‖u τ‖ := norm_pos_iff.mpr h0
  have h := (hn.pow (j + 1)).inv (pow_ne_zero _ hpos.ne')
  convert h using 1
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- **First derivative of the kernel** along a `C¹` curve. -/
theorem hasDerivAt_kg (m : Space) {u : ℝ → Space} {u1 : Space} {τ : ℝ} (hu : HasDerivAt u u1 τ)
    (h0 : u τ ≠ 0) : HasDerivAt (fun s => kg m (u s)) (kg1 m (u τ) u1) τ := by
  have hA : HasDerivAt (fun s => ⟪m, u s⟫) ⟪m, u1⟫ τ := by
    simpa using (hasDerivAt_const τ m).inner ℝ hu
  have h := hA.mul (hasDerivAt_norm_inv_pow hu h0 2)
  unfold kg kg1
  convert h using 1
  push_cast; ring

/-- **Second derivative of the kernel** along a `C²` curve. -/
theorem hasDerivAt_kg1 (m : Space) {u u1 : ℝ → Space} {u2 : Space} {τ : ℝ}
    (hu : HasDerivAt u (u1 τ) τ) (hu1 : HasDerivAt u1 u2 τ) (h0 : u τ ≠ 0) :
    HasDerivAt (fun s => kg1 m (u s) (u1 s)) (kg2 m (u τ) (u1 τ) u2) τ := by
  have hA1 : HasDerivAt (fun s => ⟪m, u1 s⟫) ⟪m, u2⟫ τ := by
    simpa using (hasDerivAt_const τ m).inner ℝ hu1
  have hA : HasDerivAt (fun s => ⟪m, u s⟫) ⟪m, u1 τ⟫ τ := by
    simpa using (hasDerivAt_const τ m).inner ℝ hu
  have hC : HasDerivAt (fun s => ⟪u s, u1 s⟫) (⟪u τ, u2⟫ + ⟪u1 τ, u1 τ⟫) τ := hu.inner ℝ hu1
  have h3 := hasDerivAt_norm_inv_pow hu h0 2
  have h5 := hasDerivAt_norm_inv_pow hu h0 4
  have h := (hA1.mul h3).sub (((hA.const_mul 3).mul hC).mul h5)
  unfold kg1 kg2
  convert h using 1
  simp only [Pi.mul_apply]
  rw [real_inner_self_eq_norm_sq]
  have hpos : 0 < ‖u τ‖ := norm_pos_iff.mpr h0
  push_cast
  field_simp
  ring

/-- `|αx + βy|² = α²|x|² + 2αβ⟨x, y⟩ + β²|y|²`. -/
theorem norm_comb_sq (α β : ℝ) (x y : Space) :
    ‖α • x + β • y‖ ^ 2 = α ^ 2 * ‖x‖ ^ 2 + 2 * α * β * ⟪x, y⟫ + β ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  simp; ring

/-- **Sharp bound on the second derivative of the kernel**. -/
theorem abs_kg2_le (m u u1 u2 : Space) (h0 : u ≠ 0) :
    |kg2 m u u1 u2| ≤ ‖m‖ * (6 * ‖u1‖ ^ 2 / ‖u‖ ^ 4 + 2 * ‖u2‖ / ‖u‖ ^ 3) := by
  set s := ‖u‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr h0
  set c1 := ⟪u, u1⟫
  set c2 := ⟪u, u2⟫
  set e := ‖u1‖
  -- the two vectors
  set W1 : Space := (-6 * c1 / s ^ 5) • u1 + (15 * c1 ^ 2 / s ^ 7 - 3 * e ^ 2 / s ^ 5) • u
  set W2 : Space := (1 / s ^ 3) • u2 + (-3 * c2 / s ^ 5) • u
  have hW : kg2 m u u1 u2 = ⟪m, W1 + W2⟫ := by
    simp only [W1, W2, kg2, inner_add_right, inner_smul_right]
    rw [← hs]
    field_simp
    ring
  have hu2 : ‖u‖ ^ 2 = s ^ 2 := by rw [hs]
  have hcs1 : c1 ^ 2 ≤ s ^ 2 * e ^ 2 := by
    have := abs_real_inner_le_norm u u1
    have h2 := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    simpa [mul_pow] using h2
  have hcs2 : c2 ^ 2 ≤ s ^ 2 * ‖u2‖ ^ 2 := by
    have := abs_real_inner_le_norm u u2
    have h2 := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    simpa [mul_pow] using h2
  have hW1 : ‖W1‖ ≤ 6 * e ^ 2 / s ^ 4 := by
    have hsq : ‖W1‖ ^ 2 = (-6 * c1 / s ^ 5) ^ 2 * e ^ 2 +
        2 * (-6 * c1 / s ^ 5) * (15 * c1 ^ 2 / s ^ 7 - 3 * e ^ 2 / s ^ 5) * c1 +
        (15 * c1 ^ 2 / s ^ 7 - 3 * e ^ 2 / s ^ 5) ^ 2 * s ^ 2 := by
      simp only [W1]; rw [norm_comb_sq, real_inner_comm]
    have key : (6 * e ^ 2 / s ^ 4) ^ 2 - ‖W1‖ ^ 2 =
        9 * (5 * c1 ^ 2 + 3 * s ^ 2 * e ^ 2) * (s ^ 2 * e ^ 2 - c1 ^ 2) / s ^ 12 := by
      rw [hsq]; field_simp; ring
    have hnn : 0 ≤ (6 * e ^ 2 / s ^ 4) ^ 2 - ‖W1‖ ^ 2 := by
      rw [key]
      apply div_nonneg _ (by positivity)
      have : 0 ≤ s ^ 2 * e ^ 2 - c1 ^ 2 := by linarith
      positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (by linarith)
  have hW2 : ‖W2‖ ≤ 2 * ‖u2‖ / s ^ 3 := by
    have hsq : ‖W2‖ ^ 2 = (1 / s ^ 3) ^ 2 * ‖u2‖ ^ 2 + 2 * (1 / s ^ 3) * (-3 * c2 / s ^ 5) * c2 +
        (-3 * c2 / s ^ 5) ^ 2 * s ^ 2 := by
      simp only [W2]; rw [norm_comb_sq, real_inner_comm]
    have key : (2 * ‖u2‖ / s ^ 3) ^ 2 - ‖W2‖ ^ 2 = 3 * (s ^ 2 * ‖u2‖ ^ 2 - c2 ^ 2) / s ^ 8 := by
      rw [hsq]; field_simp; ring
    have hnn : 0 ≤ (2 * ‖u2‖ / s ^ 3) ^ 2 - ‖W2‖ ^ 2 := by
      rw [key]; apply div_nonneg _ (by positivity); linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (by linarith)
  rw [hW]
  calc |⟪m, W1 + W2⟫| ≤ ‖m‖ * ‖W1 + W2‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖m‖ * (‖W1‖ + ‖W2‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖m‖ * (6 * e ^ 2 / s ^ 4 + 2 * ‖u2‖ / s ^ 3) :=
        mul_le_mul_of_nonneg_left (add_le_add hW1 hW2) (norm_nonneg _)

/-- The triple product `⟨n, v × w⟩ = ⟨n × v, w⟩`. -/
theorem inner_cross (n v w : Space) : ⟪n, cross v w⟫ = ⟪cross n v, w⟫ := by
  simp only [cross, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  simp [crossProduct]
  ring

/-- The segment kernel paired with `n` is the scalar kernel with `m = n × (q - p)`. -/
theorem inner_seg_kernel (n p q y : Space) (t : ℝ) :
    ⟪n, filamentKernel (seg p q) t y⟫ = kg (cross n (q - p)) (y - seg p q t) := by
  unfold filamentKernel kg
  rw [deriv_seg, inner_smul_right, inner_cross]
  ring

/-! ## Segment fields along curves -/

/-- **Interpolation bound for the field of a segment along a curve.** -/
theorem segField_interp_bound (μ₀ I : ℝ) (p q n : Space) {σ σ1 σ2 : ℝ → Space} {a b x d S1 S2 : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (hd : 0 < d)
    (hσ : ∀ τ ∈ Icc a b, HasDerivAt σ (σ1 τ) τ) (hσ1 : ∀ τ ∈ Icc a b, HasDerivAt σ1 (σ2 τ) τ)
    (hS1 : ∀ τ ∈ Icc a b, ‖σ1 τ‖ ≤ S1) (hS2 : ∀ τ ∈ Icc a b, ‖σ2 τ‖ ≤ S2)
    (hsep : ∀ τ ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖σ τ - seg p q t‖) :
    |(b - a) * ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ x)⟫ -
        ((b - x) * ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ a)⟫ +
          (x - a) * ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ b)⟫)| ≤
      |μ₀ * I / (4 * Real.pi)| * (‖n‖ * ‖q - p‖ * (6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^ 3)) *
        (x - a) * (b - x) * (b - a) / 2 := by
  set κ := μ₀ * I / (4 * Real.pi)
  set m := cross n (q - p)
  have hm : ‖m‖ ≤ ‖n‖ * ‖q - p‖ := norm_cross_le _ _
  set M := ‖n‖ * ‖q - p‖ * (6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^ 3)
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  -- continuity of the scalar kernel in `t` at separated points
  have hcont : ∀ y : Space, (∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖y - seg p q t‖) →
      ContinuousOn (fun t => kg m (y - seg p q t)) (Icc 0 1) := by
    intro y hy
    unfold kg
    have hc : Continuous (fun t => y - seg p q t) := continuous_const.sub (continuous_seg p q)
    refine (continuous_const.inner hc).continuousOn.mul ?_
    refine (hc.norm.pow 3).continuousOn.inv₀ fun t ht => ?_
    exact pow_ne_zero _ (lt_of_lt_of_le hd (hy t ht)).ne'
  -- the field paired with `n` as an integral of the scalar kernel
  have hF : ∀ y : Space, (∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖y - seg p q t‖) →
      ⟪n, filamentField μ₀ I (seg p q) 0 1 y⟫ = κ * ∫ t in (0 : ℝ)..1, kg m (y - seg p q t) := by
    intro y hy
    unfold filamentField
    have hdc : deriv (seg p q) = fun _ => q - p := funext (deriv_seg p q)
    have hint : IntervalIntegrable (fun t => filamentKernel (seg p q) t y) MeasureTheory.volume 0 1
        := by
      refine (filamentKernel_continuousOn (seg p q) y (uIcc 0 1) (continuous_seg p q).continuousOn
        (by rw [hdc]; exact continuousOn_const) fun t ht => ?_).intervalIntegrable
      rw [uIcc_of_le h01] at ht
      exact norm_pos_iff.mp (lt_of_lt_of_le hd (hy t ht))
    have hcomm := (innerSL ℝ n).intervalIntegral_comp_comm hint
    simp only [innerSL_apply_apply] at hcomm
    rw [inner_smul_right, ← hcomm]
    simp_rw [inner_seg_kernel]
    rfl
  have hxa := hsep a (left_mem_Icc.mpr hab)
  have hxb := hsep b (right_mem_Icc.mpr hab)
  have hxx := hsep x hx
  rw [hF _ hxa, hF _ hxb, hF _ hxx]
  have hI : ∀ y : Space, (∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖y - seg p q t‖) →
      IntervalIntegrable (fun t => kg m (y - seg p q t)) MeasureTheory.volume 0 1 := by
    intro y hy
    have : ContinuousOn (fun t => kg m (y - seg p q t)) (uIcc 0 1) := by
      rw [uIcc_of_le h01]; exact hcont y hy
    exact this.intervalIntegrable
  have hcomb : (b - a) * (κ * ∫ t in (0 : ℝ)..1, kg m (σ x - seg p q t)) -
      ((b - x) * (κ * ∫ t in (0 : ℝ)..1, kg m (σ a - seg p q t)) +
        (x - a) * (κ * ∫ t in (0 : ℝ)..1, kg m (σ b - seg p q t))) =
      κ * ∫ t in (0 : ℝ)..1, ((b - a) * kg m (σ x - seg p q t) -
        ((b - x) * kg m (σ a - seg p q t) + (x - a) * kg m (σ b - seg p q t))) := by
    rw [intervalIntegral.integral_sub ((hI _ hxx).const_mul _)
        (((hI _ hxa).const_mul _).add ((hI _ hxb).const_mul _)),
      intervalIntegral.integral_add ((hI _ hxa).const_mul _) ((hI _ hxb).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  rw [hcomb, abs_mul]
  -- pointwise bound
  have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖(b - a) * kg m (σ x - seg p q t) -
        ((b - x) * kg m (σ a - seg p q t) + (x - a) * kg m (σ b - seg p q t))‖ ≤
      M * (x - a) * (b - x) * (b - a) / 2 := by
    intro t ht
    rw [uIoc_of_le h01] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs]
    have hne : ∀ τ ∈ Icc a b, σ τ - seg p q t ≠ 0 := fun τ hτ =>
      norm_pos_iff.mp (lt_of_lt_of_le hd (hsep τ hτ t ht'))
    refine lin_interp_bound (g := fun τ => kg m (σ τ - seg p q t))
      (g' := fun τ => kg1 m (σ τ - seg p q t) (σ1 τ))
      (g'' := fun τ => kg2 m (σ τ - seg p q t) (σ1 τ) (σ2 τ)) hab hx ?_ ?_ ?_
    · intro τ hτ
      exact hasDerivAt_kg m ((hσ τ hτ).sub_const _) (hne τ hτ)
    · intro τ hτ
      exact hasDerivAt_kg1 m (u := fun s => σ s - seg p q t) ((hσ τ hτ).sub_const _)
        (hσ1 τ hτ) (hne τ hτ)
    · intro τ hτ
      have hb := abs_kg2_le m (σ τ - seg p q t) (σ1 τ) (σ2 τ) (hne τ hτ)
      have hdτ := hsep τ hτ t ht'
      have h4 : 6 * ‖σ1 τ‖ ^ 2 / ‖σ τ - seg p q t‖ ^ 4 ≤ 6 * S1 ^ 2 / d ^ 4 := by
        apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_left₀ hd.le hdτ 4)
        have := hS1 τ hτ
        have h0 := norm_nonneg (σ1 τ)
        nlinarith
      have h3 : 2 * ‖σ2 τ‖ / ‖σ τ - seg p q t‖ ^ 3 ≤ 2 * S2 / d ^ 3 := by
        apply div_le_div₀ (by linarith [norm_nonneg (σ2 τ), hS2 τ hτ]) _ (by positivity)
          (pow_le_pow_left₀ hd.le hdτ 3)
        linarith [hS2 τ hτ]
      calc |kg2 m (σ τ - seg p q t) (σ1 τ) (σ2 τ)|
          ≤ ‖m‖ * (6 * ‖σ1 τ‖ ^ 2 / ‖σ τ - seg p q t‖ ^ 4 + 2 * ‖σ2 τ‖ / ‖σ τ - seg p q t‖ ^ 3) :=
            hb
        _ ≤ (‖n‖ * ‖q - p‖) * (6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^ 3) :=
            mul_le_mul hm (add_le_add h4 h3) (by positivity) (by positivity)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  calc |κ| * |∫ t in (0 : ℝ)..1, ((b - a) * kg m (σ x - seg p q t) -
        ((b - x) * kg m (σ a - seg p q t) + (x - a) * kg m (σ b - seg p q t)))|
      ≤ |κ| * (M * (x - a) * (b - x) * (b - a) / 2) :=
        mul_le_mul_of_nonneg_left hint (abs_nonneg _)
    _ = |κ| * M * (x - a) * (b - x) * (b - a) / 2 := by ring

/-! ## Cells -/

/-- One-dimensional interpolation step: from the multiplied interpolation bound and bounds at
the endpoints, `|Φ(x)| ≤ e + M(b - a)²/8`. -/
theorem interp_abs_le {Φa Φb Φx a b x M e : ℝ} (h : a < b) (hx : x ∈ Icc a b)
    (hmul : |(b - a) * Φx - ((b - x) * Φa + (x - a) * Φb)| ≤ M * (x - a) * (b - x) * (b - a) / 2)
    (ha : |Φa| ≤ e) (hb : |Φb| ≤ e) (hM : 0 ≤ M) : |Φx| ≤ e + M * (b - a) ^ 2 / 8 := by
  have hba : 0 < b - a := by linarith
  have hxa : 0 ≤ x - a := by linarith [hx.1]
  have hbx : 0 ≤ b - x := by linarith [hx.2]
  have hL : |(b - x) * Φa + (x - a) * Φb| ≤ (b - a) * e := by
    calc |(b - x) * Φa + (x - a) * Φb| ≤ |(b - x) * Φa| + |(x - a) * Φb| := abs_add_le _ _
      _ = (b - x) * |Φa| + (x - a) * |Φb| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hbx, abs_of_nonneg hxa]
      _ ≤ (b - x) * e + (x - a) * e :=
          add_le_add (mul_le_mul_of_nonneg_left ha hbx) (mul_le_mul_of_nonneg_left hb hxa)
      _ = (b - a) * e := by ring
  have hq : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have h1 : (b - a) * |Φx| ≤ (b - a) * e + M * (x - a) * (b - x) * (b - a) / 2 := by
    have := abs_sub_abs_le_abs_sub ((b - a) * Φx) ((b - x) * Φa + (x - a) * Φb)
    rw [abs_mul, abs_of_pos hba] at this
    linarith
  have h2 : M * (x - a) * (b - x) * (b - a) / 2 ≤ (b - a) * (M * (b - a) ^ 2 / 8) := by
    have := mul_le_mul_of_nonneg_left hq hM
    nlinarith
  have h3 : (b - a) * |Φx| ≤ (b - a) * (e + M * (b - a) ^ 2 / 8) := by nlinarith
  exact le_of_mul_le_mul_left h3 hba

/-- **Bilinear cell bound.** If `Φ` is bounded by `e` at the four corners of
`[φ₀, φ₁] × [w₀, w₁]`, satisfies the one-dimensional interpolation bound with constant `Mφ` along
`φ` (at every `w`) and with constant `Mw` along `w` at `φ₀` and `φ₁`, then
`|Φ| ≤ e + Mφ Δφ²/8 + Mw Δw²/8` on the whole cell. -/
theorem bilinear_cell_bound {Φ : ℝ → ℝ → ℝ} {φ0 φ1 w0 w1 Mφ Mw e : ℝ} (hφ : φ0 < φ1)
    (hw : w0 < w1) (hMφ : 0 ≤ Mφ) (hMw : 0 ≤ Mw)
    (h00 : |Φ φ0 w0| ≤ e) (h10 : |Φ φ1 w0| ≤ e) (h01 : |Φ φ0 w1| ≤ e) (h11 : |Φ φ1 w1| ≤ e)
    (hφi : ∀ w ∈ Icc w0 w1, ∀ φ ∈ Icc φ0 φ1,
      |(φ1 - φ0) * Φ φ w - ((φ1 - φ) * Φ φ0 w + (φ - φ0) * Φ φ1 w)| ≤
        Mφ * (φ - φ0) * (φ1 - φ) * (φ1 - φ0) / 2)
    (hwi : ∀ φ, (φ = φ0 ∨ φ = φ1) → ∀ w ∈ Icc w0 w1,
      |(w1 - w0) * Φ φ w - ((w1 - w) * Φ φ w0 + (w - w0) * Φ φ w1)| ≤
        Mw * (w - w0) * (w1 - w) * (w1 - w0) / 2)
    {φ w : ℝ} (hφm : φ ∈ Icc φ0 φ1) (hwm : w ∈ Icc w0 w1) :
    |Φ φ w| ≤ e + Mφ * (φ1 - φ0) ^ 2 / 8 + Mw * (w1 - w0) ^ 2 / 8 := by
  have e0 := interp_abs_le hw hwm (hwi φ0 (Or.inl rfl) w hwm) h00 h01 hMw
  have e1 := interp_abs_le hw hwm (hwi φ1 (Or.inr rfl) w hwm) h10 h11 hMw
  have := interp_abs_le hφ hφm (hφi w hwm φ hφm) e0 e1 hMφ
  linarith

end PlasmaLean.Design.PolygonCoil
