/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Cubic (four-point) interpolation: remainder, Lebesgue bound, tensor-product cells

The higher-order frontier certificate (`Design/PolygonCoilCubic*`) bounds a function on a grid
cell `[x₁, x₂] × [y₁, y₂]` from its values on the `4 × 4` stencil `x₀ < x₁ < x₂ < x₃`,
`y₀ < y₁ < y₂ < y₃` and bounds on fourth derivatives along the two grid directions.

* `rolle_four`: a `C⁴` function with five ordered zeros has a zero of its fourth derivative
  (Rolle's theorem four times).
* `newt v y` (**Newton form** of the cubic interpolant with node order `x₁, x₂, x₀, x₃`) and
  `newt_interp_bound` (**remainder**): if `|g⁗| ≤ M` on `[x₀, x₃]` then for `y ∈ [x₁, x₂]`
  `|g(y) - newt g(y)| ≤ M |ω(y)|/24`, `ω(y) = (y - x₀)(y - x₁)(y - x₂)(y - x₃)`; and
  `abs_omega_le`: `|ω| ≤ (x₂ - x₁)²(x₂ - x₀)(x₃ - x₁)/4` on `[x₁, x₂]`.
* `newt_lagrange`, `abs_newt_le` (**Lebesgue bound**): on `[x₁, x₂]` the inner basis functions
  are `≥ 0`, the outer ones `≤ 0`, so `|newt v| ≤ (1 + 2(B₀ + B₃)) max |vᵢ|` with explicit
  bounds `B₀`, `B₃` of the outer basis functions.
* `newt_split`: `newt v y = (1 - θ)v₁ + θv₂ + c₂(y) dd₂ + c₃(y) dd₃` with the divided
  differences `dd₂ = v[x₀, x₁, x₂]`, `dd₃ = v[x₀, …, x₃]`, `|c₂| ≤ (x₂ - x₁)²/4`,
  `|c₃| ≤ (x₂ - x₁)²(x₂ - x₀)/4`.
* `tensor_bound` (**tensor-product cell bound**): the value of the bicubic interpolant on the
  middle cell is at most the largest of the four middle values, plus the divided-difference
  corrections in each direction.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open Set

/-! ## Rolle's theorem four times -/

/-- One Rolle step on a subinterval of the domain of differentiability. -/
theorem rolle_step {f f' : ℝ → ℝ} {A B a b : ℝ} (hA : A ≤ a) (hab : a < b) (hB : b ≤ B)
    (hf : ∀ y ∈ Icc A B, HasDerivAt f (f' y) y) (ha : f a = 0) (hb : f b = 0) :
    ∃ c ∈ Ioo a b, f' c = 0 := by
  have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc hA hB
  refine exists_hasDerivAt_eq_zero hab ?_ (by rw [ha, hb]) fun y hy => hf y (hsub
      (Ioo_subset_Icc_self hy))
  exact fun y hy => (hf y (hsub hy)).continuousAt.continuousWithinAt

/-- **Rolle's theorem, four times**: a function with four derivatives on `[p₀, p₄]` vanishing at
`p₀ < p₁ < p₂ < p₃ < p₄` has a zero of its fourth derivative in `[p₀, p₄]`. -/
theorem rolle_four {f f1 f2 f3 f4 : ℝ → ℝ} {p0 p1 p2 p3 p4 : ℝ} (h01 : p0 < p1) (h12 : p1 < p2)
    (h23 : p2 < p3) (h34 : p3 < p4)
    (hf : ∀ y ∈ Icc p0 p4, HasDerivAt f (f1 y) y) (hf1 : ∀ y ∈ Icc p0 p4, HasDerivAt f1 (f2 y) y)
    (hf2 : ∀ y ∈ Icc p0 p4, HasDerivAt f2 (f3 y) y) (hf3 : ∀ y ∈ Icc p0 p4, HasDerivAt f3 (f4 y) y)
    (z0 : f p0 = 0) (z1 : f p1 = 0) (z2 : f p2 = 0) (z3 : f p3 = 0) (z4 : f p4 = 0) :
    ∃ ζ ∈ Icc p0 p4, f4 ζ = 0 := by
  obtain ⟨a0, ha0, ea0⟩ := rolle_step le_rfl h01 (by linarith) hf z0 z1
  obtain ⟨a1, ha1, ea1⟩ := rolle_step h01.le h12 (by linarith) hf z1 z2
  obtain ⟨a2, ha2, ea2⟩ := rolle_step (by linarith) h23 (by linarith) hf z2 z3
  obtain ⟨a3, ha3, ea3⟩ := rolle_step (by linarith) h34 le_rfl hf z3 z4
  obtain ⟨b0, hb0, eb0⟩ := rolle_step (by linarith [ha0.1]) (by linarith [ha0.2, ha1.1])
    (by linarith [ha1.2]) hf1 ea0 ea1
  obtain ⟨b1, hb1, eb1⟩ := rolle_step (by linarith [ha1.1]) (by linarith [ha1.2, ha2.1])
    (by linarith [ha2.2]) hf1 ea1 ea2
  obtain ⟨b2, hb2, eb2⟩ := rolle_step (by linarith [ha2.1]) (by linarith [ha2.2, ha3.1])
    (by linarith [ha3.2]) hf1 ea2 ea3
  obtain ⟨c0, hc0, ec0⟩ := rolle_step (by linarith [hb0.1, ha0.1]) (by linarith [hb0.2, hb1.1])
    (by linarith [hb1.2, ha2.2]) hf2 eb0 eb1
  obtain ⟨c1, hc1, ec1⟩ := rolle_step (by linarith [hb1.1, ha1.1]) (by linarith [hb1.2, hb2.1])
    (by linarith [hb2.2, ha3.2]) hf2 eb1 eb2
  obtain ⟨ζ, hζ, eζ⟩ := rolle_step (by linarith [hc0.1, hb0.1, ha0.1])
    (by linarith [hc0.2, hc1.1]) (by linarith [hc1.2, hb2.2, ha3.2]) hf3 ec0 ec1
  refine ⟨ζ, ⟨?_, ?_⟩, eζ⟩
  · linarith [hζ.1, hc0.1, hb0.1, ha0.1]
  · linarith [hζ.2, hc1.2, hb2.2, ha3.2]

/-! ## The Newton form of the cubic interpolant -/

/-- Second divided difference `v[x₀, x₁, x₂]`. -/
@[expose] def dd2 (x0 x1 x2 v0 v1 v2 : ℝ) : ℝ :=
  ((v2 - v1) / (x2 - x1) - (v1 - v0) / (x1 - x0)) / (x2 - x0)

/-- Third divided difference `v[x₀, x₁, x₂, x₃]`. -/
@[expose] def dd3 (x0 x1 x2 x3 v0 v1 v2 v3 : ℝ) : ℝ :=
  (dd2 x1 x2 x3 v1 v2 v3 - dd2 x0 x1 x2 v0 v1 v2) / (x3 - x0)

/-- The cubic interpolant of `v₀, …, v₃` at `x₀, …, x₃` in Newton form (nodes in the order
`x₁, x₂, x₀, x₃`), evaluated at `y`. -/
@[expose] def newt (x0 x1 x2 x3 v0 v1 v2 v3 y : ℝ) : ℝ :=
  v1 + (v2 - v1) / (x2 - x1) * (y - x1) + dd2 x0 x1 x2 v0 v1 v2 * ((y - x1) * (y - x2)) +
    dd3 x0 x1 x2 x3 v0 v1 v2 v3 * ((y - x1) * (y - x2) * (y - x0))

/-- The node polynomial `ω(y) = (y - x₀)(y - x₁)(y - x₂)(y - x₃)`. -/
@[expose] def omega4 (x0 x1 x2 x3 y : ℝ) : ℝ := (y - x0) * (y - x1) * (y - x2) * (y - x3)

/-- The Newton form interpolates. -/
theorem newt_nodes {x0 x1 x2 x3 : ℝ} (h01 : x0 < x1) (h12 : x1 < x2) (h23 : x2 < x3)
    (v0 v1 v2 v3 : ℝ) :
    newt x0 x1 x2 x3 v0 v1 v2 v3 x0 = v0 ∧ newt x0 x1 x2 x3 v0 v1 v2 v3 x1 = v1 ∧
      newt x0 x1 x2 x3 v0 v1 v2 v3 x2 = v2 ∧ newt x0 x1 x2 x3 v0 v1 v2 v3 x3 = v3 := by
  have a : x1 - x0 ≠ 0 := by linarith
  have b : x2 - x1 ≠ 0 := by linarith
  have c : x2 - x0 ≠ 0 := by linarith
  have d : x3 - x2 ≠ 0 := by linarith
  have e : x3 - x1 ≠ 0 := by linarith
  have f : x3 - x0 ≠ 0 := by linarith
  unfold newt dd3 dd2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Derivative of a quartic polynomial in monomial form. -/
theorem hasDerivAt_quartic (a0 a1 a2 a3 a4 y : ℝ) :
    HasDerivAt (fun y => a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4)
      (a1 + 2 * a2 * y + 3 * a3 * y ^ 2 + 4 * a4 * y ^ 3) y := by
  have h0 := hasDerivAt_const y a0
  have h1 := (hasDerivAt_id' y).const_mul a1
  have h2 := (hasDerivAt_pow 2 y).const_mul a2
  have h3 := (hasDerivAt_pow 3 y).const_mul a3
  have h4 := (hasDerivAt_pow 4 y).const_mul a4
  have := HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add h0 h1) h2)
    h3) h4
  exact this.congr_deriv (by push_cast; ring)

/-- **Remainder of cubic interpolation.** If `g` has four derivatives on `[x₀, x₃]` with
`|g⁗| ≤ M`, then on `[x₁, x₂]`, `|g(y) - newt g(y)| ≤ M|ω(y)|/24`. -/
theorem newt_interp_bound {g g1 g2 g3 g4 : ℝ → ℝ} {x0 x1 x2 x3 M y : ℝ} (h01 : x0 < x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (hy : y ∈ Icc x1 x2)
    (hg : ∀ z ∈ Icc x0 x3, HasDerivAt g (g1 z) z) (hg1 : ∀ z ∈ Icc x0 x3, HasDerivAt g1 (g2 z) z)
    (hg2 : ∀ z ∈ Icc x0 x3, HasDerivAt g2 (g3 z) z) (hg3 : ∀ z ∈ Icc x0 x3, HasDerivAt g3 (g4 z) z)
    (hM : ∀ z ∈ Icc x0 x3, |g4 z| ≤ M) :
    |g y - newt x0 x1 x2 x3 (g x0) (g x1) (g x2) (g x3) y| ≤ M * |omega4 x0 x1 x2 x3 y| / 24 := by
  obtain ⟨n0, n1, n2, n3⟩ := newt_nodes h01 h12 h23 (g x0) (g x1) (g x2) (g x3)
  rcases eq_or_lt_of_le hy.1 with hy1 | hy1
  · subst hy1; rw [n1]; simp only [sub_self, abs_zero, omega4]; simp
  rcases eq_or_lt_of_le hy.2 with hy2 | hy2
  · subst hy2; rw [n2]; simp only [sub_self, abs_zero, omega4]; simp
  have hω : omega4 x0 x1 x2 x3 y ≠ 0 := by
    unfold omega4
    have : 0 < (y - x0) * (y - x1) * (x2 - y) * (x3 - y) := by
      apply mul_pos (mul_pos (mul_pos _ _) _) _ <;> linarith
    intro h; nlinarith
  set N := newt x0 x1 x2 x3 (g x0) (g x1) (g x2) (g x3)
  set K := (g y - N y) / omega4 x0 x1 x2 x3 y
  set d1 := (g x2 - g x1) / (x2 - x1)
  set d2 := dd2 x0 x1 x2 (g x0) (g x1) (g x2)
  set d3 := dd3 x0 x1 x2 x3 (g x0) (g x1) (g x2) (g x3)
  set s1 := x0 + x1 + x2 + x3
  set s2 := x0 * x1 + x0 * x2 + x0 * x3 + x1 * x2 + x1 * x3 + x2 * x3
  set s3 := x0 * x1 * x2 + x0 * x1 * x3 + x0 * x2 * x3 + x1 * x2 * x3
  set s4 := x0 * x1 * x2 * x3
  set Q4 := K
  set Q3 := d3 - K * s1
  set Q2 := d2 - d3 * (x0 + x1 + x2) + K * s2
  set Q1 := d1 - d2 * (x1 + x2) + d3 * (x0 * x1 + x0 * x2 + x1 * x2) - K * s3
  set Q0 := g x1 - d1 * x1 + d2 * x1 * x2 - d3 * x0 * x1 * x2 + K * s4
  have hQ : ∀ z, N z + K * omega4 x0 x1 x2 x3 z = Q0 + Q1 * z + Q2 * z ^ 2 + Q3 * z ^ 3 + Q4 * z ^
      4 := by
    intro z; simp only [N, newt, omega4, Q0, Q1, Q2, Q3, Q4, s1, s2, s3, s4, d1, d2, d3]; ring
  -- the auxiliary function and its derivatives
  set φ : ℝ → ℝ := fun z => g z - (Q0 + Q1 * z + Q2 * z ^ 2 + Q3 * z ^ 3 + Q4 * z ^ 4)
  set φ1 : ℝ → ℝ := fun z => g1 z - (Q1 + 2 * Q2 * z + 3 * Q3 * z ^ 2 + 4 * Q4 * z ^ 3)
  set φ2 : ℝ → ℝ := fun z => g2 z - (2 * Q2 + 2 * (3 * Q3) * z + 3 * (4 * Q4) * z ^ 2 + 4 * 0 * z ^
      3)
  set φ3 : ℝ → ℝ := fun z => g3 z - (2 * (3 * Q3) + 2 * (3 * (4 * Q4)) * z + 3 * 0 * z ^ 2 +
    4 * 0 * z ^ 3)
  set φ4 : ℝ → ℝ := fun z => g4 z - (2 * (3 * (4 * Q4)) + 2 * 0 * z + 3 * 0 * z ^ 2 + 4 * 0 * z ^ 3)
  have d1' : ∀ z ∈ Icc x0 x3, HasDerivAt φ (φ1 z) z := fun z hz =>
    HasDerivAt.fun_sub (hg z hz) (hasDerivAt_quartic Q0 Q1 Q2 Q3 Q4 z)
  have d2' : ∀ z ∈ Icc x0 x3, HasDerivAt φ1 (φ2 z) z := by
    intro z hz
    have h := hasDerivAt_quartic Q1 (2 * Q2) (3 * Q3) (4 * Q4) 0 z
    have e : (fun z => Q1 + 2 * Q2 * z + 3 * Q3 * z ^ 2 + 4 * Q4 * z ^ 3) =
        (fun z => Q1 + 2 * Q2 * z + 3 * Q3 * z ^ 2 + 4 * Q4 * z ^ 3 + 0 * z ^ 4) := by
      funext z; ring
    rw [← e] at h
    exact HasDerivAt.fun_sub (hg1 z hz) h
  have d3' : ∀ z ∈ Icc x0 x3, HasDerivAt φ2 (φ3 z) z := by
    intro z hz
    have h := hasDerivAt_quartic (2 * Q2) (2 * (3 * Q3)) (3 * (4 * Q4)) (4 * 0) 0 z
    have e : (fun z => 2 * Q2 + 2 * (3 * Q3) * z + 3 * (4 * Q4) * z ^ 2 + 4 * 0 * z ^ 3) =
        (fun z => 2 * Q2 + 2 * (3 * Q3) * z + 3 * (4 * Q4) * z ^ 2 + 4 * 0 * z ^ 3 +
          0 * z ^ 4) := by
      funext z; ring
    rw [← e] at h
    exact (HasDerivAt.fun_sub (hg2 z hz) h).congr_deriv (by simp only [φ3]; ring)
  have d4' : ∀ z ∈ Icc x0 x3, HasDerivAt φ3 (φ4 z) z := by
    intro z hz
    have h := hasDerivAt_quartic (2 * (3 * Q3)) (2 * (3 * (4 * Q4))) (3 * 0) (4 * 0) 0 z
    have e : (fun z => 2 * (3 * Q3) + 2 * (3 * (4 * Q4)) * z + 3 * 0 * z ^ 2 + 4 * 0 * z ^ 3) =
        (fun z => 2 * (3 * Q3) + 2 * (3 * (4 * Q4)) * z + 3 * 0 * z ^ 2 + 4 * 0 * z ^ 3 +
          0 * z ^ 4) := by
      funext z; ring
    rw [← e] at h
    exact (HasDerivAt.fun_sub (hg3 z hz) h).congr_deriv (by simp only [φ4]; ring)
  have e0 : φ x0 = 0 := by
    simp only [φ]; rw [← hQ, n0]; simp [omega4]
  have e1 : φ x1 = 0 := by
    simp only [φ]; rw [← hQ, n1]; simp [omega4]
  have e2 : φ x2 = 0 := by
    simp only [φ]; rw [← hQ, n2]; simp [omega4]
  have e3 : φ x3 = 0 := by
    simp only [φ]; rw [← hQ, n3]; simp [omega4]
  have ey : φ y = 0 := by
    simp only [φ]; rw [← hQ]; simp only [K]; field_simp; ring
  obtain ⟨ζ, hζ, eζ⟩ := rolle_four h01 hy1 hy2 (by linarith) d1' d2' d3' d4' e0 e1 ey e2 e3
  have hK : |K| ≤ M / 24 := by
    have : K = g4 ζ / 24 := by simp only [φ4, Q4] at eζ; linarith
    rw [this, abs_div]
    have := hM ζ hζ
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 24)]; linarith
  have : g y - N y = K * omega4 x0 x1 x2 x3 y := by simp only [K]; field_simp
  rw [this, abs_mul]
  have := mul_le_mul_of_nonneg_right hK (abs_nonneg (omega4 x0 x1 x2 x3 y))
  linarith

/-- Bound on the node polynomial on the middle interval. -/
theorem abs_omega_le {x0 x1 x2 x3 y : ℝ} (h01 : x0 ≤ x1) (h23 : x2 ≤ x3) (hy : y ∈ Icc x1 x2) :
    |omega4 x0 x1 x2 x3 y| ≤ (x2 - x1) ^ 2 * (x2 - x0) * (x3 - x1) / 4 := by
  obtain ⟨hy1, hy2⟩ := hy
  unfold omega4
  have e : (y - x0) * (y - x1) * (y - x2) * (y - x3) =
      ((y - x1) * (x2 - y)) * ((y - x0) * (x3 - y)) := by ring
  rw [e, abs_mul, abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
  have h1 : (y - x1) * (x2 - y) ≤ (x2 - x1) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * y - x1 - x2)]
  have h2 : (y - x0) * (x3 - y) ≤ (x2 - x0) * (x3 - x1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  calc (y - x1) * (x2 - y) * ((y - x0) * (x3 - y)) ≤ (x2 - x1) ^ 2 / 4 * ((x2 - x0) * (x3 - x1)) :=
        mul_le_mul h1 h2 (by nlinarith) (by positivity)
    _ = (x2 - x1) ^ 2 * (x2 - x0) * (x3 - x1) / 4 := by ring

/-! ## Lagrange form and the Lebesgue bound -/

/-- The outer Lagrange basis function `l₀`. -/
@[expose] def lag0 (x0 x1 x2 x3 y : ℝ) : ℝ :=
  (y - x1) * (y - x2) * (y - x3) / ((x0 - x1) * (x0 - x2) * (x0 - x3))
/-- The inner Lagrange basis function `l₁`. -/
@[expose] def lag1 (x0 x1 x2 x3 y : ℝ) : ℝ :=
  (y - x0) * (y - x2) * (y - x3) / ((x1 - x0) * (x1 - x2) * (x1 - x3))
/-- The inner Lagrange basis function `l₂`. -/
@[expose] def lag2 (x0 x1 x2 x3 y : ℝ) : ℝ :=
  (y - x0) * (y - x1) * (y - x3) / ((x2 - x0) * (x2 - x1) * (x2 - x3))
/-- The outer Lagrange basis function `l₃`. -/
@[expose] def lag3 (x0 x1 x2 x3 y : ℝ) : ℝ :=
  (y - x0) * (y - x1) * (y - x2) / ((x3 - x0) * (x3 - x1) * (x3 - x2))

/-- The Newton form equals the Lagrange form. -/
theorem newt_lagrange {x0 x1 x2 x3 : ℝ} (h01 : x0 < x1) (h12 : x1 < x2) (h23 : x2 < x3)
    (v0 v1 v2 v3 y : ℝ) :
    newt x0 x1 x2 x3 v0 v1 v2 v3 y = lag0 x0 x1 x2 x3 y * v0 + lag1 x0 x1 x2 x3 y * v1 +
      lag2 x0 x1 x2 x3 y * v2 + lag3 x0 x1 x2 x3 y * v3 := by
  have a : x1 - x0 ≠ 0 := by linarith
  have b : x2 - x1 ≠ 0 := by linarith
  have c : x2 - x0 ≠ 0 := by linarith
  have d : x3 - x2 ≠ 0 := by linarith
  have e : x3 - x1 ≠ 0 := by linarith
  have f : x3 - x0 ≠ 0 := by linarith
  have a' : x0 - x1 ≠ 0 := by linarith
  have b' : x1 - x2 ≠ 0 := by linarith
  have c' : x0 - x2 ≠ 0 := by linarith
  have d' : x2 - x3 ≠ 0 := by linarith
  have e' : x1 - x3 ≠ 0 := by linarith
  have f' : x0 - x3 ≠ 0 := by linarith
  unfold newt dd3 dd2 lag0 lag1 lag2 lag3
  field_simp
  ring

/-- **Lebesgue bound** on the middle interval: if `|vᵢ| ≤ U` and `B₀`, `B₃` bound the outer basis
functions, i.e. `B₀ ≥ (x₂ - x₁)²(x₃ - x₁)/(4(x₁ - x₀)(x₂ - x₀)(x₃ - x₀))` and
`B₃ ≥ (x₂ - x₁)²(x₂ - x₀)/(4(x₃ - x₀)(x₃ - x₁)(x₃ - x₂))`, then
`|newt v y| ≤ (1 + 2(B₀ + B₃)) U`. -/
theorem abs_newt_le {x0 x1 x2 x3 : ℝ} (h01 : x0 < x1) (h12 : x1 < x2) (h23 : x2 < x3)
    {v0 v1 v2 v3 U B0 B3 y : ℝ} (hy : y ∈ Icc x1 x2) (hv0 : |v0| ≤ U) (hv1 : |v1| ≤ U)
    (hv2 : |v2| ≤ U) (hv3 : |v3| ≤ U)
    (hB0 : (x2 - x1) ^ 2 * (x3 - x1) / (4 * ((x1 - x0) * (x2 - x0) * (x3 - x0))) ≤ B0)
    (hB3 : (x2 - x1) ^ 2 * (x2 - x0) / (4 * ((x3 - x0) * (x3 - x1) * (x3 - x2))) ≤ B3) :
    |newt x0 x1 x2 x3 v0 v1 v2 v3 y| ≤ (1 + 2 * (B0 + B3)) * U := by
  obtain ⟨hy1, hy2⟩ := hy
  rw [newt_lagrange h01 h12 h23]
  have hU : 0 ≤ U := (abs_nonneg _).trans hv0
  -- signs of the basis functions
  have hc : (y - x1) * (x2 - y) ≤ (x2 - x1) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * y - x1 - x2)]
  have hc0 : 0 ≤ (y - x1) * (x2 - y) := by nlinarith
  have l0n : lag0 x0 x1 x2 x3 y ≤ 0 ∧ -lag0 x0 x1 x2 x3 y ≤ B0 := by
    have e : lag0 x0 x1 x2 x3 y = -(((y - x1) * (x2 - y)) * (x3 - y) /
        ((x1 - x0) * (x2 - x0) * (x3 - x0))) := by
      unfold lag0
      have : (x0 - x1) * (x0 - x2) * (x0 - x3) = -((x1 - x0) * (x2 - x0) * (x3 - x0)) := by ring
      rw [this, div_neg]; ring
    have hden : 0 < (x1 - x0) * (x2 - x0) * (x3 - x0) := by
      apply mul_pos (mul_pos _ _) _ <;> linarith
    have hnum : 0 ≤ (y - x1) * (x2 - y) * (x3 - y) := mul_nonneg hc0 (by linarith)
    rw [e]
    refine ⟨by simp only [neg_nonpos]; positivity, ?_⟩
    rw [neg_neg]
    refine le_trans ?_ hB0
    rw [div_le_div_iff₀ hden (by positivity)]
    have : (y - x1) * (x2 - y) * (x3 - y) ≤ (x2 - x1) ^ 2 / 4 * (x3 - x1) :=
      mul_le_mul hc (by linarith) (by linarith) (by positivity)
    nlinarith
  have l3n : lag3 x0 x1 x2 x3 y ≤ 0 ∧ -lag3 x0 x1 x2 x3 y ≤ B3 := by
    have e : lag3 x0 x1 x2 x3 y = -(((y - x1) * (x2 - y)) * (y - x0) /
        ((x3 - x0) * (x3 - x1) * (x3 - x2))) := by
      unfold lag3; rw [← neg_div]; congr 1; ring
    have hden : 0 < (x3 - x0) * (x3 - x1) * (x3 - x2) := by
      apply mul_pos (mul_pos _ _) _ <;> linarith
    have hnum : 0 ≤ (y - x1) * (x2 - y) * (y - x0) := mul_nonneg hc0 (by linarith)
    rw [e]
    refine ⟨by simp only [neg_nonpos]; positivity, ?_⟩
    rw [neg_neg]
    refine le_trans ?_ hB3
    rw [div_le_div_iff₀ hden (by positivity)]
    have : (y - x1) * (x2 - y) * (y - x0) ≤ (x2 - x1) ^ 2 / 4 * (x2 - x0) :=
      mul_le_mul hc (by linarith) (by linarith) (by positivity)
    nlinarith
  have l1p : 0 ≤ lag1 x0 x1 x2 x3 y := by
    unfold lag1
    have e : (x1 - x0) * (x1 - x2) * (x1 - x3) = (x1 - x0) * (x2 - x1) * (x3 - x1) := by ring
    rw [e]
    apply div_nonneg
    · have : (y - x0) * (y - x2) * (y - x3) = (y - x0) * (x2 - y) * (x3 - y) := by ring
      rw [this]; apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
    · apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
  have l2p : 0 ≤ lag2 x0 x1 x2 x3 y := by
    unfold lag2
    have e : (x2 - x0) * (x2 - x1) * (x2 - x3) = -((x2 - x0) * (x2 - x1) * (x3 - x2)) := by ring
    have e2 : (y - x0) * (y - x1) * (y - x3) = -((y - x0) * (y - x1) * (x3 - y)) := by ring
    rw [e, e2, neg_div_neg_eq]
    apply div_nonneg
    · apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
    · apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
  have hsum : lag0 x0 x1 x2 x3 y + lag1 x0 x1 x2 x3 y + lag2 x0 x1 x2 x3 y +
      lag3 x0 x1 x2 x3 y = 1 := by
    have := newt_lagrange h01 h12 h23 1 1 1 1 y
    simp only [newt, dd3, dd2, sub_self, zero_div, zero_mul, add_zero, mul_one] at this
    linarith
  calc |lag0 x0 x1 x2 x3 y * v0 + lag1 x0 x1 x2 x3 y * v1 + lag2 x0 x1 x2 x3 y * v2 +
        lag3 x0 x1 x2 x3 y * v3|
      ≤ |lag0 x0 x1 x2 x3 y| * |v0| + |lag1 x0 x1 x2 x3 y| * |v1| + |lag2 x0 x1 x2 x3 y| * |v2| +
        |lag3 x0 x1 x2 x3 y| * |v3| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (-lag0 x0 x1 x2 x3 y) * U + lag1 x0 x1 x2 x3 y * U + lag2 x0 x1 x2 x3 y * U +
        (-lag3 x0 x1 x2 x3 y) * U := by
        rw [abs_of_nonpos l0n.1, abs_of_nonneg l1p, abs_of_nonneg l2p, abs_of_nonpos l3n.1]
        gcongr <;> linarith [l0n.1, l3n.1]
    _ = (1 - 2 * (lag0 x0 x1 x2 x3 y + lag3 x0 x1 x2 x3 y)) * U := by
        linear_combination U * hsum
    _ ≤ (1 + 2 * (B0 + B3)) * U := by
        apply mul_le_mul_of_nonneg_right _ hU; linarith [l0n.2, l3n.2]

/-! ## Splitting off the linear part -/

/-- The Newton form is the linear interpolant plus two divided-difference corrections, with
explicit bounds on the correction coefficients on `[x₁, x₂]`. -/
theorem newt_split {x0 x1 x2 x3 : ℝ} (h01 : x0 < x1) (h12 : x1 < x2) {y : ℝ}
    (hy : y ∈ Icc x1 x2) (v0 v1 v2 v3 : ℝ) :
    |newt x0 x1 x2 x3 v0 v1 v2 v3 y| ≤ max |v1| |v2| +
      (x2 - x1) ^ 2 / 4 * |dd2 x0 x1 x2 v0 v1 v2| +
      (x2 - x1) ^ 2 * (x2 - x0) / 4 * |dd3 x0 x1 x2 x3 v0 v1 v2 v3| := by
  obtain ⟨hy1, hy2⟩ := hy
  have hd : 0 < x2 - x1 := by linarith
  set θ := (y - x1) / (x2 - x1)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := by rw [div_le_one hd]; linarith
  have hlin : v1 + (v2 - v1) / (x2 - x1) * (y - x1) = (1 - θ) * v1 + θ * v2 := by
    simp only [θ]; field_simp; ring
  have hL : |(1 - θ) * v1 + θ * v2| ≤ max |v1| |v2| := by
    calc |(1 - θ) * v1 + θ * v2| ≤ (1 - θ) * |v1| + θ * |v2| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * max |v1| |v2| + θ * max |v1| |v2| :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ0)
      _ = max |v1| |v2| := by ring
  have hc2 : |(y - x1) * (y - x2)| ≤ (x2 - x1) ^ 2 / 4 := by
    rw [abs_of_nonpos (by nlinarith)]; nlinarith [sq_nonneg (2 * y - x1 - x2)]
  have hc3 : |(y - x1) * (y - x2) * (y - x0)| ≤ (x2 - x1) ^ 2 * (x2 - x0) / 4 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x0)]
    calc |(y - x1) * (y - x2)| * (y - x0) ≤ (x2 - x1) ^ 2 / 4 * (x2 - x0) :=
          mul_le_mul hc2 (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  unfold newt
  rw [hlin]
  calc |(1 - θ) * v1 + θ * v2 + dd2 x0 x1 x2 v0 v1 v2 * ((y - x1) * (y - x2)) +
        dd3 x0 x1 x2 x3 v0 v1 v2 v3 * ((y - x1) * (y - x2) * (y - x0))|
      ≤ |(1 - θ) * v1 + θ * v2| + |dd2 x0 x1 x2 v0 v1 v2 * ((y - x1) * (y - x2))| +
        |dd3 x0 x1 x2 x3 v0 v1 v2 v3 * ((y - x1) * (y - x2) * (y - x0))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ max |v1| |v2| + |dd2 x0 x1 x2 v0 v1 v2| * ((x2 - x1) ^ 2 / 4) +
        |dd3 x0 x1 x2 x3 v0 v1 v2 v3| * ((x2 - x1) ^ 2 * (x2 - x0) / 4) := by
        rw [abs_mul (dd2 x0 x1 x2 v0 v1 v2), abs_mul (dd3 x0 x1 x2 x3 v0 v1 v2 v3)]
        exact add_le_add (add_le_add hL (mul_le_mul_of_nonneg_left hc2 (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left hc3 (abs_nonneg _))
    _ = _ := by ring

/-! ## Tensor-product cells -/

/-- The bicubic interpolant at `(s, w)`: interpolation in `w` on each of the four `s`-lines, then
in `s`. -/
@[expose] def bicubic (s0 s1 s2 s3 w0 w1 w2 w3 : ℝ) (g : Fin 4 → Fin 4 → ℝ) (s w : ℝ) : ℝ :=
  newt s0 s1 s2 s3 (newt w0 w1 w2 w3 (g 0 0) (g 0 1) (g 0 2) (g 0 3) w)
    (newt w0 w1 w2 w3 (g 1 0) (g 1 1) (g 1 2) (g 1 3) w)
    (newt w0 w1 w2 w3 (g 2 0) (g 2 1) (g 2 2) (g 2 3) w)
    (newt w0 w1 w2 w3 (g 3 0) (g 3 1) (g 3 2) (g 3 3) w) s

/-- `newt` is linear in the values. -/
theorem newt_add_smul (x0 x1 x2 x3 : ℝ) (a0 a1 a2 a3 b0 b1 b2 b3 c y : ℝ) :
    newt x0 x1 x2 x3 (a0 + c * b0) (a1 + c * b1) (a2 + c * b2) (a3 + c * b3) y =
      newt x0 x1 x2 x3 a0 a1 a2 a3 y + c * newt x0 x1 x2 x3 b0 b1 b2 b3 y := by
  unfold newt dd3 dd2; ring

/-- `dd2` of interpolated values is the interpolant of the `dd2`s. -/
theorem dd2_newt (s0 s1 s2 w0 w1 w2 w3 : ℝ) (g : Fin 4 → Fin 4 → ℝ) (w : ℝ) :
    dd2 s0 s1 s2 (newt w0 w1 w2 w3 (g 0 0) (g 0 1) (g 0 2) (g 0 3) w)
      (newt w0 w1 w2 w3 (g 1 0) (g 1 1) (g 1 2) (g 1 3) w)
      (newt w0 w1 w2 w3 (g 2 0) (g 2 1) (g 2 2) (g 2 3) w) =
    newt w0 w1 w2 w3 (dd2 s0 s1 s2 (g 0 0) (g 1 0) (g 2 0)) (dd2 s0 s1 s2 (g 0 1) (g 1 1) (g 2 1))
      (dd2 s0 s1 s2 (g 0 2) (g 1 2) (g 2 2)) (dd2 s0 s1 s2 (g 0 3) (g 1 3) (g 2 3)) w := by
  unfold newt dd3 dd2; ring

/-- `dd3` of interpolated values is the interpolant of the `dd3`s. -/
theorem dd3_newt (s0 s1 s2 s3 w0 w1 w2 w3 : ℝ) (g : Fin 4 → Fin 4 → ℝ) (w : ℝ) :
    dd3 s0 s1 s2 s3 (newt w0 w1 w2 w3 (g 0 0) (g 0 1) (g 0 2) (g 0 3) w)
      (newt w0 w1 w2 w3 (g 1 0) (g 1 1) (g 1 2) (g 1 3) w)
      (newt w0 w1 w2 w3 (g 2 0) (g 2 1) (g 2 2) (g 2 3) w)
      (newt w0 w1 w2 w3 (g 3 0) (g 3 1) (g 3 2) (g 3 3) w) =
    newt w0 w1 w2 w3 (dd3 s0 s1 s2 s3 (g 0 0) (g 1 0) (g 2 0) (g 3 0))
      (dd3 s0 s1 s2 s3 (g 0 1) (g 1 1) (g 2 1) (g 3 1))
      (dd3 s0 s1 s2 s3 (g 0 2) (g 1 2) (g 2 2) (g 3 2))
      (dd3 s0 s1 s2 s3 (g 0 3) (g 1 3) (g 2 3) (g 3 3)) w := by
  unfold newt dd3 dd2; ring

/-- **Tensor-product cell bound.** On the middle cell `[s₁, s₂] × [w₁, w₂]` the bicubic
interpolant is bounded by the largest middle value `E`, the `w`-corrections `Cw` (on the two
middle `s`-lines) and the `s`-corrections `Cs` (on the four `w`-columns, amplified by the
Lebesgue factor `Λ_w = 1 + 2(B₀ + B₃)` of the `w`-nodes). -/
theorem tensor_bound {s0 s1 s2 s3 w0 w1 w2 w3 : ℝ} (hs01 : s0 < s1) (hs12 : s1 < s2)
    (_hs23 : s2 < s3) (hw01 : w0 < w1) (hw12 : w1 < w2) (hw23 : w2 < w3) (g : Fin 4 → Fin 4 → ℝ)
    {s w E Cw Cs B0 B3 : ℝ} (hs : s ∈ Icc s1 s2) (hw : w ∈ Icc w1 w2)
    (hE : ∀ i j : Fin 4, (i = 1 ∨ i = 2) → (j = 1 ∨ j = 2) → |g i j| ≤ E)
    (hCw : ∀ i : Fin 4, (i = 1 ∨ i = 2) →
      (w2 - w1) ^ 2 / 4 * |dd2 w0 w1 w2 (g i 0) (g i 1) (g i 2)| +
        (w2 - w1) ^ 2 * (w2 - w0) / 4 * |dd3 w0 w1 w2 w3 (g i 0) (g i 1) (g i 2) (g i 3)| ≤ Cw)
    (hCs : ∀ j : Fin 4,
      (s2 - s1) ^ 2 / 4 * |dd2 s0 s1 s2 (g 0 j) (g 1 j) (g 2 j)| +
        (s2 - s1) ^ 2 * (s2 - s0) / 4 * |dd3 s0 s1 s2 s3 (g 0 j) (g 1 j) (g 2 j) (g 3 j)| ≤ Cs)
    (hB0 : (w2 - w1) ^ 2 * (w3 - w1) / (4 * ((w1 - w0) * (w2 - w0) * (w3 - w0))) ≤ B0)
    (hB3 : (w2 - w1) ^ 2 * (w2 - w0) / (4 * ((w3 - w0) * (w3 - w1) * (w3 - w2))) ≤ B3) :
    |bicubic s0 s1 s2 s3 w0 w1 w2 w3 g s w| ≤ E + Cw + (1 + 2 * (B0 + B3)) * Cs := by
  unfold bicubic
  refine (newt_split hs01 hs12 hs _ _ _ _).trans ?_
  -- the two middle lines
  have hQ : ∀ i : Fin 4, (i = 1 ∨ i = 2) →
      |newt w0 w1 w2 w3 (g i 0) (g i 1) (g i 2) (g i 3) w| ≤ E + Cw := by
    intro i hi
    refine (newt_split hw01 hw12 hw _ _ _ _).trans ?_
    have h1 := hE i 1 hi (Or.inl rfl)
    have h2 := hE i 2 hi (Or.inr rfl)
    have := hCw i hi
    have : max |g i 1| |g i 2| ≤ E := max_le h1 h2
    linarith
  have hmax := max_le (hQ 1 (Or.inl rfl)) (hQ 2 (Or.inr rfl))
  -- the corrections in `s`
  rw [dd2_newt, dd3_newt]
  set Bd2 := fun j : Fin 4 => |dd2 s0 s1 s2 (g 0 j) (g 1 j) (g 2 j)|
  set Bd3 := fun j : Fin 4 => |dd3 s0 s1 s2 s3 (g 0 j) (g 1 j) (g 2 j) (g 3 j)|
  have hsd : 0 < s2 - s1 := by linarith
  -- weighted combination: interpolate the combination `c₂ dd₂ + c₃ dd₃` column-wise
  have key : (s2 - s1) ^ 2 / 4 *
      |newt w0 w1 w2 w3 (dd2 s0 s1 s2 (g 0 0) (g 1 0) (g 2 0)) (dd2 s0 s1 s2 (g 0 1) (g 1 1) (g 2
          1))
        (dd2 s0 s1 s2 (g 0 2) (g 1 2) (g 2 2)) (dd2 s0 s1 s2 (g 0 3) (g 1 3) (g 2 3)) w| +
      (s2 - s1) ^ 2 * (s2 - s0) / 4 *
      |newt w0 w1 w2 w3 (dd3 s0 s1 s2 s3 (g 0 0) (g 1 0) (g 2 0) (g 3 0))
        (dd3 s0 s1 s2 s3 (g 0 1) (g 1 1) (g 2 1) (g 3 1))
        (dd3 s0 s1 s2 s3 (g 0 2) (g 1 2) (g 2 2) (g 3 2))
        (dd3 s0 s1 s2 s3 (g 0 3) (g 1 3) (g 2 3) (g 3 3)) w| ≤ (1 + 2 * (B0 + B3)) * Cs := by
    have hΛ : 0 ≤ 1 + 2 * (B0 + B3) := by
      have : 0 ≤ B0 := le_trans (by
        apply div_nonneg (by nlinarith [sq_nonneg (w2 - w1)])
        apply mul_nonneg (by norm_num); apply mul_nonneg (mul_nonneg _ _) _ <;> linarith) hB0
      have : 0 ≤ B3 := le_trans (by
        apply div_nonneg (by nlinarith [sq_nonneg (w2 - w1)])
        apply mul_nonneg (by norm_num); apply mul_nonneg (mul_nonneg _ _) _ <;> linarith) hB3
      linarith
    -- bound each column by `Cs` after scaling
    have hcol : ∀ j : Fin 4, (s2 - s1) ^ 2 / 4 * Bd2 j + (s2 - s1) ^ 2 * (s2 - s0) / 4 * Bd3 j ≤
        Cs :=
      hCs
    have c2p : 0 ≤ (s2 - s1) ^ 2 / 4 := by positivity
    have c3p : 0 ≤ (s2 - s1) ^ 2 * (s2 - s0) / 4 := by
      apply div_nonneg _ (by norm_num); apply mul_nonneg (sq_nonneg _); linarith
    -- the sign trick: |a| + |b| = max over signs of ε₁ a + ε₂ b, and both are interpolants
    have hsign : ∀ ε1 ε2 : ℝ, |ε1| ≤ 1 → |ε2| ≤ 1 →
        (s2 - s1) ^ 2 / 4 * ε1 *
          newt w0 w1 w2 w3 (dd2 s0 s1 s2 (g 0 0) (g 1 0) (g 2 0))
            (dd2 s0 s1 s2 (g 0 1) (g 1 1) (g 2 1)) (dd2 s0 s1 s2 (g 0 2) (g 1 2) (g 2 2))
            (dd2 s0 s1 s2 (g 0 3) (g 1 3) (g 2 3)) w +
        (s2 - s1) ^ 2 * (s2 - s0) / 4 * ε2 *
          newt w0 w1 w2 w3 (dd3 s0 s1 s2 s3 (g 0 0) (g 1 0) (g 2 0) (g 3 0))
            (dd3 s0 s1 s2 s3 (g 0 1) (g 1 1) (g 2 1) (g 3 1))
            (dd3 s0 s1 s2 s3 (g 0 2) (g 1 2) (g 2 2) (g 3 2))
            (dd3 s0 s1 s2 s3 (g 0 3) (g 1 3) (g 2 3) (g 3 3)) w ≤ (1 + 2 * (B0 + B3)) * Cs := by
      intro ε1 ε2 he1 he2
      set a := (s2 - s1) ^ 2 / 4 * ε1
      set b := (s2 - s1) ^ 2 * (s2 - s0) / 4 * ε2
      have hcomb : ∀ j : Fin 4, |a * dd2 s0 s1 s2 (g 0 j) (g 1 j) (g 2 j) +
          b * dd3 s0 s1 s2 s3 (g 0 j) (g 1 j) (g 2 j) (g 3 j)| ≤ Cs := by
        intro j
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul a, abs_mul b]
        have ha : |a| ≤ (s2 - s1) ^ 2 / 4 := by
          simp only [a]; rw [abs_mul, abs_of_nonneg c2p]
          exact mul_le_of_le_one_right c2p he1
        have hb : |b| ≤ (s2 - s1) ^ 2 * (s2 - s0) / 4 := by
          simp only [b]; rw [abs_mul, abs_of_nonneg c3p]
          exact mul_le_of_le_one_right c3p he2
        have := hcol j
        calc |a| * |dd2 s0 s1 s2 (g 0 j) (g 1 j) (g 2 j)| +
              |b| * |dd3 s0 s1 s2 s3 (g 0 j) (g 1 j) (g 2 j) (g 3 j)|
            ≤ (s2 - s1) ^ 2 / 4 * Bd2 j + (s2 - s1) ^ 2 * (s2 - s0) / 4 * Bd3 j := by
              gcongr
          _ ≤ Cs := this
      have hlin : a * newt w0 w1 w2 w3 (dd2 s0 s1 s2 (g 0 0) (g 1 0) (g 2 0))
            (dd2 s0 s1 s2 (g 0 1) (g 1 1) (g 2 1)) (dd2 s0 s1 s2 (g 0 2) (g 1 2) (g 2 2))
            (dd2 s0 s1 s2 (g 0 3) (g 1 3) (g 2 3)) w +
          b * newt w0 w1 w2 w3 (dd3 s0 s1 s2 s3 (g 0 0) (g 1 0) (g 2 0) (g 3 0))
            (dd3 s0 s1 s2 s3 (g 0 1) (g 1 1) (g 2 1) (g 3 1))
            (dd3 s0 s1 s2 s3 (g 0 2) (g 1 2) (g 2 2) (g 3 2))
            (dd3 s0 s1 s2 s3 (g 0 3) (g 1 3) (g 2 3) (g 3 3)) w =
          newt w0 w1 w2 w3
            (a * dd2 s0 s1 s2 (g 0 0) (g 1 0) (g 2 0) + b * dd3 s0 s1 s2 s3 (g 0 0) (g 1 0) (g 2 0)
                (g 3 0))
            (a * dd2 s0 s1 s2 (g 0 1) (g 1 1) (g 2 1) + b * dd3 s0 s1 s2 s3 (g 0 1) (g 1 1) (g 2 1)
                (g 3 1))
            (a * dd2 s0 s1 s2 (g 0 2) (g 1 2) (g 2 2) + b * dd3 s0 s1 s2 s3 (g 0 2) (g 1 2) (g 2 2)
                (g 3 2))
            (a * dd2 s0 s1 s2 (g 0 3) (g 1 3) (g 2 3) + b * dd3 s0 s1 s2 s3 (g 0 3) (g 1 3) (g 2 3)
                (g 3 3))
            w := by
        unfold newt dd3 dd2; ring
      rw [hlin]
      exact (le_abs_self _).trans (abs_newt_le hw01 hw12 hw23 hw (hcomb 0) (hcomb 1) (hcomb 2)
        (hcomb 3) hB0 hB3)
    set N2 := newt w0 w1 w2 w3 (dd2 s0 s1 s2 (g 0 0) (g 1 0) (g 2 0))
      (dd2 s0 s1 s2 (g 0 1) (g 1 1) (g 2 1)) (dd2 s0 s1 s2 (g 0 2) (g 1 2) (g 2 2))
      (dd2 s0 s1 s2 (g 0 3) (g 1 3) (g 2 3)) w
    set N3 := newt w0 w1 w2 w3 (dd3 s0 s1 s2 s3 (g 0 0) (g 1 0) (g 2 0) (g 3 0))
      (dd3 s0 s1 s2 s3 (g 0 1) (g 1 1) (g 2 1) (g 3 1))
      (dd3 s0 s1 s2 s3 (g 0 2) (g 1 2) (g 2 2) (g 3 2))
      (dd3 s0 s1 s2 s3 (g 0 3) (g 1 3) (g 2 3) (g 3 3)) w
    have h := hsign (SignType.sign N2) (SignType.sign N3)
      (by rcases lt_trichotomy N2 0 with h | h | h <;> simp [h, sign_neg, sign_pos])
      (by rcases lt_trichotomy N3 0 with h | h | h <;> simp [h, sign_neg, sign_pos])
    have e2 : (SignType.sign N2 : ℝ) * N2 = |N2| := by
      rcases lt_trichotomy N2 0 with h | h | h
      · simp [h, sign_neg, abs_of_neg h]
      · simp [h]
      · simp [h, sign_pos, abs_of_pos h]
    have e3 : (SignType.sign N3 : ℝ) * N3 = |N3| := by
      rcases lt_trichotomy N3 0 with h | h | h
      · simp [h, sign_neg, abs_of_neg h]
      · simp [h]
      · simp [h, sign_pos, abs_of_pos h]
    calc (s2 - s1) ^ 2 / 4 * |N2| + (s2 - s1) ^ 2 * (s2 - s0) / 4 * |N3|
        = (s2 - s1) ^ 2 / 4 * (SignType.sign N2 : ℝ) * N2 +
          (s2 - s1) ^ 2 * (s2 - s0) / 4 * (SignType.sign N3 : ℝ) * N3 := by
          rw [mul_assoc, e2, mul_assoc ((s2 - s1) ^ 2 * (s2 - s0) / 4), e3]
      _ ≤ _ := h
  linarith

end PlasmaLean.Design.PolygonCoil
