/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSegment
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The straight-segment Biot–Savart field at complex points

Stage 1 of the coil-field KAM route (`notes/theory/after-kam.md` §2.3, option (a)).

For a straight filament `p → q` and a complex point `y ∈ ℂ³` put `a = p - y`, `b = q - y`
and `w(t) = seg p q t - y`. The complex quadratic `Q(t) = w(t)·w(t)` (bilinear dot product,
`segQ`) has real part `|Re y - seg t|² - |Im y|²` (`re_segQ`), so it lies in the right half
plane as long as `|Im y|` is smaller than the distance of `Re y` from the segment. There the
principal power `Q^{-3/2}` is holomorphic, and we define

`segFieldC κ p q y = κ (∫₀¹ Q(t)^{-3/2} dt) · (a × b)`,

the complex extension of the real kernel `|a + t v|⁻³ (a × b)` of `PolygonCoil.seg_kernel`.

* `segFieldC_ofReal`: at real points it is the closed form `PolygonCoil.segClosed` (at **every**
  real point, matching the convention `0⁻¹ = 0` on the segment).
* `segFieldC_bound`: if `η = |Im y| < d ≤ dist(Re y, segment)` and `|Re y - p| ≤ D`, then
  `|segFieldC κ p q y| ≤ |κ| |q - p| √(D² + η²) / (d² - η²)^{3/2}` (Hermitian norm `hnorm`;
  `segFieldC_bound_sup` for the sup norm of `Fin 3 → ℂ`).
* `segFieldC_differentiableOn`: `segFieldC κ p q` is `ℂ`-differentiable on the open domain
  `segDomain p q = {y | ∀ t ∈ [0,1], 0 < Re Q(t)}` (`isOpen_segDomain`), which contains
  the region of the bound
  (`boundRegion_subset_segDomain`). Proof: differentiation under the integral sign with the
  explicit derivative `-(3/2) Q^{-5/2} DQ` and a uniform bound on a small ball (compactness
  of `[0,1]` plus a Lipschitz estimate for `Q` in `y`).

**Sanity.** `segFieldC_zero_kappa` (no current, no field), `hnorm_ofRealV` (the Hermitian norm
extends the Euclidean norm), `segFieldC_bound_real` (at `η = 0` the bound is the real
`|κ| |q-p| D / d³` shape), `segDomain_ofReal` (real points off the segment are in the domain),
and the rejected fixture `not_mem_segDomain_endpoint` (the endpoint `p` itself is excluded).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Fields.BiotSavartComplex

open Complex MeasureTheory Set Filter Topology
open scoped Interval
open PlasmaLean.Fields PlasmaLean.Design.PolygonCoil PlasmaLean.Design.RationalStellarator.CoilsTF

/-- Complex three-vectors (with the sup norm of `Fin 3 → ℂ`). -/
abbrev CVec : Type := Fin 3 → ℂ

/-- The complex-bilinear dot product `u·w = ∑ uᵢ wᵢ` (no conjugation). -/
def dotC (u w : CVec) : ℂ := ∑ i, u i * w i

/-- The complex cross product. -/
def crossC (u w : CVec) : CVec :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

/-- First coordinate of the cross product. -/
@[simp] theorem crossC_zero (u w : CVec) : crossC u w 0 = u 1 * w 2 - u 2 * w 1 := rfl

/-- Second coordinate of the cross product. -/
@[simp] theorem crossC_one (u w : CVec) : crossC u w 1 = u 2 * w 0 - u 0 * w 2 := rfl

/-- Third coordinate of the cross product. -/
@[simp] theorem crossC_two (u w : CVec) : crossC u w 2 = u 0 * w 1 - u 1 * w 0 := rfl

/-- A real vector viewed as a complex vector. -/
def ofRealV (x : Space) : CVec := fun i => ((x i : ℝ) : ℂ)

/-- The real part of a complex vector. -/
def reV (y : CVec) : Space := WithLp.toLp 2 (fun i => (y i).re)

/-- The imaginary part of a complex vector. -/
def imV (y : CVec) : Space := WithLp.toLp 2 (fun i => (y i).im)

/-- The Hermitian norm `√(∑ |yᵢ|²)`. -/
def hnorm (y : CVec) : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2)

/-- Coordinates of `reV`. -/
@[simp] theorem reV_apply (y : CVec) (i : Fin 3) : reV y i = (y i).re := rfl

/-- Coordinates of `imV`. -/
@[simp] theorem imV_apply (y : CVec) (i : Fin 3) : imV y i = (y i).im := rfl

/-- Coordinates of `ofRealV`. -/
@[simp] theorem ofRealV_apply (x : Space) (i : Fin 3) : ofRealV x i = ((x i : ℝ) : ℂ) := rfl

/-- The squared Euclidean norm of a vector of `Space` in coordinates. -/
theorem norm_sq_space (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- `hnorm y² = |Re y|² + |Im y|²`. -/
theorem hnorm_sq (y : CVec) : hnorm y ^ 2 = ‖reV y‖ ^ 2 + ‖imV y‖ ^ 2 := by
  rw [hnorm, Real.sq_sqrt (by positivity), norm_sq_space, norm_sq_space, Fin.sum_univ_three]
  simp only [reV_apply, imV_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The Hermitian norm is nonnegative. -/
theorem hnorm_nonneg (y : CVec) : 0 ≤ hnorm y := Real.sqrt_nonneg _

/-- `hnorm y = √(|Re y|² + |Im y|²)`. -/
theorem hnorm_eq (y : CVec) : hnorm y = Real.sqrt (‖reV y‖ ^ 2 + ‖imV y‖ ^ 2) := by
  rw [← hnorm_sq, Real.sqrt_sq (hnorm_nonneg y)]

/-- The sup norm is at most the Hermitian norm. -/
theorem norm_le_hnorm (y : CVec) : ‖y‖ ≤ hnorm y := by
  refine (pi_norm_le_iff_of_nonneg (hnorm_nonneg y)).2 fun i => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

/-- Scaling: `hnorm (c • y) = |c| hnorm y`. -/
theorem hnorm_smul (c : ℂ) (y : CVec) : hnorm (c • y) = ‖c‖ * hnorm y := by
  rw [hnorm, hnorm, ← Real.sqrt_sq (norm_nonneg c), ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_pow]

/-- On real vectors the Hermitian norm is the Euclidean norm (sanity). -/
theorem hnorm_ofRealV (x : Space) : hnorm (ofRealV x) = ‖x‖ := by
  rw [hnorm_eq]
  have h1 : reV (ofRealV x) = x := by ext i; simp
  have h2 : imV (ofRealV x) = 0 := by ext i; simp
  rw [h1, h2, norm_zero]
  simp

/-! ## The complex quadratic -/

/-- The complex quadratic `Q(t) = w·w`, `w = seg p q t - y`. -/
def segQ (p q : Space) (y : CVec) (t : ℝ) : ℂ :=
  dotC (ofRealV (seg p q t) - y) (ofRealV (seg p q t) - y)

/-- `Re Q(t) = |Re y - seg t|² - |Im y|²`. -/
theorem re_segQ (p q : Space) (y : CVec) (t : ℝ) :
    (segQ p q y t).re = ‖reV y - seg p q t‖ ^ 2 - ‖imV y‖ ^ 2 := by
  rw [norm_sq_space, norm_sq_space]
  simp only [segQ, dotC, Fin.sum_univ_three, Pi.sub_apply, ofRealV_apply, Complex.add_re,
    Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    PiLp.sub_apply, reV_apply, imV_apply]
  ring

/-- `Re z ≤ |z|`. -/
theorem re_le_norm_segQ (p q : Space) (y : CVec) (t : ℝ) :
    (segQ p q y t).re ≤ ‖segQ p q y t‖ := Complex.re_le_norm _

/-- The domain of holomorphy: `Re Q(t) > 0` on the whole segment. -/
def segDomain (p q : Space) : Set CVec := {y | ∀ t ∈ Icc (0 : ℝ) 1, 0 < (segQ p q y t).re}

/-- The region of the bound (`|Im y| < dist(Re y, seg t)` for all `t`) lies in the domain. -/
theorem boundRegion_subset_segDomain (p q : Space) :
    {y : CVec | ∀ t ∈ Icc (0 : ℝ) 1, ‖imV y‖ < ‖reV y - seg p q t‖} ⊆ segDomain p q := by
  intro y hy t ht
  rw [re_segQ, sub_pos]
  exact pow_lt_pow_left₀ (hy t ht) (norm_nonneg _) two_ne_zero

/-! ## The field -/

/-- The scalar integral `∫₀¹ Q(t)^{-3/2} dt` (principal power). -/
def segIntC (p q : Space) (y : CVec) : ℂ := ∫ t in (0 : ℝ)..1, (segQ p q y t) ^ (-(3 / 2 : ℂ))

/-- **The complexified segment field** `κ (∫₀¹ Q^{-3/2}) (a × b)`, `a = p - y`, `b = q - y`. -/
def segFieldC (κ : ℝ) (p q : Space) (y : CVec) : CVec :=
  ((κ : ℂ) * segIntC p q y) • crossC (ofRealV p - y) (ofRealV q - y)

/-- No current, no field (sanity). -/
theorem segFieldC_zero_kappa (p q : Space) (y : CVec) : segFieldC 0 p q y = 0 := by
  simp [segFieldC]

/-! ## The bound -/

/-- `-(3/2 : ℂ)` is a real exponent. -/
theorem neg_three_halves : (-(3 / 2 : ℂ)) = ((-(3 / 2) : ℝ) : ℂ) := by push_cast; ring

/-- `|Q^{-3/2}| = |Q|^{-3/2}`. -/
theorem norm_cpow_neg_three_halves (z : ℂ) : ‖z ^ (-(3 / 2 : ℂ))‖ = ‖z‖ ^ (-(3 / 2) : ℝ) := by
  rw [neg_three_halves, Complex.norm_cpow_real]

/-- If `Re Q(t) ≥ m > 0` on the segment then `|∫₀¹ Q^{-3/2}| ≤ m^{-3/2}`. -/
theorem norm_segIntC_le {p q : Space} {y : CVec} {m : ℝ} (hm : 0 < m)
    (hQ : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ (segQ p q y t).re) :
    ‖segIntC p q y‖ ≤ m ^ (-(3 / 2) : ℝ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := m ^ (-(3 / 2) : ℝ))
    (f := fun t => (segQ p q y t) ^ (-(3 / 2 : ℂ))) (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
      rw [norm_cpow_neg_three_halves]
      exact Real.rpow_le_rpow_of_nonpos hm ((hQ t ht').trans (re_le_norm_segQ p q y t))
        (by norm_num))
  simpa [segIntC] using h

/-- The cross product with a real vector is unchanged by adding a multiple of the first slot:
`a × (a + v) = a × v`. -/
theorem crossC_add_self (a w : CVec) : crossC a (a + w) = crossC a w := by
  ext i; fin_cases i <;> simp [crossC] <;> ring

/-- `|a × v| ≤ |a| |v|` for complex `a` and real `v` (Hermitian norm). -/
theorem hnorm_crossC_le (a : CVec) (v : Space) :
    hnorm (crossC a (ofRealV v)) ≤ hnorm a * ‖v‖ := by
  rw [hnorm, hnorm, ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_space]
  simp only [Fin.sum_univ_three, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, crossC,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ofRealV_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [sq_nonneg ((a 0).re * v 0 + (a 1).re * v 1 + (a 2).re * v 2),
    sq_nonneg ((a 0).im * v 0 + (a 1).im * v 1 + (a 2).im * v 2)]

/-- `a × b = a × (q - p)` for `a = p - y`, `b = q - y`. -/
theorem crossC_seg (p q : Space) (y : CVec) :
    crossC (ofRealV p - y) (ofRealV q - y) = crossC (ofRealV p - y) (ofRealV (q - p)) := by
  have : ofRealV q - y = (ofRealV p - y) + ofRealV (q - p) := by
    ext i; simp
  rw [this, crossC_add_self]

/-- `hnorm (p - y) = √(|Re y - p|² + |Im y|²)`. -/
theorem hnorm_sub (p : Space) (y : CVec) :
    hnorm (ofRealV p - y) = Real.sqrt (‖reV y - p‖ ^ 2 + ‖imV y‖ ^ 2) := by
  rw [hnorm_eq]
  have h1 : ‖reV (ofRealV p - y)‖ = ‖reV y - p‖ := by
    rw [← norm_neg]; congr 1; ext i; simp
  have h2 : ‖imV (ofRealV p - y)‖ = ‖imV y‖ := by
    rw [← norm_neg]; congr 1; ext i; simp
  rw [h1, h2]

/-- **Complex Biot–Savart bound for a segment.** If `η = |Im y| < d`, the real part of `y` is
at distance `≥ d` from every point of the segment, and `|Re y - p| ≤ D`, then
`|segFieldC κ p q y| ≤ |κ| |q - p| √(D² + η²) / (d² - η²)^{3/2}`. -/
theorem segFieldC_bound {κ d D : ℝ} {p q : Space} {y : CVec} (hη : ‖imV y‖ < d)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖reV y - seg p q t‖) (hD : ‖reV y - p‖ ≤ D) :
    hnorm (segFieldC κ p q y) ≤
      |κ| * ‖q - p‖ * Real.sqrt (D ^ 2 + ‖imV y‖ ^ 2) / (d ^ 2 - ‖imV y‖ ^ 2) ^ (3 / 2 : ℝ) := by
  set η := ‖imV y‖ with hηdef
  have hη0 : 0 ≤ η := norm_nonneg _
  have hm : 0 < d ^ 2 - η ^ 2 := by
    have : η ^ 2 < d ^ 2 := pow_lt_pow_left₀ hη hη0 two_ne_zero
    linarith
  have hQ : ∀ t ∈ Icc (0 : ℝ) 1, d ^ 2 - η ^ 2 ≤ (segQ p q y t).re := fun t ht => by
    rw [re_segQ]
    have := pow_le_pow_left₀ (hη0.trans hη.le) (hd t ht) 2
    linarith
  have hI := norm_segIntC_le hm hQ
  have hC : hnorm (crossC (ofRealV p - y) (ofRealV q - y)) ≤
      Real.sqrt (D ^ 2 + η ^ 2) * ‖q - p‖ := by
    rw [crossC_seg]
    refine (hnorm_crossC_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [hnorm_sub]
    refine Real.sqrt_le_sqrt ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    linarith
  rw [segFieldC, hnorm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv,
    ← Real.rpow_neg hm.le]
  calc |κ| * ‖segIntC p q y‖ * hnorm (crossC (ofRealV p - y) (ofRealV q - y))
      ≤ |κ| * (d ^ 2 - η ^ 2) ^ (-(3 / 2) : ℝ) * (Real.sqrt (D ^ 2 + η ^ 2) * ‖q - p‖) := by
        gcongr
        exact hnorm_nonneg _
    _ = _ := by ring

/-- The bound for the sup norm of `Fin 3 → ℂ`. -/
theorem segFieldC_bound_sup {κ d D : ℝ} {p q : Space} {y : CVec} (hη : ‖imV y‖ < d)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖reV y - seg p q t‖) (hD : ‖reV y - p‖ ≤ D) :
    ‖segFieldC κ p q y‖ ≤
      |κ| * ‖q - p‖ * Real.sqrt (D ^ 2 + ‖imV y‖ ^ 2) / (d ^ 2 - ‖imV y‖ ^ 2) ^ (3 / 2 : ℝ) :=
  (norm_le_hnorm _).trans (segFieldC_bound hη hd hD)

/-- At real points (`η = 0`) the bound has the real shape `|κ| |q - p| D / d³` (sanity). -/
theorem segFieldC_bound_real {κ d D : ℝ} {p q : Space} {y : CVec} (hy : imV y = 0) (hd0 : 0 < d)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖reV y - seg p q t‖) (hD : ‖reV y - p‖ ≤ D) :
    hnorm (segFieldC κ p q y) ≤ |κ| * ‖q - p‖ * D / d ^ 3 := by
  have h := segFieldC_bound (κ := κ) (by rw [hy, norm_zero]; exact hd0) hd hD
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  rw [hy, norm_zero] at h
  have e1 : Real.sqrt (D ^ 2 + 0 ^ 2) = D := by simp [Real.sqrt_sq hD0]
  have e2 : (d ^ 2 - 0 ^ 2) ^ (3 / 2 : ℝ) = d ^ 3 := by
    rw [show d ^ 2 - 0 ^ 2 = d ^ 2 by ring, ← Real.rpow_natCast d 2, ← Real.rpow_mul hd0.le]
    norm_num
  rwa [e1, e2] at h

/-! ## Agreement with the real closed form -/

/-- `ofRealV` is additive. -/
theorem ofRealV_sub (x z : Space) : ofRealV (x - z) = ofRealV x - ofRealV z := by
  ext i; simp

/-- `ofRealV` commutes with real scalars. -/
theorem ofRealV_smul (c : ℝ) (x : Space) : ofRealV (c • x) = (c : ℂ) • ofRealV x := by
  ext i; simp

/-- `ofRealV` maps the real cross product to the complex one. -/
theorem ofRealV_cross (u v : Space) : ofRealV (cross u v) = crossC (ofRealV u) (ofRealV v) := by
  ext i; fin_cases i <;> simp [cross, crossC, crossProduct]

/-- At real points `Q(t) = |a + t v|²` (real, nonnegative). -/
theorem segQ_ofReal (p q y : Space) (t : ℝ) :
    segQ p q (ofRealV y) t = ((‖(p - y) + t • (q - p)‖ ^ 2 : ℝ) : ℂ) := by
  rw [norm_sq_space]
  simp only [segQ, dotC, Fin.sum_univ_three, Pi.sub_apply, ofRealV_apply, seg, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  push_cast; ring

/-- `(r²)^{-3/2} = (r³)⁻¹` for `r ≥ 0`, as complex numbers (including `r = 0`). -/
theorem ofReal_sq_cpow {r : ℝ} (hr : 0 ≤ r) :
    ((r ^ 2 : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)) = (((r ^ 3)⁻¹ : ℝ) : ℂ) := by
  rw [neg_three_halves, ← Complex.ofReal_cpow (sq_nonneg r)]
  congr 1
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr, ← Real.rpow_natCast r 3, ← Real.rpow_neg hr]
  norm_num

/-- **At real points the complex field is the real closed form** (at every real point). -/
theorem segFieldC_ofReal (κ : ℝ) (p q y : Space) :
    segFieldC κ p q (ofRealV y) = ofRealV (segClosed κ p q y) := by
  have hc : segClosed κ p q y =
      (κ * ∫ t in (0 : ℝ)..1, (‖(p - y) + t • (q - p)‖ ^ 3)⁻¹) • cross (p - y) (q - y) := by
    have h := segField_eq_closed (4 * Real.pi * κ) 1 p q y
    have hk : 4 * Real.pi * κ * 1 / (4 * Real.pi) = κ := by
      field_simp
    rw [hk] at h
    rw [← h]
    unfold filamentField
    simp_rw [seg_kernel]
    rw [intervalIntegral.integral_smul_const, smul_smul]
    congr 2
  have hI : segIntC p q (ofRealV y) =
      (((∫ t in (0 : ℝ)..1, (‖(p - y) + t • (q - p)‖ ^ 3)⁻¹ : ℝ)) : ℂ) := by
    rw [segIntC, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [segQ_ofReal]
    exact ofReal_sq_cpow (norm_nonneg _)
  rw [hc, ofRealV_smul, ofRealV_cross, ofRealV_sub, ofRealV_sub, segFieldC, hI]
  push_cast
  rfl

/-! ## Holomorphy -/

/-- Coordinates of a point of the segment. -/
theorem seg_apply (p q : Space) (t : ℝ) (i : Fin 3) : seg p q t i = p i + t * (q i - p i) := by
  simp [seg]

/-- `Q(t)` is continuous in `t`. -/
theorem continuous_segQ (p q : Space) (y : CVec) : Continuous fun t => segQ p q y t := by
  simp only [segQ, dotC, Pi.sub_apply, ofRealV_apply, seg_apply]
  fun_prop

/-- The derivative of `y ↦ Q(t)`: `h ↦ -2 w·h`. -/
def segDQ (p q : Space) (y : CVec) (t : ℝ) : CVec →L[ℂ] ℂ :=
  ∑ i, (-2 * (ofRealV (seg p q t) i - y i)) • ContinuousLinearMap.proj i

/-- `y ↦ Q(t)` has derivative `segDQ`. -/
theorem hasFDerivAt_segQ (p q : Space) (y : CVec) (t : ℝ) :
    HasFDerivAt (fun y => segQ p q y t) (segDQ p q y t) y := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 3)), HasFDerivAt
      (fun y : CVec => (ofRealV (seg p q t) i - y i) * (ofRealV (seg p q t) i - y i))
      ((-2 * (ofRealV (seg p q t) i - y i)) • (ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ))
      y := by
    intro i _
    have hl : HasFDerivAt (fun y : CVec => ofRealV (seg p q t) i - y i)
        (-(ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ)) y := by
      exact (hasFDerivAt_apply i y).const_sub _
    refine (hl.mul hl).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun h => ?_
    simp
    ring
  have := HasFDerivAt.fun_sum h
  simpa [segQ, dotC, segDQ] using this

/-- The derivative of `y ↦ Q(t)^{-3/2}`. -/
def segDF (p q : Space) (y : CVec) (t : ℝ) : CVec →L[ℂ] ℂ :=
  ((-(3 / 2 : ℂ)) * segQ p q y t ^ (-(3 / 2 : ℂ) - 1)) • segDQ p q y t

/-- `y ↦ Q(t)^{-3/2}` has derivative `segDF` where `Re Q(t) > 0`. -/
theorem hasFDerivAt_segF {p q : Space} {y : CVec} {t : ℝ} (h : 0 < (segQ p q y t).re) :
    HasFDerivAt (fun y => segQ p q y t ^ (-(3 / 2 : ℂ))) (segDF p q y t) y := by
  have hd := (Complex.hasStrictDerivAt_cpow_const (c := -(3 / 2 : ℂ))
    (mem_slitPlane_iff.2 (Or.inl h))).hasDerivAt
  exact hd.comp_hasFDerivAt y (hasFDerivAt_segQ p q y t)

/-- `‖segDQ‖ ≤ 6R` when every coordinate of `w` is bounded by `R`. -/
theorem norm_segDQ_le {p q : Space} {y : CVec} {t R : ℝ}
    (hR : ∀ i, ‖ofRealV (seg p q t) i - y i‖ ≤ R) : ‖segDQ p q y t‖ ≤ 6 * R := by
  have hproj : ∀ i : Fin 3, ‖(ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ)‖ ≤ 1 := fun i =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
      simpa using norm_le_pi_norm h i
  have hterm : ∀ i : Fin 3,
      ‖(-2 * (ofRealV (seg p q t) i - y i)) • (ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ)‖ ≤
        2 * R := fun i => by
    rw [norm_smul, norm_mul, norm_neg]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR i)
    calc 2 * ‖ofRealV (seg p q t) i - y i‖ * ‖(ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ)‖
        ≤ 2 * R * 1 := by gcongr; exacts [hR i, hproj i]
      _ = 2 * R := by ring
  calc ‖segDQ p q y t‖ ≤ ∑ i : Fin 3,
        ‖(-2 * (ofRealV (seg p q t) i - y i)) • (ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 2 * R := Finset.sum_le_sum fun i _ => hterm i
    _ = 6 * R := by simp; ring

/-- `‖segDF‖ ≤ (3/2) m^{-5/2} (6R)` when `Re Q(t) ≥ m > 0` and the coordinates are `≤ R`. -/
theorem norm_segDF_le {p q : Space} {y : CVec} {t R m : ℝ} (hm : 0 < m)
    (hQ : m ≤ (segQ p q y t).re) (hR : ∀ i, ‖ofRealV (seg p q t) i - y i‖ ≤ R) :
    ‖segDF p q y t‖ ≤ 3 / 2 * m ^ (-(5 / 2) : ℝ) * (6 * R) := by
  have he : (-(3 / 2 : ℂ) - 1) = ((-(5 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [segDF, norm_smul, norm_mul, he, Complex.norm_cpow_real]
  have h1 : ‖(-(3 / 2 : ℂ))‖ = 3 / 2 := by
    rw [norm_neg]; norm_num
  rw [h1]
  have h2 : ‖segQ p q y t‖ ^ (-(5 / 2) : ℝ) ≤ m ^ (-(5 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hm (hQ.trans (re_le_norm_segQ p q y t)) (by norm_num)
  have h3 := norm_segDQ_le hR
  gcongr

/-- The coordinate radius used on the unit ball around `y₀`. -/
def segR (p q : Space) (y₀ : CVec) : ℝ := ‖p‖ + ‖q - p‖ + ‖y₀‖ + 1

/-- On the unit ball around `y₀`, `|seg t i - y i| ≤ segR` for `t ∈ [0,1]`. -/
theorem coord_le_segR {p q : Space} {y₀ y : CVec} (hy : dist y y₀ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 3) : ‖ofRealV (seg p q t) i - y i‖ ≤ segR p q y₀ := by
  have h1 : ‖ofRealV (seg p q t) i‖ ≤ ‖p‖ + ‖q - p‖ := by
    rw [ofRealV_apply, Complex.norm_real]
    refine (PiLp.norm_apply_le _ i).trans ?_
    unfold seg
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have := norm_nonneg (q - p)
    nlinarith [ht.2]
  have h2 : ‖y i‖ ≤ ‖y₀‖ + 1 := by
    refine (norm_le_pi_norm y i).trans ?_
    have := norm_le_norm_add_norm_sub' y y₀
    rw [dist_eq_norm] at hy
    linarith
  calc ‖ofRealV (seg p q t) i - y i‖ ≤ ‖ofRealV (seg p q t) i‖ + ‖y i‖ := norm_sub_le _ _
    _ ≤ segR p q y₀ := by unfold segR; linarith

/-- Lipschitz estimate: `|Q(y,t) - Q(y₀,t)| ≤ 6R |y - y₀|` on the unit ball. -/
theorem norm_segQ_sub_le {p q : Space} {y₀ y : CVec} (hy : dist y y₀ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segQ p q y t - segQ p q y₀ t‖ ≤ 6 * segR p q y₀ * dist y y₀ := by
  set c := ofRealV (seg p q t)
  have he : segQ p q y t - segQ p q y₀ t =
      ∑ i, (y₀ i - y i) * ((c i - y i) + (c i - y₀ i)) := by
    simp only [segQ, dotC, Fin.sum_univ_three, Pi.sub_apply, c]; ring
  have h0 : dist y₀ y₀ < 1 := by simp
  rw [he]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i : Fin 3, ‖(y₀ i - y i) * ((c i - y i) + (c i - y₀ i))‖ ≤
      dist y y₀ * (2 * segR p q y₀) := fun i => by
    rw [norm_mul]
    have ha : ‖y₀ i - y i‖ ≤ dist y y₀ := by
      rw [dist_comm, dist_eq_norm]; exact norm_le_pi_norm (y₀ - y) i
    have hb : ‖(c i - y i) + (c i - y₀ i)‖ ≤ 2 * segR p q y₀ := by
      have := coord_le_segR (p := p) (q := q) hy ht i
      have := coord_le_segR (p := p) (q := q) h0 ht i
      refine (norm_add_le _ _).trans ?_
      linarith
    exact mul_le_mul ha hb (norm_nonneg _) dist_nonneg
  calc ∑ i : Fin 3, ‖(y₀ i - y i) * ((c i - y i) + (c i - y₀ i))‖
      ≤ ∑ _i : Fin 3, dist y y₀ * (2 * segR p q y₀) := Finset.sum_le_sum fun i _ => hterm i
    _ = 6 * segR p q y₀ * dist y y₀ := by simp; ring

/-- `segR > 0`. -/
theorem segR_pos (p q : Space) (y₀ : CVec) : 0 < segR p q y₀ := by
  unfold segR; positivity

/-- A ball around each point of `segDomain` on which `Re Q ≥ m > 0` uniformly. -/
theorem segDomain_ball {p q : Space} {y₀ : CVec} (hy₀ : y₀ ∈ segDomain p q) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ m > 0, ∀ y ∈ Metric.ball y₀ ε, ∀ t ∈ Icc (0 : ℝ) 1,
      m ≤ (segQ p q y t).re := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (Complex.continuous_re.comp (continuous_segQ p q y₀)).continuousOn
  set m₀ := (segQ p q y₀ t₀).re
  have hm₀ : 0 < m₀ := hy₀ t₀ ht₀
  have hR := segR_pos p q y₀
  set R := segR p q y₀
  refine ⟨min 1 (m₀ / (12 * R)), by positivity, min_le_left _ _, m₀ / 2, by positivity, ?_⟩
  intro y hy t ht
  rw [Metric.mem_ball, lt_min_iff] at hy
  have hL := norm_segQ_sub_le (p := p) (q := q) hy.1 ht
  have hmt : m₀ ≤ (segQ p q y₀ t).re := hmin ht
  have h6 : 6 * R * dist y y₀ ≤ m₀ / 2 := by
    have := hy.2
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have hre : (segQ p q y₀ t).re - (segQ p q y t).re ≤ ‖segQ p q y t - segQ p q y₀ t‖ := by
    have := Complex.abs_re_le_norm (segQ p q y t - segQ p q y₀ t)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le ((segQ p q y t).re - (segQ p q y₀ t).re)]
  linarith

/-- `segDomain` is open. -/
theorem isOpen_segDomain (p q : Space) : IsOpen (segDomain p q) := by
  refine Metric.isOpen_iff.2 fun y₀ hy₀ => ?_
  obtain ⟨ε, hε, -, m, hm, h⟩ := segDomain_ball hy₀
  exact ⟨ε, hε, fun y hy t ht => hm.trans_le (h y hy t ht)⟩

/-- `t ↦ Q(t)^c` is continuous on `[0,1]` for `y` in the domain. -/
theorem continuousOn_segQ_cpow {p q : Space} {y : CVec} (hy : y ∈ segDomain p q) (c : ℂ) :
    ContinuousOn (fun t => segQ p q y t ^ c) (Icc 0 1) := fun t ht =>
  ((continuousAt_cpow_const (mem_slitPlane_iff.2 (Or.inl (hy t ht)))).comp
    (continuous_segQ p q y).continuousAt).continuousWithinAt

/-- `t ↦ segDQ p q y t` is continuous. -/
theorem continuous_segDQ (p q : Space) (y : CVec) : Continuous fun t => segDQ p q y t := by
  unfold segDQ
  refine continuous_finsetSum _ fun i _ => ?_
  have h : Continuous fun t : ℝ => -2 * (ofRealV (seg p q t) i - y i) := by
    simp only [ofRealV_apply, seg_apply]
    fun_prop
  exact h.smul continuous_const

/-- **The scalar integral is holomorphic** at every point of `segDomain`. -/
theorem differentiableAt_segIntC {p q : Space} {y₀ : CVec} (hy₀ : y₀ ∈ segDomain p q) :
    DifferentiableAt ℂ (segIntC p q) y₀ := by
  obtain ⟨ε, hε, hε1, m, hm, hball⟩ := segDomain_ball hy₀
  have hdom : ∀ y ∈ Metric.ball y₀ ε, y ∈ segDomain p q := fun y hy t ht =>
    hm.trans_le (hball y hy t ht)
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have hR : ∀ y ∈ Metric.ball y₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      ‖ofRealV (seg p q t) i - y i‖ ≤ segR p q y₀ := fun y hy t ht i =>
    coord_le_segR (lt_of_lt_of_le (Metric.mem_ball.1 hy) hε1) ht i
  have hy₀b : y₀ ∈ Metric.ball y₀ ε := Metric.mem_ball_self hε
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 1)
    (F := fun y t => segQ p q y t ^ (-(3 / 2 : ℂ))) (F' := fun y t => segDF p q y t)
    (x₀ := y₀) (bound := fun _ => 3 / 2 * m ^ (-(5 / 2) : ℝ) * (6 * segR p q y₀))
    (Metric.ball_mem_nhds y₀ hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ hε) fun y hy =>
      ((continuousOn_segQ_cpow (hdom y hy) _).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    ((continuousOn_segQ_cpow hy₀ _).intervalIntegrable_of_Icc zero_le_one)
    ((((continuousOn_const.mul (continuousOn_segQ_cpow hy₀ _)).smul
      (continuous_segDQ p q y₀).continuousOn).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht y hy =>
      norm_segDF_le hm (hball y hy t (hsub ht)) (hR y hy t (hsub ht)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht y hy =>
      hasFDerivAt_segF (hm.trans_le (hball y hy t (hsub ht))))
  exact key.differentiableAt

/-- The cross-product factor is polynomial, hence holomorphic. -/
theorem differentiable_crossC_seg (p q : Space) :
    Differentiable ℂ fun y : CVec => crossC (ofRealV p - y) (ofRealV q - y) := by
  intro y
  refine differentiableAt_pi.2 fun i => ?_
  match i with
  | 0 => simp only [crossC_zero, Pi.sub_apply]; fun_prop
  | 1 => simp only [crossC_one, Pi.sub_apply]; fun_prop
  | 2 => simp only [crossC_two, Pi.sub_apply]; fun_prop

/-- **Holomorphy of the complexified segment field** on `segDomain p q`. -/
theorem segFieldC_differentiableOn (κ : ℝ) (p q : Space) :
    DifferentiableOn ℂ (segFieldC κ p q) (segDomain p q) := fun y hy =>
  (((differentiableAt_segIntC hy).const_mul (κ : ℂ)).smul
    (differentiable_crossC_seg p q y)).differentiableWithinAt

/-- Holomorphy on the region of the bound (`|Im y| < dist(Re y, segment)`). -/
theorem segFieldC_differentiableOn_boundRegion (κ : ℝ) (p q : Space) :
    DifferentiableOn ℂ (segFieldC κ p q)
      {y : CVec | ∀ t ∈ Icc (0 : ℝ) 1, ‖imV y‖ < ‖reV y - seg p q t‖} :=
  (segFieldC_differentiableOn κ p q).mono (boundRegion_subset_segDomain p q)

/-- Real points off the segment lie in the domain (sanity). -/
theorem segDomain_ofReal {p q y : Space} (hy : ∀ t ∈ Icc (0 : ℝ) 1, y ≠ seg p q t) :
    ofRealV y ∈ segDomain p q := by
  refine boundRegion_subset_segDomain p q fun t ht => ?_
  have h1 : imV (ofRealV y) = 0 := by ext i; simp
  have h2 : reV (ofRealV y) = y := by ext i; simp
  rw [h1, h2, norm_zero, norm_pos_iff, sub_ne_zero]
  exact hy t ht

/-- Rejected fixture: the endpoint `p` is not in the domain (`Q(0) = 0` there). -/
theorem not_mem_segDomain_endpoint (p q : Space) : ofRealV p ∉ segDomain p q := by
  intro h
  have := h 0 ⟨le_rfl, zero_le_one⟩
  rw [re_segQ] at this
  have h1 : imV (ofRealV p) = 0 := by ext i; simp
  have h2 : reV (ofRealV p) = p := by ext i; simp
  simp [h1, h2, seg] at this

end PlasmaLean.Fields.BiotSavartComplex
