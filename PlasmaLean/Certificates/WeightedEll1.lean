/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The weighted sequence space ℓ¹_ν(ℤ) and its Banach-algebra estimate

For `ν ≥ 1`, the space `ℓ¹_ν(ℤ)` consists of real sequences `a` with
`‖a‖_ν = ∑ₖ |aₖ| ν^|k| < ∞`. It is the natural home of Fourier coefficients of
functions analytic on a strip (`ν > 1`) or with absolutely convergent Fourier series
(`ν = 1`, in which case `‖a‖₁` bounds the sup norm of `∑ aₖ e^{ikx}`).

**Model.** We realise `ℓ¹_ν(ℤ)` isometrically as Mathlib's `lp (fun _ : ℤ => ℝ) 1`, a
sequence `a` being represented by its *scaled* sequence `xₖ = aₖ ν^|k|`. Thus
completeness and the normed-space structure are inherited from Mathlib, the norm is
literally `∑ |xₖ|` (`norm_eq_tsum_abs`), and the Fourier coefficients are recovered by
`coeff ν x k = xₖ / ν^|k|` (`norm_eq_tsum_coeff`). For `ν = 1` the two coincide.

**Convolution.** The discrete convolution `(a * b)ₖ = ∑ⱼ aⱼ b_{k-j}` is transported to the
scaled model (`conv`). Because `ν^|k| ≤ ν^|j| ν^|k-j|` for `ν ≥ 1`, it satisfies the
Banach-algebra estimate `‖a * b‖_ν ≤ ‖a‖_ν ‖b‖_ν` (`norm_conv_le`), with constant `1`.
Even sequences (`a_{-k} = aₖ`) are exactly cosine series, so the cosine-series product
`u(x) v(x)` is the restriction of this convolution; no separate cosine constant is needed.

**Truncation.** Splitting the norm into a finite block plus a tail (`norm_eq_sum_add_tail`),
finitely supported elements (`norm_eq_sum_of_support`), finite-sum formulas for
convolution with a finitely supported factor (`conv_eq_sum_of_support`), and the support of
a product of truncated sequences (`conv_support`), which is what makes the residual of a
finite Fourier candidate an exact finite computation.
-/
public section
noncomputable section

namespace PlasmaLean.Certificates

open scoped BigOperators

/-- The underlying unweighted space `ℓ¹(ℤ)` of real sequences. -/
abbrev Ell1Z : Type := lp (fun _ : ℤ => ℝ) 1

/-- The weighted space `ℓ¹_ν(ℤ)`, modelled by scaled sequences `aₖ ν^|k|` in `ℓ¹(ℤ)`.
The parameter only affects `coeff`, `conv`, and the associated lemmas. -/
abbrev WeightedEll1 (_ν : ℝ) : Type := Ell1Z

/-- The weight `ν^|k|`. -/
@[expose] def nuWeight (ν : ℝ) (k : ℤ) : ℝ := ν ^ k.natAbs

/-- The Fourier coefficient `aₖ = xₖ / ν^|k|` of an element `x` of the scaled model. -/
@[expose] def coeff (ν : ℝ) (x : WeightedEll1 ν) (k : ℤ) : ℝ := x k / nuWeight ν k

/-- The weight is positive for `ν > 0`. -/
theorem nuWeight_pos {ν : ℝ} (hν : 0 < ν) (k : ℤ) : 0 < nuWeight ν k := by
  unfold nuWeight; positivity

/-- The weight is at least `1` for `ν ≥ 1`. -/
theorem one_le_nuWeight {ν : ℝ} (hν : 1 ≤ ν) (k : ℤ) : 1 ≤ nuWeight ν k := by
  unfold nuWeight; exact one_le_pow₀ hν

/-- Submultiplicativity of the weight, the source of the Banach-algebra property. -/
theorem nuWeight_le_mul {ν : ℝ} (hν : 1 ≤ ν) (j k : ℤ) :
    nuWeight ν k ≤ nuWeight ν j * nuWeight ν (k - j) := by
  unfold nuWeight
  rw [← pow_add]
  apply pow_le_pow_right₀ hν
  have := Int.natAbs_add_le j (k - j)
  simpa using this

/-- The weight is trivial for `ν = 1`. -/
@[simp] theorem nuWeight_one (k : ℤ) : nuWeight 1 k = 1 := by simp [nuWeight]

/-- For `ν = 1` the coefficients are the entries themselves. -/
@[simp] theorem coeff_one (x : WeightedEll1 1) (k : ℤ) : coeff 1 x k = x k := by
  simp [coeff]

/-! ### Norm formulas -/

/-- Membership of a real sequence in `ℓ¹` is absolute summability. -/
theorem memℓp_one_iff (a : ℤ → ℝ) : Memℓp a 1 ↔ Summable fun k => |a k| := by
  rw [memℓp_gen_iff (by norm_num)]
  simp [Real.norm_eq_abs]

/-- Entries of an element of `ℓ¹(ℤ)` are absolutely summable. -/
theorem summable_abs (x : Ell1Z) : Summable fun k => |x k| :=
  (memℓp_one_iff _).1 (lp.memℓp x)

/-- The `ℓ¹` norm is the sum of the absolute values of the entries. -/
theorem norm_eq_tsum_abs (x : Ell1Z) : ‖x‖ = ∑' k, |x k| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp [Real.norm_eq_abs]

/-- The weighted norm in terms of Fourier coefficients: `‖x‖ = ∑ |aₖ| ν^|k|`. -/
theorem norm_eq_tsum_coeff {ν : ℝ} (hν : 0 < ν) (x : WeightedEll1 ν) :
    ‖x‖ = ∑' k, |coeff ν x k| * nuWeight ν k := by
  rw [norm_eq_tsum_abs]
  congr 1; funext k
  have := nuWeight_pos hν k
  rw [coeff, abs_div, abs_of_pos this, div_mul_cancel₀ _ this.ne']

/-- Each entry is bounded by the norm. -/
theorem abs_apply_le_norm (x : Ell1Z) (k : ℤ) : |x k| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (E := fun _ : ℤ => ℝ) (p := 1) one_ne_zero x k
  simpa [Real.norm_eq_abs] using this

/-- A weighted sequence with `∑ |aₖ| ν^|k| < ∞` defines an element of `ℓ¹_ν`. -/
@[expose] def ofCoeff {ν : ℝ} (hν : 0 < ν) (a : ℤ → ℝ)
    (h : Summable fun k => |a k| * nuWeight ν k) : WeightedEll1 ν :=
  ⟨fun k => a k * nuWeight ν k, (memℓp_one_iff _).2 (h.congr fun k => by
    rw [abs_mul, abs_of_pos (nuWeight_pos hν k)])⟩

/-- `ofCoeff` has the prescribed Fourier coefficients. -/
theorem coeff_ofCoeff {ν : ℝ} (hν : 0 < ν) (a : ℤ → ℝ)
    (h : Summable fun k => |a k| * nuWeight ν k) (k : ℤ) :
    coeff ν (ofCoeff hν a h) k = a k := by
  have := (nuWeight_pos hν k).ne'
  simp [coeff, ofCoeff, this]

/-- The norm splits into a finite block and a tail. -/
theorem norm_eq_sum_add_tail (x : Ell1Z) (s : Finset ℤ) :
    ‖x‖ = ∑ k ∈ s, |x k| + ∑' k, (if k ∈ s then 0 else |x k|) := by
  have hs := summable_abs x
  have h1 : Summable fun k => (if k ∈ s then |x k| else 0) :=
    hs.of_nonneg_of_le (fun k => by split_ifs <;> simp) (fun k => by split_ifs <;> simp)
  have h2 : Summable fun k => (if k ∈ s then 0 else |x k|) :=
    hs.of_nonneg_of_le (fun k => by split_ifs <;> simp) (fun k => by split_ifs <;> simp)
  rw [norm_eq_tsum_abs]
  have hsplit : (fun k => |x k|) =
      fun k => (if k ∈ s then |x k| else 0) + (if k ∈ s then 0 else |x k|) := by
    funext k; split_ifs <;> simp
  rw [hsplit, h1.tsum_add h2]
  congr 1
  rw [tsum_eq_sum (s := s) (fun k hk => by simp [hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [hk]

/-- A finite block of entries is bounded by the norm. -/
theorem sum_abs_le_norm (x : Ell1Z) (s : Finset ℤ) : ∑ k ∈ s, |x k| ≤ ‖x‖ := by
  rw [norm_eq_sum_add_tail x s]
  have : 0 ≤ ∑' k, (if k ∈ s then 0 else |x k|) :=
    tsum_nonneg fun k => by split_ifs <;> simp
  linarith

/-- Finitely supported elements: the norm is a finite sum. -/
theorem norm_eq_sum_of_support (x : Ell1Z) (s : Finset ℤ) (hx : ∀ k ∉ s, x k = 0) :
    ‖x‖ = ∑ k ∈ s, |x k| := by
  rw [norm_eq_tsum_abs, tsum_eq_sum (s := s) (fun k hk => by simp [hx k hk])]

/-! ### Convolution -/

/-- The convolution of the coefficient sequences, expressed on scaled entries:
`(x ⋆ y)ₖ = ν^|k| ∑ⱼ (xⱼ/ν^|j|)(y_{k-j}/ν^|k-j|)`. -/
@[expose] def convFun (ν : ℝ) (x y : ℤ → ℝ) (k : ℤ) : ℝ :=
  nuWeight ν k * ∑' j, (x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))

/-- Pointwise domination of the convolution summand. -/
theorem abs_conv_summand_le {ν : ℝ} (hν : 1 ≤ ν) (x y : ℤ → ℝ) (k j : ℤ) :
    nuWeight ν k * |(x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))| ≤
      |x j| * |y (k - j)| := by
  have h1 := one_le_nuWeight hν j
  have h2 := one_le_nuWeight hν (k - j)
  have hk := nuWeight_le_mul hν j k
  have hj0 : (0:ℝ) < nuWeight ν j := by linarith
  have hkj0 : (0:ℝ) < nuWeight ν (k - j) := by linarith
  have hq : nuWeight ν k / (nuWeight ν j * nuWeight ν (k - j)) ≤ 1 :=
    div_le_one_of_le₀ hk (by positivity)
  have hq0 : 0 ≤ nuWeight ν k / (nuWeight ν j * nuWeight ν (k - j)) :=
    div_nonneg (nuWeight_pos (by linarith) k).le (by positivity)
  calc nuWeight ν k * |(x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))|
      = nuWeight ν k / (nuWeight ν j * nuWeight ν (k - j)) * (|x j| * |y (k - j)|) := by
        rw [abs_mul, abs_div, abs_div, abs_of_pos hj0, abs_of_pos hkj0]
        field_simp
    _ ≤ 1 * (|x j| * |y (k - j)|) := by gcongr
    _ = |x j| * |y (k - j)| := one_mul _

/-- The product family `|xⱼ| |y_{k-j}|` is summable in `j`. -/
theorem summable_abs_mul_shift (x y : Ell1Z) (k : ℤ) :
    Summable fun j => |x j| * |y (k - j)| := by
  refine (summable_abs x).mul_right ‖y‖ |>.of_nonneg_of_le (fun j => by positivity) ?_
  intro j
  exact mul_le_mul_of_nonneg_left (abs_apply_le_norm y _) (abs_nonneg _)

/-- The convolution summand is absolutely summable. -/
theorem summable_conv_summand {ν : ℝ} (hν : 1 ≤ ν) (x y : Ell1Z) (k : ℤ) :
    Summable fun j => (x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j)) := by
  refine Summable.of_norm_bounded (summable_abs_mul_shift x y k) fun j => ?_
  have h := abs_conv_summand_le hν x y k j
  have hk := one_le_nuWeight hν k
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg ((x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j)))]

/-- Entrywise bound of the convolution by the unweighted convolution of absolute values. -/
theorem abs_convFun_le {ν : ℝ} (hν : 1 ≤ ν) (x y : Ell1Z) (k : ℤ) :
    |convFun ν x y k| ≤ ∑' j, |x j| * |y (k - j)| := by
  have hk0 := (nuWeight_pos (by linarith) k).le
  have hs := summable_conv_summand hν x y k
  unfold convFun
  rw [abs_mul, abs_of_nonneg hk0]
  calc nuWeight ν k * |∑' j, (x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))|
      ≤ nuWeight ν k * ∑' j, |(x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))| := by
        gcongr
        have habs : Summable fun j =>
            ‖(x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))‖ := by
          simp only [Real.norm_eq_abs]; exact hs.abs
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm habs
    _ = ∑' j, nuWeight ν k * |(x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j))| :=
        (tsum_mul_left).symm
    _ ≤ ∑' j, |x j| * |y (k - j)| :=
        (hs.abs.mul_left _).tsum_le_tsum (abs_conv_summand_le hν x y k)
          (summable_abs_mul_shift x y k)

/-- The double series `∑ₖ ∑ⱼ |xⱼ| |y_{k-j}|` sums to `‖x‖ ‖y‖` (Cauchy product over `ℤ`). -/
theorem hasSum_abs_conv (x y : Ell1Z) :
    HasSum (fun k => ∑' j, |x j| * |y (k - j)|) (‖x‖ * ‖y‖) := by
  have hx := summable_abs x
  have hy := summable_abs y
  have hprod : Summable fun p : ℤ × ℤ => |x p.1| * |y p.2| :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun j => |x j|) (g := fun j => |y j|)
      (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
      (by simpa only [Real.norm_eq_abs, abs_abs] using hy)
  have hHas : HasSum (fun p : ℤ × ℤ => |x p.1| * |y p.2|) (‖x‖ * ‖y‖) := by
    rw [norm_eq_tsum_abs x, norm_eq_tsum_abs y]
    exact hx.hasSum.mul hy.hasSum hprod
  -- reindex `(k, j) ↦ (j, k - j)`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  have hHas' : HasSum (fun p : ℤ × ℤ => |x p.2| * |y (p.1 - p.2)|) (‖x‖ * ‖y‖) := by
    exact (e.hasSum_iff (f := fun p : ℤ × ℤ => |x p.1| * |y p.2|)).2 hHas
  exact hHas'.prod_fiberwise fun k => (hHas'.summable.prod_factor k).hasSum

/-- The convolution of two `ℓ¹_ν` elements, as an element of `ℓ¹_ν` (requires `ν ≥ 1`;
for other `ν` the definition is junk). -/
@[expose] def conv (ν : ℝ) (x y : WeightedEll1 ν) : WeightedEll1 ν :=
  if hν : 1 ≤ ν then
    ⟨convFun ν x y, (memℓp_one_iff _).2 <|
      (hasSum_abs_conv x y).summable.of_nonneg_of_le (fun _ => abs_nonneg _)
        (abs_convFun_le hν x y)⟩
  else 0

/-- Coordinates of the convolution for `ν ≥ 1`. -/
theorem conv_apply {ν : ℝ} (hν : 1 ≤ ν) (x y : WeightedEll1 ν) (k : ℤ) :
    conv ν x y k = convFun ν x y k := by
  simp [conv, hν]

/-- **Banach-algebra estimate** `‖x ⋆ y‖_ν ≤ ‖x‖_ν ‖y‖_ν` for `ν ≥ 1`. -/
theorem norm_conv_le {ν : ℝ} (hν : 1 ≤ ν) (x y : WeightedEll1 ν) :
    ‖conv ν x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_tsum_abs, ← (hasSum_abs_conv x y).tsum_eq]
  refine (summable_abs _).tsum_le_tsum (fun k => ?_) (hasSum_abs_conv x y).summable
  rw [conv_apply hν]
  exact abs_convFun_le hν x y k

/-- For `ν = 1`, convolution is the plain discrete convolution. -/
theorem conv_one_apply (x y : WeightedEll1 1) (k : ℤ) :
    conv 1 x y k = ∑' j, x j * y (k - j) := by
  rw [conv_apply le_rfl]
  simp [convFun]

/-- Convolution is commutative. -/
theorem conv_comm {ν : ℝ} (x y : WeightedEll1 ν) : conv ν x y = conv ν y x := by
  by_cases hν : 1 ≤ ν
  · ext k
    rw [conv_apply hν, conv_apply hν]
    unfold convFun
    congr 1
    rw [← (Equiv.subLeft k).tsum_eq]
    congr 1; funext j
    simp [Equiv.subLeft, mul_comm]
  · simp [conv, hν]

/-- Convolution is additive in the first argument. -/
theorem conv_add_left {ν : ℝ} (x y z : WeightedEll1 ν) :
    conv ν (x + y) z = conv ν x z + conv ν y z := by
  by_cases hν : 1 ≤ ν
  · ext k
    rw [lp.coeFn_add, Pi.add_apply, conv_apply hν, conv_apply hν, conv_apply hν]
    unfold convFun
    rw [← mul_add, ← (summable_conv_summand hν x z k).tsum_add
      (summable_conv_summand hν y z k)]
    congr 2; funext j
    rw [lp.coeFn_add, Pi.add_apply]; ring
  · simp [conv, hν]

/-- Convolution is additive in the second argument. -/
theorem conv_add_right {ν : ℝ} (x y z : WeightedEll1 ν) :
    conv ν x (y + z) = conv ν x y + conv ν x z := by
  rw [conv_comm, conv_add_left, conv_comm y, conv_comm z]

/-- Convolution commutes with negation in the first argument. -/
theorem conv_neg_left {ν : ℝ} (x z : WeightedEll1 ν) : conv ν (-x) z = -conv ν x z := by
  have h := conv_add_left x (-x) z
  rw [add_neg_cancel] at h
  have h0 : conv ν 0 z = 0 := by
    have := conv_add_left (0 : WeightedEll1 ν) 0 z
    simpa using this
  rw [h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- Convolution is subtractive in the first argument. -/
theorem conv_sub_left {ν : ℝ} (x y z : WeightedEll1 ν) :
    conv ν (x - y) z = conv ν x z - conv ν y z := by
  rw [sub_eq_add_neg, conv_add_left, conv_neg_left, ← sub_eq_add_neg]

/-- Convolution is subtractive in the second argument. -/
theorem conv_sub_right {ν : ℝ} (x y z : WeightedEll1 ν) :
    conv ν x (y - z) = conv ν x y - conv ν x z := by
  rw [conv_comm, conv_sub_left, conv_comm y, conv_comm z]

/-- Difference of squares, the algebraic identity behind the quadratic `Z₂` bound. -/
theorem conv_self_sub_conv_self {ν : ℝ} (a b : WeightedEll1 ν) :
    conv ν a a - conv ν b b = conv ν (a + b) (a - b) := by
  rw [conv_add_left, conv_sub_right, conv_sub_right, conv_comm b a]
  abel

/-! ### Truncation -/

/-- Convolution with a factor supported on a finite set is a finite sum. -/
theorem conv_eq_sum_of_support {ν : ℝ} (hν : 1 ≤ ν) (x y : WeightedEll1 ν) (s : Finset ℤ)
    (hx : ∀ j ∉ s, x j = 0) (k : ℤ) :
    conv ν x y k = nuWeight ν k *
      ∑ j ∈ s, (x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j)) := by
  rw [conv_apply hν, convFun, tsum_eq_sum (s := s) (fun j hj => by simp [hx j hj])]

/-- Support of a product of truncated sequences: if `xⱼ = 0` for `|j| > N` and
`yⱼ = 0` for `|j| > M`, then `(x ⋆ y)ₖ = 0` for `|k| > N + M`. -/
theorem conv_support {ν : ℝ} (x y : WeightedEll1 ν) {N M : ℕ}
    (hx : ∀ j : ℤ, N < j.natAbs → x j = 0) (hy : ∀ j : ℤ, M < j.natAbs → y j = 0)
    (k : ℤ) (hk : N + M < k.natAbs) : conv ν x y k = 0 := by
  by_cases hν : 1 ≤ ν
  · rw [conv_apply hν, convFun]
    have : ∀ j, (x j / nuWeight ν j) * (y (k - j) / nuWeight ν (k - j)) = 0 := by
      intro j
      by_cases hj : N < j.natAbs
      · simp [hx j hj]
      · have hkj : M < (k - j).natAbs := by
          have := Int.natAbs_add_le j (k - j)
          simp at this
          omega
        simp [hy _ hkj]
    simp [this]
  · simp [conv, hν]

/-! ### Finite blocks and point evaluation -/

/-- **Finite block operator bound.** If every column of the matrix `C` (rows `S`,
columns `S₂`) has absolute column sum at most `c`, then the block maps the `ℓ¹` mass of
`h` on `S₂` to at most `c` times that mass. This is the `ν = 1` operator-norm bound used
for the computed blocks `Z₀`, `Z₁` of a radii-polynomial certificate. -/
theorem sum_abs_matrix_mul_le (C : ℤ → ℤ → ℝ) (h : ℤ → ℝ) (S S₂ : Finset ℤ) {c : ℝ}
    (hc : ∀ m ∈ S₂, ∑ k ∈ S, |C k m| ≤ c) :
    ∑ k ∈ S, |∑ m ∈ S₂, C k m * h m| ≤ c * ∑ m ∈ S₂, |h m| := by
  calc ∑ k ∈ S, |∑ m ∈ S₂, C k m * h m| ≤ ∑ k ∈ S, ∑ m ∈ S₂, |C k m| * |h m| := by
        gcongr with k hk
        exact (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
    _ = ∑ m ∈ S₂, (∑ k ∈ S, |C k m|) * |h m| := by
        rw [Finset.sum_comm]; simp [Finset.sum_mul]
    _ ≤ ∑ m ∈ S₂, c * |h m| := by
        gcongr with m hm; exact hc m hm
    _ = c * ∑ m ∈ S₂, |h m| := by rw [Finset.mul_sum]

/-- Point evaluation of the cosine form `∑ₖ xₖ cos(kθ)` of a sequence. For an even
sequence (`x₋ₖ = xₖ`) this is exactly the real `2π`-periodic function `∑ₖ xₖ e^{ikθ}`. -/
@[expose] def evalCos (x : Ell1Z) (θ : ℝ) : ℝ := ∑' k, x k * Real.cos (k * θ)

/-- The cosine series of an `ℓ¹` sequence converges absolutely. -/
theorem summable_evalCos (x : Ell1Z) (θ : ℝ) :
    Summable fun k : ℤ => x k * Real.cos (k * θ) := by
  refine Summable.of_norm_bounded (summable_abs x) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- **Sup-norm bound.** `|∑ₖ xₖ cos(kθ)| ≤ ‖x‖₁` for every `θ`. -/
theorem abs_evalCos_le (x : Ell1Z) (θ : ℝ) : |evalCos x θ| ≤ ‖x‖ := by
  rw [norm_eq_tsum_abs, evalCos]
  have h1 : Summable fun k : ℤ => ‖x k * Real.cos (k * θ)‖ := by
    refine (summable_abs x).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  calc |∑' k, x k * Real.cos (k * θ)| ≤ ∑' k : ℤ, ‖x k * Real.cos (k * θ)‖ := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm h1
    _ ≤ ∑' k, |x k| := h1.tsum_le_tsum (fun k => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) (summable_abs x)

/-- Point evaluation is additive. -/
theorem evalCos_sub (x y : Ell1Z) (θ : ℝ) :
    evalCos (x - y) θ = evalCos x θ - evalCos y θ := by
  unfold evalCos
  rw [← (summable_evalCos x θ).tsum_sub (summable_evalCos y θ)]
  congr 1; funext k
  rw [lp.coeFn_sub, Pi.sub_apply]; ring

/-! ### Reflection `k ↦ -k` -/

/-- The reflection `(R x)ₖ = x₋ₖ`; even sequences (cosine series) are its fixed points. -/
@[expose] def refl (x : Ell1Z) : Ell1Z :=
  ⟨fun k => x (-k), (memℓp_one_iff _).2 <|
    (Equiv.neg ℤ).summable_iff.2 (summable_abs x)⟩

/-- Coordinates of the reflection. -/
theorem refl_apply (x : Ell1Z) (k : ℤ) : refl x k = x (-k) := rfl

/-- The weight is even. -/
theorem nuWeight_neg (ν : ℝ) (k : ℤ) : nuWeight ν (-k) = nuWeight ν k := by
  simp [nuWeight]

/-- Reflection is an isometry. -/
theorem norm_refl (x : Ell1Z) : ‖refl x‖ = ‖x‖ := by
  rw [norm_eq_tsum_abs, norm_eq_tsum_abs]
  exact (Equiv.neg ℤ).tsum_eq (fun k => |x k|)

/-- Reflection is additive. -/
theorem refl_sub (x y : Ell1Z) : refl (x - y) = refl x - refl y := by
  ext k; simp [refl_apply]

/-- Reflection of zero. -/
theorem refl_zero : refl 0 = 0 := by
  ext k; simp [refl_apply]

/-- Reflection commutes with convolution. -/
theorem conv_refl {ν : ℝ} (x y : WeightedEll1 ν) :
    conv ν (refl x) (refl y) = refl (conv ν x y) := by
  by_cases hν : 1 ≤ ν
  · ext k
    rw [refl_apply, conv_apply hν, conv_apply hν]
    unfold convFun
    rw [nuWeight_neg]
    congr 1
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; funext j
    simp only [Equiv.neg_apply, refl_apply, neg_neg, nuWeight_neg]
    have h1 : -(k - -j) = -k - j := by ring
    have h2 : k - -j = -(-k - j) := by ring
    rw [h1, h2, nuWeight_neg]
  · ext k; simp [conv, hν, refl_apply]

end PlasmaLean.Certificates
