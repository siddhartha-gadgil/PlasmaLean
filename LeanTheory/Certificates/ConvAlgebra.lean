/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.FourierRegularity
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# `ℓ¹(ℤ)` as a commutative Banach algebra, and its exponential

The space `Ell1Z = ℓ¹(ℤ)` with discrete convolution `conv 1` is a commutative unital
Banach algebra (the Wiener algebra of absolutely convergent Fourier series). We record
this as **scoped** instances (namespace `LeanTheory.Certificates.ConvAlgebra`):
`x * y = conv 1 x y`, `1 = δ₀`, giving `NormedCommRing`, `NormOneClass`,
`NormedAlgebra ℝ`. The additive, normed and module structures are the existing ones of
Mathlib's `lp`, so no diamonds are introduced. Associativity is the reindexing
`(j, i) ↦ (i, j - i)` of an absolutely summable double series (`conv_assoc`).

**Exponential.** Mathlib's `NormedSpace.exp` then applies. We prove:
* `norm_exp_le`: `‖e^x‖ ≤ e^{‖x‖}`;
* `norm_exp_sub_exp_le`: `‖e^x - e^y‖ ≤ e^ρ ‖x - y‖` when `‖x‖, ‖y‖ ≤ ρ` (mean value);
* `norm_exp_sub_exp_sub_mul_le`: the second-order bound
  `‖e^φ - e^ψ - e^{ū} (φ - ψ)‖ ≤ r e^{‖ū‖ + r} ‖φ - ψ‖` for `φ, ψ ∈ B̄(ū, r)`, which is the
  `Z₂` estimate of a radii-polynomial certificate with exponential nonlinearity;
* `evalCos_exp`: for an even sequence `φ` (a cosine series),
  `∑ₖ (e^φ)ₖ cos kθ = exp(∑ₖ φₖ cos kθ)`; i.e. the Banach-algebra exponential of the
  coefficient sequence is the coefficient sequence of the pointwise exponential.

**Symmetric/antisymmetric parts.** `evenPart x = (x + Rx)/2` and `oddPart x = (x - Rx)/2`
(`R` the reflection `k ↦ -k`), with `‖evenPart x‖ ≤ ‖x‖`, used to remove the translation
symmetry of autonomous periodic problems.

Sanity: `one_apply` (the unit is `δ₀`), `exp_zero'` (`e^0 = δ₀`), and `evalCos_one`.
-/
public section
noncomputable section

namespace LeanTheory.Certificates

open scoped BigOperators

/-! ### Convolution: unit, scalars, associativity -/

/-- The unit `δ₀` of the convolution algebra. -/
@[expose] def delta0 : Ell1Z := lp.single 1 0 1

/-- Coordinates of `δ₀`. -/
theorem delta0_apply (k : ℤ) : delta0 k = if k = 0 then 1 else 0 := by
  simp only [delta0, lp.single_apply, Pi.single_apply]

/-- `δ₀` is a left unit for convolution. -/
theorem conv_delta0_left (y : Ell1Z) : conv 1 delta0 y = y := by
  ext k
  rw [conv_one_apply, tsum_eq_single 0 (fun j hj => by simp [delta0_apply, hj])]
  simp [delta0_apply]

/-- `δ₀` is a right unit for convolution. -/
theorem conv_delta0_right (y : Ell1Z) : conv 1 y delta0 = y := by
  rw [conv_comm, conv_delta0_left]

/-- Convolution commutes with scalars in the first argument. -/
theorem conv_smul_left (c : ℝ) (x y : Ell1Z) : conv 1 (c • x) y = c • conv 1 x y := by
  ext k
  rw [lp.coeFn_smul, Pi.smul_apply, conv_one_apply, conv_one_apply, smul_eq_mul,
    ← tsum_mul_left]
  congr 1; funext j
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- Convolution commutes with scalars in the second argument. -/
theorem conv_smul_right (c : ℝ) (x y : Ell1Z) : conv 1 x (c • y) = c • conv 1 x y := by
  rw [conv_comm, conv_smul_left, conv_comm]

/-- Convolution with zero. -/
theorem conv_zero_left (y : Ell1Z) : conv 1 0 y = 0 := by
  have := conv_smul_left 0 0 y
  simpa using this

/-- The triple-product family `xᵢ yₘ z_{k-i-m}` is summable on `ℤ × ℤ`. -/
theorem summable_triple (x y z : Ell1Z) (k : ℤ) :
    Summable fun p : ℤ × ℤ => x p.1 * y p.2 * z (k - p.1 - p.2) := by
  have hprod : Summable fun p : ℤ × ℤ => |x p.1| * |y p.2| :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun j => |x j|) (g := fun j => |y j|)
      (by simpa only [Real.norm_eq_abs, abs_abs] using summable_abs x)
      (by simpa only [Real.norm_eq_abs, abs_abs] using summable_abs y)
  refine Summable.of_norm_bounded (hprod.mul_right ‖z‖) fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_apply_le_norm z _) (by positivity)

/-- **Associativity of convolution.** -/
theorem conv_assoc (x y z : Ell1Z) : conv 1 (conv 1 x y) z = conv 1 x (conv 1 y z) := by
  ext k
  have hs := summable_triple x y z k
  set h : ℤ × ℤ → ℝ := fun p => x p.1 * y p.2 * z (k - p.1 - p.2) with hh
  -- right side
  have hR : conv 1 x (conv 1 y z) k = ∑' p, h p := by
    rw [conv_one_apply, hs.tsum_prod' (fun i => hs.prod_factor i)]
    refine tsum_congr fun i => ?_
    rw [conv_one_apply, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hh]
    rw [show k - i - m = k - i - m from rfl]; ring
  -- left side
  have hs' : Summable (h ∘ convEquiv) := (convEquiv.summable_iff).2 hs
  have hL : conv 1 (conv 1 x y) z k = ∑' p, h p := by
    rw [← (convEquiv.tsum_eq h)]
    rw [show (∑' c, h (convEquiv c)) = ∑' c, (h ∘ convEquiv) c from rfl,
      hs'.tsum_prod' (fun j => hs'.prod_factor j), conv_one_apply]
    refine tsum_congr fun j => ?_
    rw [conv_one_apply, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    simp only [hh, Function.comp_apply, convEquiv, Equiv.coe_fn_mk]
    rw [show k - i - (j - i) = k - j by ring]
  rw [hL, hR]

/-! ### Scoped Banach-algebra instances -/

namespace ConvAlgebra

/-- The unit `δ₀`. -/
scoped instance instOne : One Ell1Z := ⟨delta0⟩

/-- Multiplication is convolution. -/
scoped instance instMul : Mul Ell1Z := ⟨conv 1⟩

/-- Multiplication is convolution (definitional). -/
theorem mul_def (x y : Ell1Z) : x * y = conv 1 x y := rfl

/-- The unit is `δ₀` (definitional). -/
theorem one_def : (1 : Ell1Z) = delta0 := rfl

/-- Coordinates of the unit. -/
theorem one_apply (k : ℤ) : (1 : Ell1Z) k = if k = 0 then 1 else 0 := delta0_apply k

/-- `ℓ¹(ℤ)` with convolution is a commutative ring. -/
scoped instance instCommRing : CommRing Ell1Z :=
  { (inferInstance : AddCommGroup Ell1Z) with
    mul := conv 1
    one := delta0
    mul_assoc := conv_assoc
    one_mul := conv_delta0_left
    mul_one := conv_delta0_right
    left_distrib := fun a b c => conv_add_right a b c
    right_distrib := fun a b c => conv_add_left a b c
    zero_mul := conv_zero_left
    mul_zero := fun a => by
      change conv 1 a 0 = 0
      rw [conv_comm]; exact conv_zero_left a
    mul_comm := conv_comm }

/-- `ℓ¹(ℤ)` with convolution is a normed commutative ring (`‖x ⋆ y‖ ≤ ‖x‖ ‖y‖`). -/
scoped instance instNormedCommRing : NormedCommRing Ell1Z :=
  { (inferInstance : NormedAddCommGroup Ell1Z), instCommRing with
    norm_mul_le := fun x y => norm_conv_le le_rfl x y }

/-- `‖δ₀‖ = 1`. -/
scoped instance instNormOneClass : NormOneClass Ell1Z :=
  ⟨by
    change ‖delta0‖ = 1
    rw [delta0, lp.norm_single (by norm_num)]; simp⟩

/-- `ℓ¹(ℤ)` with convolution is a normed `ℝ`-algebra. -/
scoped instance instAlgebra : Algebra ℝ Ell1Z :=
  Algebra.ofModule (fun c x y => conv_smul_left c x y) (fun c x y => conv_smul_right c x y)

/-- `ℓ¹(ℤ)` with convolution is a normed `ℝ`-algebra. -/
scoped instance instNormedAlgebra : NormedAlgebra ℝ Ell1Z :=
  { instAlgebra with norm_smul_le := fun c x => norm_smul_le c x }

end ConvAlgebra

open ConvAlgebra

/-! ### Point evaluation as a continuous linear functional -/

/-- Point evaluation `x ↦ ∑ₖ xₖ cos kθ` as a continuous linear functional of norm `≤ 1`. -/
@[expose] def evalCosCLM (θ : ℝ) : Ell1Z →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => evalCos x θ
      map_add' := fun x y => evalCos_add x y θ
      map_smul' := fun c x => by simp [evalCos_smul] }
    1 (fun x => by simpa [Real.norm_eq_abs] using abs_evalCos_le x θ)

/-- `evalCosCLM` evaluates the cosine series. -/
theorem evalCosCLM_apply (θ : ℝ) (x : Ell1Z) : evalCosCLM θ x = evalCos x θ := rfl

/-- Sanity: the unit evaluates to `1`. -/
theorem evalCos_one (θ : ℝ) : evalCos (1 : Ell1Z) θ = 1 := by
  unfold evalCos
  rw [tsum_eq_single 0 (fun k hk => by simp [one_apply, hk])]
  simp [one_apply]

/-- For an even `φ`, `evalCos (φⁿ) = (evalCos φ)ⁿ`. -/
theorem evalCos_pow (φ : Ell1Z) (hφ : ∀ k, φ (-k) = φ k) (θ : ℝ) (n : ℕ) :
    evalCos (φ ^ n) θ = evalCos φ θ ^ n := by
  induction n with
  | zero => simp [evalCos_one]
  | succ n ih => rw [pow_succ', pow_succ', mul_def, evalCos_conv _ _ hφ, ih]

/-- **The exponential commutes with point evaluation on cosine series.** For an even
`φ ∈ ℓ¹(ℤ)`, `∑ₖ (e^φ)ₖ cos kθ = exp (∑ₖ φₖ cos kθ)`. -/
theorem evalCos_exp (φ : Ell1Z) (hφ : ∀ k, φ (-k) = φ k) (θ : ℝ) :
    evalCos (NormedSpace.exp φ) θ = Real.exp (evalCos φ θ) := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) φ
  have h2 := (evalCosCLM θ).hasSum h1
  simp only [map_smul, evalCosCLM_apply, evalCos_pow φ hφ θ, smul_eq_mul] at h2
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (evalCos φ θ)
  simp only [smul_eq_mul] at h3
  rw [Real.exp_eq_exp_ℝ]
  exact h2.unique h3

/-! ### Norm bounds for the exponential -/

/-- `‖e^x‖ ≤ e^{‖x‖}`. -/
theorem norm_exp_le (x : Ell1Z) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [Real.exp_eq_exp_ℝ, ← h1.tsum_eq]
  refine tsum_of_norm_bounded h3 fun n => ?_
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le x n

/-- Sanity: `e^0 = δ₀`. -/
theorem exp_zero' : NormedSpace.exp (0 : Ell1Z) = delta0 := NormedSpace.exp_zero

/-- The derivative of `exp` is multiplication by `exp`. -/
theorem hasFDerivAt_exp' (x : Ell1Z) :
    HasFDerivAt (NormedSpace.exp : Ell1Z → Ell1Z)
      (NormedSpace.exp x • (1 : Ell1Z →L[ℝ] Ell1Z)) x :=
  hasFDerivAt_exp (𝕂 := ℝ)

/-- Norm of the multiplication operator `a • 1`. -/
theorem norm_smul_one_le (a : Ell1Z) : ‖a • (1 : Ell1Z →L[ℝ] Ell1Z)‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact norm_mul_le a h

/-- **First-order bound** `‖e^x - e^y‖ ≤ e^ρ ‖x - y‖` for `x, y` in a ball of radius `r`
around `c` with `‖c‖ + r ≤ ρ`. -/
theorem norm_exp_sub_exp_le {c x y : Ell1Z} {r ρ : ℝ} (hρ : ‖c‖ + r ≤ ρ)
    (hx : ‖x - c‖ ≤ r) (hy : ‖y - c‖ ≤ r) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ ≤ Real.exp ρ * ‖x - y‖ := by
  have hball : ∀ w ∈ Metric.closedBall c r, ‖w‖ ≤ ρ := fun w hw => by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    calc ‖w‖ = ‖c + (w - c)‖ := by abel_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  have hderiv : ∀ w ∈ Metric.closedBall c r, HasFDerivWithinAt NormedSpace.exp
      (NormedSpace.exp w • (1 : Ell1Z →L[ℝ] Ell1Z)) (Metric.closedBall c r) w :=
    fun w _ => (hasFDerivAt_exp' w).hasFDerivWithinAt
  have hbound : ∀ w ∈ Metric.closedBall c r,
      ‖NormedSpace.exp w • (1 : Ell1Z →L[ℝ] Ell1Z)‖ ≤ Real.exp ρ := fun w hw =>
    (norm_smul_one_le _).trans ((norm_exp_le w).trans (Real.exp_le_exp.2 (hball w hw)))
  have hxm : x ∈ Metric.closedBall c r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx
  have hym : y ∈ Metric.closedBall c r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
  exact (convex_closedBall c r).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    hym hxm

/-- **Second-order bound.** For `φ, ψ ∈ B̄(ū, r)`,
`‖e^φ - e^ψ - e^{ū} (φ - ψ)‖ ≤ r e^{‖ū‖ + r} ‖φ - ψ‖`. -/
theorem norm_exp_sub_exp_sub_mul_le {c x y : Ell1Z} {r : ℝ}
    (hx : ‖x - c‖ ≤ r) (hy : ‖y - c‖ ≤ r) :
    ‖NormedSpace.exp x - NormedSpace.exp y - NormedSpace.exp c * (x - y)‖ ≤
      r * Real.exp (‖c‖ + r) * ‖x - y‖ := by
  set g : Ell1Z → Ell1Z := fun w => NormedSpace.exp w - NormedSpace.exp c * w with hg
  have hderiv : ∀ w ∈ Metric.closedBall c r, HasFDerivWithinAt g
      ((NormedSpace.exp w - NormedSpace.exp c) • (1 : Ell1Z →L[ℝ] Ell1Z))
      (Metric.closedBall c r) w := by
    intro w _
    have h1 := hasFDerivAt_exp' w
    have h2 : HasFDerivAt (fun w : Ell1Z => NormedSpace.exp c * w)
        (NormedSpace.exp c • (1 : Ell1Z →L[ℝ] Ell1Z)) w := by
      have := (NormedSpace.exp c • (1 : Ell1Z →L[ℝ] Ell1Z)).hasFDerivAt (x := w)
      convert this using 1
      funext v; simp [smul_eq_mul]
    have := h1.sub h2
    rw [← sub_smul] at this
    exact this.hasFDerivWithinAt
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hbound : ∀ w ∈ Metric.closedBall c r,
      ‖(NormedSpace.exp w - NormedSpace.exp c) • (1 : Ell1Z →L[ℝ] Ell1Z)‖ ≤
        r * Real.exp (‖c‖ + r) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    refine (norm_smul_one_le _).trans ?_
    have := norm_exp_sub_exp_le (c := c) (x := w) (y := c) (r := r) (ρ := ‖c‖ + r) le_rfl hw
      (by simp [hr])
    calc _ ≤ Real.exp (‖c‖ + r) * ‖w - c‖ := this
      _ ≤ Real.exp (‖c‖ + r) * r := by gcongr
      _ = r * Real.exp (‖c‖ + r) := by ring
  have hxm : x ∈ Metric.closedBall c r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx
  have hym : y ∈ Metric.closedBall c r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
  have := (convex_closedBall c r).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    hym hxm
  have heq : g x - g y = NormedSpace.exp x - NormedSpace.exp y -
      NormedSpace.exp c * (x - y) := by simp only [hg, mul_sub]; abel
  rw [← heq]; exact this

/-! ### Reflection and the exponential -/

/-- The reflection `k ↦ -k` as a continuous linear isometry-like map (norm `≤ 1`). -/
@[expose] def reflCLM : Ell1Z →L[ℝ] Ell1Z :=
  LinearMap.mkContinuous
    { toFun := refl
      map_add' := fun x y => by ext k; simp [refl_apply]
      map_smul' := fun c x => by ext k; simp [refl_apply] }
    1 (fun x => by simp [norm_refl])

/-- The reflection fixes the unit. -/
theorem refl_one : refl (1 : Ell1Z) = 1 := by
  ext k; rw [refl_apply, one_apply, one_apply]; simp

/-- The reflection is multiplicative. -/
theorem refl_mul (x y : Ell1Z) : refl (x * y) = refl x * refl y := by
  rw [mul_def, mul_def, conv_refl]

/-- The reflection commutes with powers. -/
theorem refl_pow (x : Ell1Z) (n : ℕ) : refl (x ^ n) = refl x ^ n := by
  induction n with
  | zero => simp [refl_one]
  | succ n ih => rw [pow_succ, pow_succ, refl_mul, ih]

/-- The reflection commutes with the exponential. -/
theorem refl_exp (x : Ell1Z) : refl (NormedSpace.exp x) = NormedSpace.exp (refl x) := by
  have h1 := reflCLM.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (refl x)
  have : (fun n : ℕ => reflCLM (((n.factorial : ℝ))⁻¹ • x ^ n)) =
      fun n : ℕ => ((n.factorial : ℝ))⁻¹ • refl x ^ n := by
    funext n
    rw [map_smul]
    change _ • refl (x ^ n) = _
    rw [refl_pow]
  rw [this] at h1
  exact h1.unique h2

/-- The exponential of an even sequence is even. -/
theorem exp_even {x : Ell1Z} (hx : ∀ k, x (-k) = x k) (k : ℤ) :
    NormedSpace.exp x (-k) = NormedSpace.exp x k := by
  have hr : refl x = x := by ext j; rw [refl_apply, hx]
  have := congrArg (fun z : Ell1Z => z k) (refl_exp x)
  simp only [hr, refl_apply] at this
  exact this

/-! ### Even and odd parts -/

/-- The even part `(x + Rx)/2`. -/
@[expose] def evenPart (x : Ell1Z) : Ell1Z := (1 / 2 : ℝ) • (x + refl x)

/-- The odd part `(x - Rx)/2`. -/
@[expose] def oddPart (x : Ell1Z) : Ell1Z := (1 / 2 : ℝ) • (x - refl x)

/-- Coordinates of the even part. -/
theorem evenPart_apply (x : Ell1Z) (k : ℤ) : evenPart x k = (x k + x (-k)) / 2 := by
  rw [evenPart, lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, refl_apply,
    smul_eq_mul]; ring

/-- Coordinates of the odd part. -/
theorem oddPart_apply (x : Ell1Z) (k : ℤ) : oddPart x k = (x k - x (-k)) / 2 := by
  rw [oddPart, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, refl_apply,
    smul_eq_mul]; ring

/-- `x = evenPart x + oddPart x`. -/
theorem evenPart_add_oddPart (x : Ell1Z) : evenPart x + oddPart x = x := by
  ext k; simp [evenPart_apply, oddPart_apply]; ring

/-- The even part is even. -/
theorem evenPart_even (x : Ell1Z) (k : ℤ) : evenPart x (-k) = evenPart x k := by
  simp [evenPart_apply]; ring

/-- `‖evenPart x‖ ≤ ‖x‖`. -/
theorem norm_evenPart_le (x : Ell1Z) : ‖evenPart x‖ ≤ ‖x‖ := by
  unfold evenPart
  rw [norm_smul]
  calc ‖(1 / 2 : ℝ)‖ * ‖x + refl x‖ ≤ 1 / 2 * (‖x‖ + ‖refl x‖) := by
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; gcongr; exact norm_add_le _ _
    _ = ‖x‖ := by rw [norm_refl]; ring

/-- `‖oddPart x‖ ≤ ‖x‖`. -/
theorem norm_oddPart_le (x : Ell1Z) : ‖oddPart x‖ ≤ ‖x‖ := by
  unfold oddPart
  rw [norm_smul]
  calc ‖(1 / 2 : ℝ)‖ * ‖x - refl x‖ ≤ 1 / 2 * (‖x‖ + ‖refl x‖) := by
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; gcongr; exact norm_sub_le _ _
    _ = ‖x‖ := by rw [norm_refl]; ring

/-- The even part is additive. -/
theorem evenPart_sub (x y : Ell1Z) : evenPart (x - y) = evenPart x - evenPart y := by
  ext k; simp [evenPart_apply]; ring

/-- The odd part is additive. -/
theorem oddPart_sub (x y : Ell1Z) : oddPart (x - y) = oddPart x - oddPart y := by
  ext k; simp [oddPart_apply]; ring

/-- An even sequence is its own even part. -/
theorem evenPart_of_even {x : Ell1Z} (hx : ∀ k, x (-k) = x k) : evenPart x = x := by
  ext k; rw [evenPart_apply, hx]; ring

/-- An even sequence has zero odd part. -/
theorem oddPart_of_even {x : Ell1Z} (hx : ∀ k, x (-k) = x k) : oddPart x = 0 := by
  ext k; rw [oddPart_apply, hx]; simp

/-- A sequence with zero odd part is even. -/
theorem even_of_oddPart_eq_zero {x : Ell1Z} (hx : oddPart x = 0) (k : ℤ) : x (-k) = x k := by
  have := congrArg (fun z : Ell1Z => z k) hx
  simp only [oddPart_apply, lp.coeFn_zero, Pi.zero_apply] at this
  linarith

/-- The odd part of an odd part. -/
theorem oddPart_oddPart (x : Ell1Z) : oddPart (oddPart x) = oddPart x := by
  ext k; simp [oddPart_apply]; ring

end LeanTheory.Certificates
