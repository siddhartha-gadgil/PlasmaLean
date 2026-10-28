/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.Cohomological
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Banach algebra `ℓ¹_r(ℤ²)` of analytic functions on the complex strip

A Banach-algebra lemma for the a posteriori KAM scheme: the
two-dimensional analogue of `Certificates/WeightedEll1` + `Certificates/ConvAlgebra`, with the
weight `e^{r(|k|+|m|)}` of `Theory/KAM/Cohomological.lean` and complex coefficients.

**Coefficient level.** For `f g : ℤ × ℤ → ℂ` the convolution is
`(f ⋆ g)_n = ∑_a f_a g_{n−a}` (`cconv`); it represents the pointwise product of Fourier series
(`fourierSum_cconv`). Since `|k+k'| + |m+m'| ≤ (|k|+|m|) + (|k'|+|m'|)` the weight is
submultiplicative for `r ≥ 0` (`weight_add_le`), hence
`‖f ⋆ g‖_r ≤ ‖f‖_r ‖g‖_r` for the norm `wnorm` of `Cohomological.lean` (`wnorm_cconv_le`).
Monotonicity in `r`: `InWeighted.mono`, `wnorm_mono`. Evaluation: `‖F(θ,ψ)‖ ≤ ‖f‖_0 ≤ ‖f‖_r`
(`norm_fourierSum_le`) and on the complex strip `|Im θ|, |Im ψ| ≤ r`:
`‖F(θ,ψ)‖ ≤ ‖f‖_r` (`norm_fourierSumC_le`, with `fourierSumC_ofReal` showing it extends `F`).

**The space.** `WEll1Z2 r` is Mathlib's `lp (fun _ : ℤ × ℤ => ℂ) 1`, an element being the
rescaled sequence `x_n = f_n e^{r(|k|+|m|)}`. Completeness and the normed-space structure come
from Mathlib. The bridge to `Cohomological.lean` is exact: `coeff x` recovers `f`, and
`‖x‖ = wnorm r (coeff x)` (`norm_eq_wnorm`), `‖ofCoeff f hf‖ = wnorm r f` (`norm_ofCoeff`).
For `r ≥ 0` (a `Fact (0 ≤ r)` instance) it is a commutative unital Banach algebra over `ℂ`
(`NormedCommRing`, `NormOneClass`, `NormedAlgebra ℂ`), with multiplication `cconv` on
coefficients (`coeff_mul`). The Cauchy estimates and the cohomological solver of
`Cohomological.lean` become bounded maps `WEll1Z2 r → WEll1Z2 (r − δ)` (`dθL`, `dψL`,
`cohSolL`), restriction `WEll1Z2 r → WEll1Z2 r'` (`restrict`, `r' ≤ r`) has norm `≤ 1` and is
multiplicative.

**Neumann series.** `neumann`: if `‖a‖_r < 1` then `1 + a` is a unit and
`‖(1 + a)⁻¹‖_r ≤ 1 / (1 − ‖a‖_r)`; `neumann_near_one` is the same for `b` with `‖b − 1‖ < 1`.

**Sanity.** `coeff_one` (the unit is `δ₀`), `norm_mode` (`‖e^{i(kθ+mψ)}‖_r = e^{r(|k|+|m|)}`),
`mode_mul` (modes multiply by adding frequencies), `neumann_zero`, and two rejected fixtures:
`not_isUnit_one_add_neg_one` (the Neumann hypothesis `‖a‖ < 1` cannot be relaxed to `≤ 1`) and
`cconv_not_submult_neg` (for `r < 0` the Banach-algebra estimate fails).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open Complex

/-! ## Submultiplicativity of the weight -/

/-- `|k+k'| + |m+m'| ≤ (|k|+|m|) + (|k'|+|m'|)`. -/
theorem modeSize_add_le (a b : ℤ × ℤ) : modeSize (a + b) ≤ modeSize a + modeSize b := by
  unfold modeSize
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  linarith [abs_add_le (a.1 : ℝ) b.1, abs_add_le (a.2 : ℝ) b.2]

/-- The weight is submultiplicative for `r ≥ 0`. -/
theorem weight_add_le {r : ℝ} (hr : 0 ≤ r) (a b : ℤ × ℤ) :
    weight r (a + b) ≤ weight r a * weight r b := by
  unfold weight
  rw [← Real.exp_add, ← mul_add]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (modeSize_add_le a b) hr)

/-- Submultiplicativity in the form used for convolutions. -/
theorem weight_le_mul_sub {r : ℝ} (hr : 0 ≤ r) (n a : ℤ × ℤ) :
    weight r n ≤ weight r a * weight r (n - a) := by
  have := weight_add_le hr a (n - a)
  rwa [add_sub_cancel] at this

/-- The weight of the zero mode is `1`. -/
@[simp] theorem weight_zero_mode (r : ℝ) : weight r 0 = 1 := by
  simp [weight, modeSize]

/-! ## Monotonicity in the strip width -/

/-- A function analytic on a wider strip is analytic on a narrower one. -/
theorem InWeighted.mono {r r' : ℝ} {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) (h : r' ≤ r) :
    InWeighted r' f :=
  (wnorm_le_of_termwise (C := 1) hf fun km => by
    rw [one_mul]; exact mul_le_mul_of_nonneg_left (weight_mono h km) (norm_nonneg _)).1

/-- **Monotonicity of the norm in `r`:** `‖f‖_{r'} ≤ ‖f‖_r` for `r' ≤ r`. -/
theorem wnorm_mono {r r' : ℝ} {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) (h : r' ≤ r) :
    wnorm r' f ≤ wnorm r f := by
  simpa using (wnorm_le_of_termwise (C := 1) hf fun km => by
    rw [one_mul]; exact mul_le_mul_of_nonneg_left (weight_mono h km) (norm_nonneg _)).2

/-- `InWeighted 0 f` is absolute summability. -/
theorem inWeighted_zero_iff (f : ℤ × ℤ → ℂ) :
    InWeighted 0 f ↔ Summable fun n => ‖f n‖ := by
  simp [InWeighted, weight]

/-- Each coefficient is bounded by the unweighted norm. -/
theorem norm_le_tsum_norm {f : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖) (n : ℤ × ℤ) :
    ‖f n‖ ≤ ∑' a, ‖f a‖ :=
  hf.le_tsum n fun _ _ => norm_nonneg _

/-! ## Convolution of coefficients -/

/-- The convolution `(f ⋆ g)_n = ∑_a f_a g_{n−a}` (coefficients of the product of the Fourier
series). -/
def cconv (f g : ℤ × ℤ → ℂ) (n : ℤ × ℤ) : ℂ := ∑' a, f a * g (n - a)

/-- The unit `δ₀` (coefficients of the constant function `1`). -/
def delta2 (n : ℤ × ℤ) : ℂ := if n = 0 then 1 else 0

/-- The reindexing `(n, a) ↦ (a, n − a)` of `ℤ² × ℤ²`. -/
def pairEquiv : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun q := (q.2, q.1 - q.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv q := by simp
  right_inv p := by simp

/-- Cauchy product of nonnegative summable families over `ℤ²`:
`∑_n ∑_a F_a G_{n−a} = (∑ F)(∑ G)`, with summable fibres. -/
theorem hasSum_conv_nonneg {F G : ℤ × ℤ → ℝ} (hF0 : ∀ n, 0 ≤ F n) (hG0 : ∀ n, 0 ≤ G n)
    (hF : Summable F) (hG : Summable G) :
    HasSum (fun n => ∑' a, F a * G (n - a)) ((∑' a, F a) * ∑' b, G b) ∧
      ∀ n, Summable fun a => F a * G (n - a) := by
  have hprod : Summable fun p : (ℤ × ℤ) × (ℤ × ℤ) => F p.1 * G p.2 :=
    summable_mul_of_summable_norm (R := ℝ)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)] using hF)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hG0 _)] using hG)
  have hHas := hF.hasSum.mul hG.hasSum hprod
  have hHas' : HasSum (fun q : (ℤ × ℤ) × (ℤ × ℤ) => F q.2 * G (q.1 - q.2))
      ((∑' a, F a) * ∑' b, G b) :=
    (pairEquiv.hasSum_iff (f := fun p : (ℤ × ℤ) × (ℤ × ℤ) => F p.1 * G p.2)).2 hHas
  exact ⟨hHas'.prod_fiberwise fun n => (hHas'.summable.prod_factor n).hasSum,
    fun n => hHas'.summable.prod_factor n⟩

/-- The convolution summand is absolutely summable when `f` is and `g` is bounded by `B`. -/
theorem summable_norm_conv_summand {f g : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) (n : ℤ × ℤ) :
    Summable fun a => ‖f a * g (n - a)‖ :=
  (hf.mul_right (∑' b, ‖g b‖)).of_nonneg_of_le (fun _ => norm_nonneg _) fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_tsum_norm hg _) (norm_nonneg _)

/-- The convolution summand is summable. -/
theorem summable_conv_summand {f g : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) (n : ℤ × ℤ) :
    Summable fun a => f a * g (n - a) :=
  (summable_norm_conv_summand hf hg n).of_norm

/-- Coefficientwise bound: `‖(f⋆g)_n‖ w_n ≤ ∑_a (‖f_a‖ w_a)(‖g_{n−a}‖ w_{n−a})` for `r ≥ 0`. -/
theorem norm_cconv_mul_weight_le {r : ℝ} (hr : 0 ≤ r) {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (hg : InWeighted r g) (n : ℤ × ℤ) :
    ‖cconv f g n‖ * weight r n ≤
      ∑' a, (‖f a‖ * weight r a) * (‖g (n - a)‖ * weight r (n - a)) := by
  obtain ⟨-, hfib⟩ := hasSum_conv_nonneg
    (fun a => mul_nonneg (norm_nonneg (f a)) (weight_pos r a).le)
    (fun a => mul_nonneg (norm_nonneg (g a)) (weight_pos r a).le) hf hg
  have hf0 := summable_norm_of_inWeighted hr hf
  have hg0 := summable_norm_of_inWeighted hr hg
  have hs := summable_norm_conv_summand hf0 hg0 n
  have hw := (weight_pos r n).le
  calc ‖cconv f g n‖ * weight r n ≤ (∑' a, ‖f a * g (n - a)‖) * weight r n := by
        gcongr; exact norm_tsum_le_tsum_norm hs
    _ = ∑' a, weight r n * ‖f a * g (n - a)‖ := by rw [mul_comm, tsum_mul_left]
    _ ≤ ∑' a, (‖f a‖ * weight r a) * (‖g (n - a)‖ * weight r (n - a)) := by
        refine (hs.mul_left _).tsum_le_tsum (fun a => ?_) (hfib n)
        rw [norm_mul]
        have := weight_le_mul_sub hr n a
        calc weight r n * (‖f a‖ * ‖g (n - a)‖)
            ≤ (weight r a * weight r (n - a)) * (‖f a‖ * ‖g (n - a)‖) := by gcongr
          _ = _ := by ring

/-- Convolution preserves analyticity on the strip (`r ≥ 0`). -/
theorem inWeighted_cconv {r : ℝ} (hr : 0 ≤ r) {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (hg : InWeighted r g) : InWeighted r (cconv f g) := by
  obtain ⟨hsum, -⟩ := hasSum_conv_nonneg
    (fun a => mul_nonneg (norm_nonneg (f a)) (weight_pos r a).le)
    (fun a => mul_nonneg (norm_nonneg (g a)) (weight_pos r a).le) hf hg
  exact hsum.summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (weight_pos r n).le)
    (norm_cconv_mul_weight_le hr hf hg)

/-- **Banach-algebra estimate** `‖f ⋆ g‖_r ≤ ‖f‖_r ‖g‖_r` for `r ≥ 0`. -/
theorem wnorm_cconv_le {r : ℝ} (hr : 0 ≤ r) {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (hg : InWeighted r g) : wnorm r (cconv f g) ≤ wnorm r f * wnorm r g := by
  obtain ⟨hsum, -⟩ := hasSum_conv_nonneg
    (fun a => mul_nonneg (norm_nonneg (f a)) (weight_pos r a).le)
    (fun a => mul_nonneg (norm_nonneg (g a)) (weight_pos r a).le) hf hg
  unfold wnorm
  rw [← hsum.tsum_eq]
  exact (inWeighted_cconv hr hf hg).tsum_le_tsum (norm_cconv_mul_weight_le hr hf hg)
    hsum.summable

/-- Convolution is commutative. -/
theorem cconv_comm (f g : ℤ × ℤ → ℂ) : cconv f g = cconv g f := by
  funext n
  unfold cconv
  rw [← (Equiv.subLeft n).tsum_eq]
  congr 1; funext a
  simp [Equiv.subLeft, mul_comm]

/-- `δ₀` is a left unit. -/
theorem cconv_delta2_left (g : ℤ × ℤ → ℂ) : cconv delta2 g = g := by
  funext n
  unfold cconv
  rw [tsum_eq_single 0 (fun a ha => by simp [delta2, ha])]
  simp [delta2]

/-- `δ₀` is a right unit. -/
theorem cconv_delta2_right (g : ℤ × ℤ → ℂ) : cconv g delta2 = g := by
  rw [cconv_comm, cconv_delta2_left]

/-- Convolution with zero. -/
@[simp] theorem cconv_zero_left (g : ℤ × ℤ → ℂ) : cconv 0 g = 0 := by
  funext n; simp [cconv]

/-- Convolution commutes with scalars. -/
theorem cconv_smul_left (c : ℂ) (f g : ℤ × ℤ → ℂ) : cconv (c • f) g = c • cconv f g := by
  funext n
  simp only [cconv, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left, mul_assoc]

/-- Convolution is additive in the first argument (absolutely summable data). -/
theorem cconv_add_left {f g h : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) (hh : Summable fun n => ‖h n‖) :
    cconv (f + g) h = cconv f h + cconv g h := by
  funext n
  simp only [cconv, Pi.add_apply, add_mul]
  exact (summable_conv_summand hf hh n).tsum_add (summable_conv_summand hg hh n)

/-- **Associativity** of convolution (absolutely summable data). -/
theorem cconv_assoc {f g h : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) (hh : Summable fun n => ‖h n‖) :
    cconv (cconv f g) h = cconv f (cconv g h) := by
  funext n
  set T : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun p => f p.1 * g p.2 * h (n - p.1 - p.2) with hT
  have hprod : Summable fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖f p.1‖ * ‖g p.2‖ :=
    hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hs : Summable T := by
    refine Summable.of_norm_bounded (hprod.mul_right (∑' b, ‖h b‖)) fun p => ?_
    simp only [hT, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_tsum_norm hh _) (by positivity)
  have hR : cconv f (cconv g h) n = ∑' p, T p := by
    rw [hs.tsum_prod' (fun a => hs.prod_factor a)]
    refine tsum_congr fun a => ?_
    simp only [cconv, hT, ← tsum_mul_left, mul_assoc]
  have hs' : Summable (T ∘ pairEquiv) := pairEquiv.summable_iff.2 hs
  have hL : cconv (cconv f g) h n = ∑' p, T p := by
    rw [← pairEquiv.tsum_eq T,
      show (∑' q, T (pairEquiv q)) = ∑' q, (T ∘ pairEquiv) q from rfl,
      hs'.tsum_prod' (fun c => hs'.prod_factor c)]
    refine tsum_congr fun c => ?_
    simp only [cconv, ← tsum_mul_right]
    refine tsum_congr fun a => ?_
    simp only [hT, Function.comp_apply, pairEquiv, Equiv.coe_fn_mk]
    rw [show n - a - (c - a) = n - c by abel]
  rw [hL, hR]

/-- Convolution of absolutely summable data is absolutely summable. -/
theorem summable_norm_cconv {f g : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) : Summable fun n => ‖cconv f g n‖ := by
  have := inWeighted_cconv le_rfl ((inWeighted_zero_iff f).2 hf) ((inWeighted_zero_iff g).2 hg)
  exact (inWeighted_zero_iff _).1 this

/-! ## Evaluation of Fourier series -/

/-- Fourier modes multiply by adding frequencies. -/
theorem fourierMode_add (a b : ℤ × ℤ) (θ ψ : ℝ) :
    fourierMode (a + b) θ ψ = fourierMode a θ ψ * fourierMode b θ ψ := by
  unfold fourierMode
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast; ring

/-- **Evaluation is multiplicative:** the Fourier series of `f ⋆ g` is the product of the
Fourier series of `f` and `g` (absolutely summable data). -/
theorem fourierSum_cconv {f g : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) (θ ψ : ℝ) :
    fourierSum (cconv f g) θ ψ = fourierSum f θ ψ * fourierSum g θ ψ := by
  set H : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun p => f p.1 * g p.2 * fourierMode (p.1 + p.2) θ ψ
    with hH
  have hprod : Summable fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖f p.1‖ * ‖g p.2‖ :=
    hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hs : Summable H := by
    refine Summable.of_norm_bounded hprod fun p => ?_
    simp [hH, norm_fourierMode]
  have hRHS : fourierSum f θ ψ * fourierSum g θ ψ = ∑' p, H p := by
    unfold fourierSum
    rw [tsum_mul_tsum_of_summable_norm (by simpa [norm_mul, norm_fourierMode] using hf)
      (by simpa [norm_mul, norm_fourierMode] using hg)]
    refine tsum_congr fun p => ?_
    simp only [hH, fourierMode_add]; ring
  have hs' : Summable (H ∘ pairEquiv) := pairEquiv.summable_iff.2 hs
  rw [hRHS, ← pairEquiv.tsum_eq H,
    show (∑' q, H (pairEquiv q)) = ∑' q, (H ∘ pairEquiv) q from rfl,
    hs'.tsum_prod' (fun c => hs'.prod_factor c)]
  unfold fourierSum
  refine tsum_congr fun n => ?_
  simp only [cconv, ← tsum_mul_right]
  refine tsum_congr fun a => ?_
  simp only [hH, Function.comp_apply, pairEquiv, Equiv.coe_fn_mk, add_sub_cancel]

/-- The Fourier series of `δ₀` is `1`. -/
theorem fourierSum_delta2 (θ ψ : ℝ) : fourierSum delta2 θ ψ = 1 := by
  unfold fourierSum
  rw [tsum_eq_single 0 (fun a ha => by simp [delta2, ha])]
  simp [delta2, fourierMode]

/-- **Sup bound on the real torus:** `‖F(θ,ψ)‖ ≤ ‖f‖_0 ≤ ‖f‖_r` for `r ≥ 0`. -/
theorem norm_fourierSum_le {r : ℝ} (hr : 0 ≤ r) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (θ ψ : ℝ) : ‖fourierSum f θ ψ‖ ≤ wnorm 0 f ∧ wnorm 0 f ≤ wnorm r f := by
  refine ⟨?_, wnorm_mono hf hr⟩
  have h0 := summable_norm_of_inWeighted hr hf
  have hn : Summable fun n => ‖f n * fourierMode n θ ψ‖ := by
    simpa [norm_mul, norm_fourierMode] using h0
  calc ‖fourierSum f θ ψ‖ ≤ ∑' n, ‖f n * fourierMode n θ ψ‖ := norm_tsum_le_tsum_norm hn
    _ = wnorm 0 f := by simp [wnorm, weight, norm_fourierMode]

/-- The Fourier mode `e^{i(kθ + mψ)}` at complex arguments. -/
def fourierModeC (km : ℤ × ℤ) (θ ψ : ℂ) : ℂ := Complex.exp (I * (km.1 * θ + km.2 * ψ))

/-- The Fourier series at complex arguments `θ, ψ`. -/
def fourierSumC (u : ℤ × ℤ → ℂ) (θ ψ : ℂ) : ℂ := ∑' km, u km * fourierModeC km θ ψ

/-- At real arguments the complex Fourier series is the Fourier series. -/
theorem fourierSumC_ofReal (u : ℤ × ℤ → ℂ) (θ ψ : ℝ) :
    fourierSumC u θ ψ = fourierSum u θ ψ := by
  unfold fourierSumC fourierSum fourierModeC fourierMode
  refine tsum_congr fun km => ?_
  congr 2
  push_cast; ring

/-- On the strip `|Im θ|, |Im ψ| ≤ r` a mode has modulus at most `e^{r(|k|+|m|)}`. -/
theorem norm_fourierModeC_le {r : ℝ} {θ ψ : ℂ} (hθ : |θ.im| ≤ r) (hψ : |ψ.im| ≤ r)
    (km : ℤ × ℤ) : ‖fourierModeC km θ ψ‖ ≤ weight r km := by
  unfold fourierModeC weight modeSize
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have hre : (I * (km.1 * θ + km.2 * ψ)).re = -((km.1 : ℝ) * θ.im + (km.2 : ℝ) * ψ.im) := by
    simp
  rw [hre]
  have h1 : -((km.1 : ℝ) * θ.im) ≤ |(km.1 : ℝ)| * r := by
    have := neg_abs_le ((km.1 : ℝ) * θ.im)
    rw [abs_mul] at this
    nlinarith [abs_nonneg (km.1 : ℝ)]
  have h2 : -((km.2 : ℝ) * ψ.im) ≤ |(km.2 : ℝ)| * r := by
    have := neg_abs_le ((km.2 : ℝ) * ψ.im)
    rw [abs_mul] at this
    nlinarith [abs_nonneg (km.2 : ℝ)]
  nlinarith

/-- **Sup bound on the complex strip:** for `|Im θ|, |Im ψ| ≤ r` the Fourier series converges
absolutely and `‖F(θ,ψ)‖ ≤ ‖f‖_r`. -/
theorem norm_fourierSumC_le {r : ℝ} {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) {θ ψ : ℂ}
    (hθ : |θ.im| ≤ r) (hψ : |ψ.im| ≤ r) : ‖fourierSumC f θ ψ‖ ≤ wnorm r f := by
  have hb : ∀ km, ‖f km * fourierModeC km θ ψ‖ ≤ ‖f km‖ * weight r km := fun km => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_fourierModeC_le hθ hψ km) (norm_nonneg _)
  have hn : Summable fun km => ‖f km * fourierModeC km θ ψ‖ :=
    hf.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hf)

/-! ## The space `ℓ¹_r(ℤ²)` -/

/-- Unweighted `ℓ¹(ℤ², ℂ)`. -/
abbrev Ell1Z2 : Type := lp (fun _ : ℤ × ℤ => ℂ) 1

/-- The weighted space `ℓ¹_r(ℤ²)`: an element is stored as the rescaled sequence
`x_n = f_n e^{r(|k|+|m|)}` in `ℓ¹(ℤ²)`, `f = coeff x` being its Fourier coefficients. -/
def WEll1Z2 (_r : ℝ) : Type := Ell1Z2

namespace WEll1Z2

variable {r : ℝ}

/-- The normed group structure (that of `ℓ¹`). -/
instance : NormedAddCommGroup (WEll1Z2 r) := inferInstanceAs (NormedAddCommGroup Ell1Z2)

/-- The complex normed space structure (that of `ℓ¹`). -/
instance : NormedSpace ℂ (WEll1Z2 r) := inferInstanceAs (NormedSpace ℂ Ell1Z2)

/-- **Completeness** of `ℓ¹_r(ℤ²)` (inherited from Mathlib's `lp`). -/
instance : CompleteSpace (WEll1Z2 r) := inferInstanceAs (CompleteSpace Ell1Z2)

/-- The underlying rescaled sequence. -/
def toEll (x : WEll1Z2 r) : Ell1Z2 := x

/-- `toEll` is additive (definitional). -/
theorem toEll_add (x y : WEll1Z2 r) : toEll (x + y) = toEll x + toEll y := rfl

/-- `toEll` commutes with scalars (definitional). -/
theorem toEll_smul (c : ℂ) (x : WEll1Z2 r) : toEll (c • x) = c • toEll x := rfl

/-- `toEll` commutes with negation (definitional). -/
theorem toEll_neg (x : WEll1Z2 r) : toEll (-x) = -toEll x := rfl

/-- `toEll` commutes with subtraction (definitional). -/
theorem toEll_sub (x y : WEll1Z2 r) : toEll (x - y) = toEll x - toEll y := rfl

/-- `toEll` of zero (definitional). -/
theorem toEll_zero : toEll (0 : WEll1Z2 r) = 0 := rfl

/-- Membership in `ℓ¹(ℤ²)` is absolute summability. -/
theorem memℓp_one_iff' (a : ℤ × ℤ → ℂ) : Memℓp a 1 ↔ Summable fun n => ‖a n‖ := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

/-- The Fourier coefficients `f_n = x_n / e^{r(|k|+|m|)}`. -/
def coeff (x : WEll1Z2 r) (n : ℤ × ℤ) : ℂ := toEll x n / (weight r n : ℂ)

/-- The rescaled entry in terms of the coefficient. -/
theorem toEll_apply (x : WEll1Z2 r) (n : ℤ × ℤ) :
    toEll x n = coeff x n * (weight r n : ℂ) := by
  have : (weight r n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos r n).ne'
  rw [coeff, div_mul_cancel₀ _ this]

/-- `‖x_n‖ = ‖f_n‖ e^{r(|k|+|m|)}`. -/
theorem norm_toEll_apply (x : WEll1Z2 r) (n : ℤ × ℤ) :
    ‖toEll x n‖ = ‖coeff x n‖ * weight r n := by
  rw [toEll_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (weight_pos r n).le]

/-- Extensionality through the coefficients. -/
theorem ext_coeff {x y : WEll1Z2 r} (h : ∀ n, coeff x n = coeff y n) : x = y := by
  apply lp.ext (E := fun _ : ℤ × ℤ => ℂ) (p := 1)
  funext n
  change toEll x n = toEll y n
  rw [toEll_apply, toEll_apply, h]

/-- Coefficients of a sum. -/
@[simp] theorem coeff_add (x y : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (x + y) n = coeff x n + coeff y n := by
  simp only [coeff, toEll_add, lp.coeFn_add, Pi.add_apply, add_div]

/-- Coefficients of zero. -/
@[simp] theorem coeff_zero (n : ℤ × ℤ) : coeff (0 : WEll1Z2 r) n = 0 := by
  simp [coeff, toEll_zero]

/-- Coefficients of a scalar multiple. -/
@[simp] theorem coeff_smul (c : ℂ) (x : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (c • x) n = c * coeff x n := by
  simp only [coeff, toEll_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- Coefficients of a negation. -/
@[simp] theorem coeff_neg (x : WEll1Z2 r) (n : ℤ × ℤ) : coeff (-x) n = -coeff x n := by
  simp only [coeff, toEll_neg, lp.coeFn_neg, Pi.neg_apply, neg_div]

/-- Coefficients of a difference. -/
@[simp] theorem coeff_sub (x y : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (x - y) n = coeff x n - coeff y n := by
  simp only [coeff, toEll_sub, lp.coeFn_sub, Pi.sub_apply, sub_div]

/-- **The norm is the weighted norm of `Cohomological.lean`:** `‖x‖ = ∑ |f_n| e^{r(|k|+|m|)}`. -/
theorem norm_eq_wnorm (x : WEll1Z2 r) : ‖x‖ = wnorm r (coeff x) := by
  change ‖toEll x‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
  exact tsum_congr fun n => norm_toEll_apply x n

/-- The coefficients of an element have finite weighted norm. -/
theorem inWeighted_coeff (x : WEll1Z2 r) : InWeighted r (coeff x) := by
  have h := (memℓp_one_iff' _).1 (lp.memℓp (toEll x))
  exact h.congr fun n => norm_toEll_apply x n

/-- The element of `ℓ¹_r(ℤ²)` with prescribed coefficients `f`, `‖f‖_r < ∞`. -/
def ofCoeff (f : ℤ × ℤ → ℂ) (hf : InWeighted r f) : WEll1Z2 r :=
  (⟨fun n => f n * (weight r n : ℂ), (memℓp_one_iff' _).2 (hf.congr fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (weight_pos r n).le])⟩ : Ell1Z2)

/-- `ofCoeff` has the prescribed coefficients. -/
@[simp] theorem coeff_ofCoeff (f : ℤ × ℤ → ℂ) (hf : InWeighted r f) (n : ℤ × ℤ) :
    coeff (ofCoeff f hf) n = f n := by
  have : (weight r n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos r n).ne'
  change f n * (weight r n : ℂ) / (weight r n : ℂ) = f n
  rw [mul_div_cancel_right₀ _ this]

/-- `‖ofCoeff f‖ = ‖f‖_r`. -/
theorem norm_ofCoeff (f : ℤ × ℤ → ℂ) (hf : InWeighted r f) : ‖ofCoeff f hf‖ = wnorm r f := by
  rw [norm_eq_wnorm]; congr 1; funext n; simp

/-- Reconstruction from the coefficients. -/
@[simp] theorem ofCoeff_coeff (x : WEll1Z2 r) : ofCoeff (coeff x) (inWeighted_coeff x) = x :=
  ext_coeff fun n => by simp

/-- Absolute summability of the coefficients for `r ≥ 0`. -/
theorem summable_norm_coeff (hr : 0 ≤ r) (x : WEll1Z2 r) : Summable fun n => ‖coeff x n‖ :=
  summable_norm_of_inWeighted hr (inWeighted_coeff x)

/-- Each coefficient is bounded: `‖f_n‖ e^{r(|k|+|m|)} ≤ ‖x‖_r`. -/
theorem norm_coeff_mul_weight_le (x : WEll1Z2 r) (n : ℤ × ℤ) :
    ‖coeff x n‖ * weight r n ≤ ‖x‖ := by
  rw [norm_eq_wnorm]; exact norm_mul_weight_le_wnorm (inWeighted_coeff x) n

/-! ### Restriction to a narrower strip -/

/-- Restriction `ℓ¹_r → ℓ¹_{r'}` for `r' ≤ r` (same coefficients). -/
def restrict {r' : ℝ} (h : r' ≤ r) (x : WEll1Z2 r) : WEll1Z2 r' :=
  ofCoeff (coeff x) ((inWeighted_coeff x).mono h)

/-- Restriction keeps the coefficients. -/
@[simp] theorem coeff_restrict {r' : ℝ} (h : r' ≤ r) (x : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (restrict h x) n = coeff x n := by simp [restrict]

/-- **Monotonicity:** `‖x‖_{r'} ≤ ‖x‖_r` for `r' ≤ r`. -/
theorem norm_restrict_le {r' : ℝ} (h : r' ≤ r) (x : WEll1Z2 r) : ‖restrict h x‖ ≤ ‖x‖ := by
  rw [restrict, norm_ofCoeff, norm_eq_wnorm]; exact wnorm_mono (inWeighted_coeff x) h

/-- Restriction is additive. -/
theorem restrict_add {r' : ℝ} (h : r' ≤ r) (x y : WEll1Z2 r) :
    restrict h (x + y) = restrict h x + restrict h y := ext_coeff fun n => by simp

/-- Restriction is `ℂ`-linear. -/
theorem restrict_smul {r' : ℝ} (h : r' ≤ r) (c : ℂ) (x : WEll1Z2 r) :
    restrict h (c • x) = c • restrict h x := ext_coeff fun n => by simp

/-! ### Derivatives and the cohomological solver as bounded maps -/

/-- `∂_θ : ℓ¹_r → ℓ¹_{r−δ}`. -/
def dθL {δ : ℝ} (hδ : 0 < δ) (x : WEll1Z2 r) : WEll1Z2 (r - δ) :=
  ofCoeff (dθ (coeff x)) (dθ_estimate hδ (inWeighted_coeff x)).1

/-- `∂_ψ : ℓ¹_r → ℓ¹_{r−δ}`. -/
def dψL {δ : ℝ} (hδ : 0 < δ) (x : WEll1Z2 r) : WEll1Z2 (r - δ) :=
  ofCoeff (dψ (coeff x)) (dψ_estimate hδ (inWeighted_coeff x)).1

/-- Coefficients of `∂_θ x`. -/
@[simp] theorem coeff_dθL {δ : ℝ} (hδ : 0 < δ) (x : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (dθL hδ x) n = dθ (coeff x) n := by simp [dθL]

/-- Coefficients of `∂_ψ x`. -/
@[simp] theorem coeff_dψL {δ : ℝ} (hδ : 0 < δ) (x : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (dψL hδ x) n = dψ (coeff x) n := by simp [dψL]

/-- **Cauchy estimate** `‖∂_θ x‖_{r−δ} ≤ (eδ)⁻¹ ‖x‖_r`. -/
theorem norm_dθL_le {δ : ℝ} (hδ : 0 < δ) (x : WEll1Z2 r) :
    ‖dθL hδ x‖ ≤ (Real.exp 1 * δ)⁻¹ * ‖x‖ := by
  rw [dθL, norm_ofCoeff, norm_eq_wnorm]; exact (dθ_estimate hδ (inWeighted_coeff x)).2

/-- **Cauchy estimate** `‖∂_ψ x‖_{r−δ} ≤ (eδ)⁻¹ ‖x‖_r`. -/
theorem norm_dψL_le {δ : ℝ} (hδ : 0 < δ) (x : WEll1Z2 r) :
    ‖dψL hδ x‖ ≤ (Real.exp 1 * δ)⁻¹ * ‖x‖ := by
  rw [dψL, norm_ofCoeff, norm_eq_wnorm]; exact (dψ_estimate hδ (inWeighted_coeff x)).2

/-- The zero-mean solution of `L_ω u = f` as a map `ℓ¹_r → ℓ¹_{r−δ}` (`τ = 1`). -/
def cohSolL {ω γ δ : ℝ} (hD : Diophantine ω γ 1) (hγ : 0 < γ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 2 / Real.exp 1) (x : WEll1Z2 r) : WEll1Z2 (r - δ) :=
  ofCoeff (cohSol ω (coeff x)) (cohSol_estimate_one hD hγ hδ hδ2 (inWeighted_coeff x)).1

/-- **Rüssmann estimate** on the space: `‖u‖_{r−δ} ≤ ‖f‖_r / (eγδ)`. -/
theorem norm_cohSolL_le {ω γ δ : ℝ} (hD : Diophantine ω γ 1) (hγ : 0 < γ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 2 / Real.exp 1) (x : WEll1Z2 r) :
    ‖cohSolL hD hγ hδ hδ2 x‖ ≤ ‖x‖ / (Real.exp 1 * γ * δ) := by
  rw [cohSolL, norm_ofCoeff, norm_eq_wnorm]
  exact (cohSol_estimate_one hD hγ hδ hδ2 (inWeighted_coeff x)).2

/-- `cohSolL` solves `L_ω u = f` for zero-mean `f`. -/
theorem cohOp_cohSolL {ω γ δ : ℝ} (hD : Diophantine ω γ 1) (hγ : 0 < γ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 2 / Real.exp 1) (x : WEll1Z2 r) (hx : coeff x (0, 0) = 0) (n : ℤ × ℤ) :
    cohOp ω (coeff (cohSolL hD hγ hδ hδ2 x)) n = coeff x n := by
  have : coeff (cohSolL hD hγ hδ hδ2 x) = cohSol ω (coeff x) := by
    funext m; simp [cohSolL]
  rw [this]; exact cohSol_spec hD hγ hx n

/-! ### Evaluation -/

/-- The function `F(θ,ψ) = ∑ f_n e^{i(kθ+mψ)}` represented by `x`. -/
def eval (x : WEll1Z2 r) (θ ψ : ℝ) : ℂ := fourierSum (coeff x) θ ψ

/-- **Sup bound** `|F(θ,ψ)| ≤ ‖x‖_0 ≤ ‖x‖_r` for `r ≥ 0`. -/
theorem norm_eval_le (hr : 0 ≤ r) (x : WEll1Z2 r) (θ ψ : ℝ) : ‖eval x θ ψ‖ ≤ ‖x‖ := by
  obtain ⟨h1, h2⟩ := norm_fourierSum_le hr (inWeighted_coeff x) θ ψ
  rw [norm_eq_wnorm]; exact h1.trans h2

/-- **Sup bound on the complex strip** `|F(θ,ψ)| ≤ ‖x‖_r` for `|Im θ|, |Im ψ| ≤ r`. -/
theorem norm_evalC_le (x : WEll1Z2 r) {θ ψ : ℂ} (hθ : |θ.im| ≤ r) (hψ : |ψ.im| ≤ r) :
    ‖fourierSumC (coeff x) θ ψ‖ ≤ ‖x‖ := by
  rw [norm_eq_wnorm]; exact norm_fourierSumC_le (inWeighted_coeff x) hθ hψ

/-! ### The Banach-algebra structure (`r ≥ 0`) -/

/-- The unit `δ₀`. -/
instance : One (WEll1Z2 r) :=
  ⟨ofCoeff delta2 (by
    unfold InWeighted
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [delta2, Finset.mem_singleton.not.1 hn])⟩

/-- Coefficients of the unit. -/
@[simp] theorem coeff_one (n : ℤ × ℤ) : coeff (1 : WEll1Z2 r) n = delta2 n := by
  change coeff (ofCoeff _ _) n = _; simp

/-- Coefficients of a sum, as functions. -/
theorem coeff_add' (x y : WEll1Z2 r) : coeff (x + y) = coeff x + coeff y := by
  funext n; simp

/-- The unit evaluates to `1`. -/
theorem eval_one (θ ψ : ℝ) : eval (1 : WEll1Z2 r) θ ψ = 1 := by
  rw [eval, show coeff (1 : WEll1Z2 r) = delta2 from funext coeff_one, fourierSum_delta2]

section Algebra

variable [hr : Fact (0 ≤ r)]

/-- Multiplication is convolution of coefficients. -/
instance : Mul (WEll1Z2 r) :=
  ⟨fun x y => ofCoeff (cconv (coeff x) (coeff y))
    (inWeighted_cconv hr.out (inWeighted_coeff x) (inWeighted_coeff y))⟩

/-- Coefficients of a product. -/
@[simp] theorem coeff_mul (x y : WEll1Z2 r) (n : ℤ × ℤ) :
    coeff (x * y) n = cconv (coeff x) (coeff y) n := by
  change coeff (ofCoeff _ _) n = _; simp

/-- `coeff` as functions. -/
theorem coeff_mul' (x y : WEll1Z2 r) : coeff (x * y) = cconv (coeff x) (coeff y) := by
  funext n; simp

/-- `ℓ¹_r(ℤ²)` with convolution is a commutative ring (`r ≥ 0`). -/
instance instCommRing : CommRing (WEll1Z2 r) :=
  { (inferInstance : AddCommGroup (WEll1Z2 r)) with
    npow := npowRec
    npow_zero := fun _ => rfl
    npow_succ := fun _ _ => rfl
    mul_assoc := fun x y z => ext_coeff fun n => by
      simp only [coeff_mul', cconv_assoc (summable_norm_coeff hr.out x)
        (summable_norm_coeff hr.out y) (summable_norm_coeff hr.out z)]
    one_mul := fun x => ext_coeff fun n => by
      rw [coeff_mul', show coeff (1 : WEll1Z2 r) = delta2 from funext coeff_one,
        cconv_delta2_left]
    mul_one := fun x => ext_coeff fun n => by
      rw [coeff_mul', show coeff (1 : WEll1Z2 r) = delta2 from funext coeff_one,
        cconv_delta2_right]
    left_distrib := fun x y z => ext_coeff fun n => by
      rw [coeff_mul', coeff_add', cconv_comm, cconv_add_left (summable_norm_coeff hr.out y)
        (summable_norm_coeff hr.out z) (summable_norm_coeff hr.out x), coeff_add',
        coeff_mul', coeff_mul', cconv_comm (coeff x), cconv_comm (coeff x)]
    right_distrib := fun x y z => ext_coeff fun n => by
      rw [coeff_mul', coeff_add', cconv_add_left (summable_norm_coeff hr.out x)
        (summable_norm_coeff hr.out y) (summable_norm_coeff hr.out z), coeff_add',
        coeff_mul', coeff_mul']
    zero_mul := fun x => ext_coeff fun n => by
      rw [coeff_mul', show coeff (0 : WEll1Z2 r) = 0 from funext coeff_zero,
        cconv_zero_left]
    mul_zero := fun x => ext_coeff fun n => by
      rw [coeff_mul', show coeff (0 : WEll1Z2 r) = 0 from funext coeff_zero, cconv_comm,
        cconv_zero_left]
    mul_comm := fun x y => ext_coeff fun n => by rw [coeff_mul', coeff_mul', cconv_comm] }

/-- **Banach-algebra estimate** `‖x y‖_r ≤ ‖x‖_r ‖y‖_r`. -/
theorem norm_mul_le' (x y : WEll1Z2 r) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_wnorm, norm_eq_wnorm, norm_eq_wnorm, coeff_mul']
  exact wnorm_cconv_le hr.out (inWeighted_coeff x) (inWeighted_coeff y)

/-- `ℓ¹_r(ℤ²)` is a normed commutative ring (`r ≥ 0`). -/
instance instNormedCommRing : NormedCommRing (WEll1Z2 r) :=
  { (inferInstance : NormedAddCommGroup (WEll1Z2 r)), instCommRing with
    norm_mul_le := norm_mul_le' }

/-- `‖δ₀‖_r = 1`. -/
instance : NormOneClass (WEll1Z2 r) :=
  ⟨by
    rw [norm_eq_wnorm, show coeff (1 : WEll1Z2 r) = delta2 from funext coeff_one, wnorm,
      tsum_eq_single 0 (fun n hn => by simp [delta2, hn])]
    simp [delta2]⟩

/-- `ℓ¹_r(ℤ²)` is a `ℂ`-algebra. -/
instance instAlgebra : Algebra ℂ (WEll1Z2 r) :=
  Algebra.ofModule
    (fun c x y => ext_coeff fun n => by
      rw [coeff_smul, coeff_mul', coeff_mul',
        show coeff (c • x) = c • coeff x from funext fun m => coeff_smul c x m,
        cconv_smul_left]; rfl)
    (fun c x y => ext_coeff fun n => by
      rw [coeff_smul, coeff_mul', coeff_mul',
        show coeff (c • y) = c • coeff y from funext fun m => coeff_smul c y m,
        cconv_comm (coeff x), cconv_smul_left, cconv_comm (coeff y)]; rfl)

/-- `ℓ¹_r(ℤ²)` is a normed `ℂ`-algebra (a commutative unital Banach algebra, `r ≥ 0`). -/
instance : NormedAlgebra ℂ (WEll1Z2 r) :=
  { instAlgebra with norm_smul_le := fun c x => norm_smul_le c x }

/-- Evaluation is a ring homomorphism: `F_{xy} = F_x F_y`. -/
theorem eval_mul (x y : WEll1Z2 r) (θ ψ : ℝ) : eval (x * y) θ ψ = eval x θ ψ * eval y θ ψ := by
  rw [eval, coeff_mul']
  exact fourierSum_cconv (summable_norm_coeff hr.out x) (summable_norm_coeff hr.out y) θ ψ

/-- Restriction to a narrower strip `0 ≤ r' ≤ r` is multiplicative. -/
theorem restrict_mul {r' : ℝ} [Fact (0 ≤ r')] (h : r' ≤ r) (x y : WEll1Z2 r) :
    restrict h (x * y) = restrict h x * restrict h y :=
  ext_coeff fun n => by
    simp only [coeff_restrict, coeff_mul]
    congr 1 <;> funext m <;> simp

/-- **Neumann series.** If `‖a‖_r < 1` then `1 + a` is invertible in `ℓ¹_r(ℤ²)` and
`‖(1 + a)⁻¹‖_r ≤ 1 / (1 − ‖a‖_r)`. -/
theorem neumann (a : WEll1Z2 r) (ha : ‖a‖ < 1) :
    IsUnit (1 + a) ∧ ‖Ring.inverse (1 + a)‖ ≤ 1 / (1 - ‖a‖) := by
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  have h1 : (1 : WEll1Z2 r) + a = 1 - -a := by rw [sub_neg_eq_add]
  refine ⟨h1 ▸ isUnit_one_sub_of_norm_lt_one hna, ?_⟩
  rw [h1, ← geom_series_eq_inverse (-a) hna]
  have := tsum_geometric_le_of_norm_lt_one (-a) hna
  rw [norm_one, norm_neg, sub_self, zero_add] at this
  rwa [one_div]

/-- The inverse given by `neumann` is a two-sided inverse. -/
theorem neumann_mul_inverse (a : WEll1Z2 r) (ha : ‖a‖ < 1) :
    (1 + a) * Ring.inverse (1 + a) = 1 ∧ Ring.inverse (1 + a) * (1 + a) = 1 :=
  ⟨Ring.mul_inverse_cancel _ (neumann a ha).1, Ring.inverse_mul_cancel _ (neumann a ha).1⟩

/-- **Neumann series near `1`.** If `‖b − 1‖_r < 1` then `b` is invertible and
`‖b⁻¹‖_r ≤ 1 / (1 − ‖b − 1‖_r)` (used for `D⁻¹` and frame inverses). -/
theorem neumann_near_one (b : WEll1Z2 r) (hb : ‖b - 1‖ < 1) :
    IsUnit b ∧ ‖Ring.inverse b‖ ≤ 1 / (1 - ‖b - 1‖) := by
  have := neumann (b - 1) hb
  rwa [add_sub_cancel] at this

end Algebra

/-! ### Sanity checks -/

/-- The single Fourier mode `e^{i(kθ+mψ)}` as an element of `ℓ¹_r(ℤ²)`. -/
def mode (r : ℝ) (km : ℤ × ℤ) : WEll1Z2 r :=
  ofCoeff (Pi.single km 1) (by
    unfold InWeighted
    refine summable_of_ne_finset_zero (s := {km}) fun n hn => ?_
    simp [Finset.mem_singleton.not.1 hn])

/-- Coefficients of a mode. -/
@[simp] theorem coeff_mode (km n : ℤ × ℤ) :
    coeff (mode r km) n = (Pi.single km (1 : ℂ) : ℤ × ℤ → ℂ) n := by
  simp [mode]

/-- Sanity (special case): `‖e^{i(kθ+mψ)}‖_r = e^{r(|k|+|m|)}`. -/
theorem norm_mode (km : ℤ × ℤ) : ‖mode r km‖ = weight r km := by
  rw [mode, norm_ofCoeff, wnorm, tsum_eq_single km (fun n hn => by simp [hn])]
  simp

/-- Sanity: the mode `(0,0)` is the unit. -/
theorem mode_zero : mode r 0 = 1 := ext_coeff fun n => by
  simp [delta2, Pi.single_apply]

/-- Sanity: modes multiply by adding frequencies,
`e^{i(kθ+mψ)} e^{i(k'θ+m'ψ)} = e^{i((k+k')θ+(m+m')ψ)}`. -/
theorem mode_mul [Fact (0 ≤ r)] (a b : ℤ × ℤ) : mode r a * mode r b = mode r (a + b) :=
  ext_coeff fun n => by
    rw [coeff_mul, coeff_mode, cconv,
      tsum_eq_single a (fun c hc => by simp [Pi.single_apply, hc])]
    simp only [coeff_mode, Pi.single_eq_same, one_mul, Pi.single_apply]
    by_cases h : n = a + b
    · subst h; simp
    · have h2 : n - a ≠ b := fun h' => h (by rw [← h']; abel)
      simp [h, h2]

/-- Sanity (degenerate case of `neumann`): `a = 0` gives `‖1⁻¹‖ ≤ 1`. -/
theorem neumann_zero [Fact (0 ≤ r)] : ‖Ring.inverse (1 + (0 : WEll1Z2 r))‖ ≤ 1 := by
  have := (neumann (0 : WEll1Z2 r) (by simp)).2
  simpa only [add_zero, norm_zero, sub_zero, div_one] using this

/-- Sanity (rejected fixture): at `‖a‖ = 1` the Neumann conclusion fails: `1 + (−1) = 0` is not
a unit, so the strict hypothesis `‖a‖ < 1` cannot be relaxed. -/
theorem not_isUnit_one_add_neg_one [Fact (0 ≤ r)] :
    ‖(-1 : WEll1Z2 r)‖ = 1 ∧ ¬ IsUnit ((1 : WEll1Z2 r) + -1) := by
  refine ⟨by simp, ?_⟩
  rw [add_neg_cancel]
  intro h
  have h1 : (1 : WEll1Z2 r) = 0 := by
    obtain ⟨u, hu⟩ := h
    rw [← u.mul_inv, hu, zero_mul]
  have := congrArg norm h1
  simp at this

end WEll1Z2

/-- Sanity (rejected fixture): for `r = −1 < 0` the Banach-algebra estimate fails:
`δ_{(1,0)} ⋆ δ_{(−1,0)} = δ₀` has norm `1 > e^{−1} e^{−1}`. -/
theorem cconv_not_submult_neg :
    wnorm (-1) (Pi.single ((1 : ℤ), (0 : ℤ)) 1) * wnorm (-1) (Pi.single ((-1 : ℤ), (0 : ℤ)) 1) <
      wnorm (-1) (cconv (Pi.single ((1 : ℤ), (0 : ℤ)) 1) (Pi.single ((-1 : ℤ), (0 : ℤ)) 1)) := by
  have hc : cconv (Pi.single ((1 : ℤ), (0 : ℤ)) (1 : ℂ)) (Pi.single ((-1 : ℤ), (0 : ℤ)) 1) =
      delta2 := by
    funext n
    rw [cconv, tsum_eq_single ((1 : ℤ), (0 : ℤ)) (fun c hc => by simp [Pi.single_apply, hc])]
    simp only [Pi.single_eq_same, one_mul, Pi.single_apply, delta2]
    by_cases h : n = 0
    · subst h; simp
    · have h2 : n - ((1 : ℤ), (0 : ℤ)) ≠ ((-1 : ℤ), (0 : ℤ)) := by
        intro h'
        apply h
        rw [sub_eq_iff_eq_add] at h'
        rw [h']; ext <;> simp
      simp [h, h2]
  have hs : ∀ km : ℤ × ℤ, wnorm (-1) (Pi.single km (1 : ℂ)) = weight (-1) km := fun km => by
    rw [wnorm, tsum_eq_single km (fun n hn => by simp [hn])]
    simp
  have h0 : wnorm (-1) delta2 = 1 := by
    rw [wnorm, tsum_eq_single 0 (fun n hn => by simp [delta2, hn])]
    simp [delta2]
  rw [hc, h0, hs, hs, weight, weight, ← Real.exp_add]
  rw [Real.exp_lt_one_iff]
  simp [modeSize]

end LeanTheory.Theory.KAM
