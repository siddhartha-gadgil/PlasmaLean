/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.StripPaleyWiener
public import PlasmaLean.Theory.Fields.BiotSavartComplex
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Joint holomorphy of complexified Fourier series and of the complexified torus map

Stage 1, gap 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). This file shows that
an absolutely convergent double Fourier series with exponential weights is **jointly**
holomorphic on the open product strip, and that the same holds for the complexified torus
embedding in cylindrical coordinates.

* `differentiableOn_fourierSumC`: for `u ∈ ℓ¹_r`, `(θ, ψ) ↦ ∑ u_n e^{i(kθ+mψ)}` is
  `ℂ`-differentiable on `stripC r ×ˢ stripC r` (`|Im θ|, |Im ψ| < r`). The proof uses Mathlib's
  `hasFDerivAt_tsum_of_isPreconnected` on the convex strip `|Im| < r'` for some `r' < r`, with
  the derivative bound `(|k|+|m|) e^{r'(|k|+|m|)} ≤ e^{r(|k|+|m|)}/(r − r')`.
* `fourierSumC_add_two_pi_left`, `fourierSumC_add_two_pi_right`: `2π`-periodicity at complex
  arguments; `fourierSumC_coeff_ofReal`: at real points the series of `x : FA` is `eval x`;
  `norm_fourierSumC_le_of_Bd`: `Bd ρ x B` bounds the series by `B` on the closed strip.
* `cylC R φ Z = (R cos φ, R sin φ, Z)`: the complexified cylindrical map. It is entire
  (`differentiable_cylC`) and extends the real map `cylR` (`cylC_ofReal`). The exact identities
  `norm_imV_cylC_sq` and `norm_reV_cylC_sub_sq` give
  `|Im cyl|² = (Im R)² cosh²(Im φ) + (Re R)² sinh²(Im φ) + (Im Z)²` and
  `|Re cyl − cylR(Re R, Re φ, Re Z)|² = (Re R)² (cosh(Im φ) − 1)² + (Im R)² sinh²(Im φ)`.
* `torusMapC u₁ u₂ θ ψ z₁ z₂ = cylC (F_{u₁}(θ,ψ) + z₁) ψ (F_{u₂}(θ,ψ) + z₂)`: the complexified
  torus embedding with offsets; `differentiableOn_torusMapC` (joint holomorphy on
  `(stripC r ×ˢ stripC r) ×ˢ univ`) and its periodicity `torusMapC_add_two_pi_left/right`.

**Sanity.** `fourierSumC_zero` (degenerate), `fourierSumC_delta2` (the constant mode),
`torusMapC_zero`, and the rejected fixture `not_norm_fourierModeC_le_one` (off the real torus
a mode is not unimodular: the strip weight cannot be dropped).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM.FourierSumHolo

open Complex Set Filter Topology WEll1Z2 PaleyWiener
open PlasmaLean.Fields PlasmaLean.Fields.BiotSavartComplex

/-! ## The open strip -/

/-- The open strip is open. -/
theorem isOpen_stripC (r : ℝ) : IsOpen (stripC r) :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

/-- The open strip is convex. -/
theorem convex_stripC (r : ℝ) : Convex ℝ (stripC r) := by
  intro x hx y hy a b ha hb hab
  simp only [stripC, Set.mem_ofPred_eq, abs_lt] at *
  have e : (a • x + b • y).im = a * x.im + b * y.im := by simp
  rw [e]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  constructor
  · set m := min (x.im + r) (y.im + r)
    have hm : 0 < m := lt_min (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (x.im + r) (y.im + r)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (x.im + r) (y.im + r)) hb
    nlinarith
  · set m := min (r - x.im) (r - y.im)
    have hm : 0 < m := lt_min (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (r - x.im) (r - y.im)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (r - x.im) (r - y.im)) hb
    nlinarith

/-- `x ≤ e^{δx}/δ` for `δ > 0`. -/
theorem le_exp_div {δ x : ℝ} (hδ : 0 < δ) : x ≤ Real.exp (δ * x) / δ := by
  rw [le_div_iff₀ hδ]
  have := Real.add_one_le_exp (δ * x)
  nlinarith

/-! ## Joint holomorphy of the Fourier series -/

/-- The phase `(θ, ψ) ↦ i(kθ + mψ)` as a continuous linear map. -/
def phaseL (km : ℤ × ℤ) : ℂ × ℂ →L[ℂ] ℂ :=
  I • ((km.1 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ + (km.2 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The phase map evaluates to `i(kθ + mψ)`. -/
theorem phaseL_apply (km : ℤ × ℤ) (p : ℂ × ℂ) : phaseL km p = I * (km.1 * p.1 + km.2 * p.2) := by
  simp [phaseL, smul_eq_mul]; ring

/-- `‖phase‖ ≤ |k| + |m|`. -/
theorem norm_phaseL_le (km : ℤ × ℤ) : ‖phaseL km‖ ≤ modeSize km := by
  unfold phaseL modeSize
  refine (norm_smul_le (I : ℂ) ((km.1 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (km.2 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ)).trans ?_
  rw [norm_I, one_mul]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_smul_le (km.1 : ℂ) (ContinuousLinearMap.fst ℂ ℂ ℂ)).trans ?_)
    ((norm_smul_le (km.2 : ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ)).trans ?_)
  · have := ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ
    have h : ‖(km.1 : ℂ)‖ = |(km.1 : ℝ)| := by simp
    rw [h]; nlinarith [abs_nonneg (km.1 : ℝ)]
  · have := ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ
    have h : ‖(km.2 : ℂ)‖ = |(km.2 : ℝ)| := by simp
    rw [h]; nlinarith [abs_nonneg (km.2 : ℝ)]

/-- The derivative of one term of the series. -/
theorem hasFDerivAt_term (u : ℤ × ℤ → ℂ) (km : ℤ × ℤ) (p : ℂ × ℂ) :
    HasFDerivAt (fun q : ℂ × ℂ => u km * fourierModeC km q.1 q.2)
      (u km • (Complex.exp (phaseL km p) • phaseL km)) p := by
  have h := ((phaseL km).hasFDerivAt (x := p)).cexp.const_mul (u km)
  have e : (fun q : ℂ × ℂ => u km * fourierModeC km q.1 q.2) =
      fun q => u km * Complex.exp (phaseL km q) := by
    funext q; rw [phaseL_apply]; rfl
  rw [e]; exact h

/-- The weight is monotone in the strip width. -/
theorem weight_mono {r r' : ℝ} (h : r' ≤ r) (km : ℤ × ℤ) : weight r' km ≤ weight r km := by
  unfold weight
  have : 0 ≤ modeSize km := by unfold modeSize; positivity
  exact Real.exp_le_exp.2 (by nlinarith)

/-- The strip `|Im θ|, |Im ψ| < r'` as a subset of `ℂ × ℂ`. -/
theorem holo_on_substrip {r r' : ℝ} {u : ℤ × ℤ → ℂ} (hu : InWeighted r u) (hr : r' < r)
    {p : ℂ × ℂ} (hp : p ∈ stripC r' ×ˢ stripC r') :
    HasFDerivAt (fun q : ℂ × ℂ => fourierSumC u q.1 q.2)
      (∑' km, u km • (Complex.exp (phaseL km p) • phaseL km)) p := by
  set s := stripC r' ×ˢ stripC r'
  have hs : IsOpen s := (isOpen_stripC r').prod (isOpen_stripC r')
  have hc : IsPreconnected s := ((convex_stripC r').prod (convex_stripC r')).isPreconnected
  set δ := r - r'
  have hδ : 0 < δ := sub_pos.2 hr
  have hbd : ∀ km (q : ℂ × ℂ), q ∈ s →
      ‖u km • (Complex.exp (phaseL km q) • phaseL km)‖ ≤ ‖u km‖ * weight r km / δ := by
    intro km q hq
    have hq1 : |q.1.im| ≤ r' := (show |q.1.im| < r' from hq.1).le
    have hq2 : |q.2.im| ≤ r' := (show |q.2.im| < r' from hq.2).le
    have hmode : ‖Complex.exp (phaseL km q)‖ ≤ weight r' km := by
      have := norm_fourierModeC_le hq1 hq2 km
      rw [phaseL_apply]; exact this
    have hW : weight r' km * modeSize km ≤ weight r km / δ := by
      have h1 := le_exp_div (x := modeSize km) hδ
      have e : weight r km = weight r' km * Real.exp (δ * modeSize km) := by
        unfold weight; rw [← Real.exp_add]; congr 1; simp only [δ]; ring
      rw [e, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    calc ‖u km • (Complex.exp (phaseL km q) • phaseL km)‖
        ≤ ‖u km‖ * (‖Complex.exp (phaseL km q)‖ * ‖phaseL km‖) := by
          rw [norm_smul, norm_smul]
      _ ≤ ‖u km‖ * (weight r' km * modeSize km) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hmode (norm_phaseL_le km)
            (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
      _ ≤ ‖u km‖ * (weight r km / δ) := by gcongr
      _ = ‖u km‖ * weight r km / δ := by ring
  have hsum : Summable fun km => ‖u km‖ * weight r km / δ := hu.div_const δ
  have hf0 : Summable fun km => u km * fourierModeC km p.1 p.2 := by
    refine Summable.of_norm_bounded hu fun km => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_fourierModeC_le (show |p.1.im| < r' from hp.1).le
      (show |p.2.im| < r' from hp.2).le km).trans (weight_mono hr.le km)
  exact hasFDerivAt_tsum_of_isPreconnected hsum hs hc
    (fun km q _ => hasFDerivAt_term u km q) hbd hp hf0 hp

/-- **Joint holomorphy of the complexified Fourier series** on the open product strip. -/
theorem differentiableOn_fourierSumC {r : ℝ} {u : ℤ × ℤ → ℂ} (hu : InWeighted r u) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => fourierSumC u p.1 p.2) (stripC r ×ˢ stripC r) := by
  intro p hp
  have h1 : |p.1.im| < r := hp.1
  have h2 : |p.2.im| < r := hp.2
  set m := max |p.1.im| |p.2.im|
  have hm : m < r := max_lt h1 h2
  set r' := (m + r) / 2
  have hr' : r' < r := by simp only [r']; linarith
  have hp' : p ∈ stripC r' ×ˢ stripC r' :=
    ⟨show |p.1.im| < r' by simp only [r']; linarith [le_max_left |p.1.im| |p.2.im|],
     show |p.2.im| < r' by simp only [r']; linarith [le_max_right |p.1.im| |p.2.im|]⟩
  exact (holo_on_substrip hu hr' hp').differentiableAt.differentiableWithinAt

/-! ## Periodicity, real values and bounds -/

/-- A mode is `2π`-periodic in `θ` (complex arguments). -/
theorem fourierModeC_add_two_pi_left (km : ℤ × ℤ) (θ ψ : ℂ) :
    fourierModeC km (θ + 2 * Real.pi) ψ = fourierModeC km θ ψ := by
  unfold fourierModeC
  have e : I * (km.1 * (θ + 2 * Real.pi) + km.2 * ψ) =
      I * (km.1 * θ + km.2 * ψ) + km.1 * (2 * Real.pi * I) := by ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A mode is `2π`-periodic in `ψ` (complex arguments). -/
theorem fourierModeC_add_two_pi_right (km : ℤ × ℤ) (θ ψ : ℂ) :
    fourierModeC km θ (ψ + 2 * Real.pi) = fourierModeC km θ ψ := by
  unfold fourierModeC
  have e : I * (km.1 * θ + km.2 * (ψ + 2 * Real.pi)) =
      I * (km.1 * θ + km.2 * ψ) + km.2 * (2 * Real.pi * I) := by ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The complexified series is `2π`-periodic in `θ`. -/
theorem fourierSumC_add_two_pi_left (u : ℤ × ℤ → ℂ) (θ ψ : ℂ) :
    fourierSumC u (θ + 2 * Real.pi) ψ = fourierSumC u θ ψ := by
  unfold fourierSumC; simp only [fourierModeC_add_two_pi_left]

/-- The complexified series is `2π`-periodic in `ψ`. -/
theorem fourierSumC_add_two_pi_right (u : ℤ × ℤ → ℂ) (θ ψ : ℂ) :
    fourierSumC u θ (ψ + 2 * Real.pi) = fourierSumC u θ ψ := by
  unfold fourierSumC; simp only [fourierModeC_add_two_pi_right]

/-- At real points the complexified series of `x ∈ 𝔸` is the function of `x`. -/
theorem fourierSumC_coeff_ofReal (x : FA) (θ ψ : ℝ) :
    fourierSumC (coeff x) θ ψ = WEll1Z2.eval x θ ψ :=
  fourierSumC_ofReal _ θ ψ

/-- A strip bound `Bd ρ x B` bounds the complexified series by `B` on `|Im θ|, |Im ψ| ≤ ρ`. -/
theorem norm_fourierSumC_le_of_Bd {ρ B : ℝ} {x : FA} (hx : Bd ρ x B) {θ ψ : ℂ}
    (hθ : |θ.im| ≤ ρ) (hψ : |ψ.im| ≤ ρ) : ‖fourierSumC (coeff x) θ ψ‖ ≤ B :=
  (norm_fourierSumC_le hx.1 hθ hψ).trans hx.2

/-- Joint holomorphy of the series of `x ∈ 𝔸` with `Bd ρ x B`. -/
theorem differentiableOn_fourierSumC_of_Bd {ρ B : ℝ} {x : FA} (hx : Bd ρ x B) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => fourierSumC (coeff x) p.1 p.2)
      (stripC ρ ×ˢ stripC ρ) :=
  differentiableOn_fourierSumC hx.1

/-! ## Complexified cylindrical coordinates -/

/-- `Re cos z = cos (Re z) cosh (Im z)`. -/
theorem re_cos (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

/-- `Im cos z = −sin (Re z) sinh (Im z)`. -/
theorem im_cos (z : ℂ) : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

/-- `Re sin z = sin (Re z) cosh (Im z)`. -/
theorem re_sin (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

/-- `Im sin z = cos (Re z) sinh (Im z)`. -/
theorem im_sin (z : ℂ) : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

/-- The complexified cylindrical map `(R, φ, Z) ↦ (R cos φ, R sin φ, Z)`. -/
def cylC (R φ Z : ℂ) : CVec := ![R * Complex.cos φ, R * Complex.sin φ, Z]

/-- The real cylindrical map `(R, φ, Z) ↦ (R cos φ, R sin φ, Z)`. -/
def cylR (R φ Z : ℝ) : Space := WithLp.toLp 2 ![R * Real.cos φ, R * Real.sin φ, Z]

/-- The complexified cylindrical map is entire (jointly in `(R, φ, Z)`). -/
theorem differentiable_cylC :
    Differentiable ℂ (fun q : ℂ × ℂ × ℂ => cylC q.1 q.2.1 q.2.2) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · change Differentiable ℂ fun q : ℂ × ℂ × ℂ => q.1 * Complex.cos q.2.1
    fun_prop
  · change Differentiable ℂ fun q : ℂ × ℂ × ℂ => q.1 * Complex.sin q.2.1
    fun_prop
  · change Differentiable ℂ fun q : ℂ × ℂ × ℂ => q.2.2
    fun_prop

/-- At real arguments the complexified cylindrical map extends the real one. -/
theorem cylC_ofReal (R φ Z : ℝ) : cylC R φ Z = ofRealV (cylR R φ Z) := by
  funext i
  fin_cases i <;> simp [cylC, cylR, ofRealV]

/-- `2π`-periodicity of the cylindrical map in the angle. -/
theorem cylC_add_two_pi (R φ Z : ℂ) : cylC R (φ + 2 * Real.pi) Z = cylC R φ Z := by
  simp [cylC, Complex.cos_add_two_pi, Complex.sin_add_two_pi]

/-- **Imaginary part of the cylindrical map** (exact):
`|Im cyl|² = (Im R)² cosh²(Im φ) + (Re R)² sinh²(Im φ) + (Im Z)²`. -/
theorem norm_imV_cylC_sq (R φ Z : ℂ) :
    ‖imV (cylC R φ Z)‖ ^ 2 = R.im ^ 2 * Real.cosh φ.im ^ 2 + R.re ^ 2 * Real.sinh φ.im ^ 2 +
      Z.im ^ 2 := by
  rw [norm_sq_space]
  simp only [imV_apply, cylC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Complex.mul_im, re_cos, im_cos,
    re_sin, im_sin]
  linear_combination (R.im ^ 2 * Real.cosh φ.im ^ 2 + R.re ^ 2 * Real.sinh φ.im ^ 2) *
    Real.sin_sq_add_cos_sq φ.re

/-- **Real part of the cylindrical map** (exact):
`|Re cyl − cylR(Re R, Re φ, Re Z)|² = (Re R)² (cosh(Im φ) − 1)² + (Im R)² sinh²(Im φ)`. -/
theorem norm_reV_cylC_sub_sq (R φ Z : ℂ) :
    ‖reV (cylC R φ Z) - cylR R.re φ.re Z.re‖ ^ 2 =
      R.re ^ 2 * (Real.cosh φ.im - 1) ^ 2 + R.im ^ 2 * Real.sinh φ.im ^ 2 := by
  rw [norm_sq_space]
  simp only [PiLp.sub_apply, reV_apply, cylC, cylR, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Complex.mul_re, re_cos, im_cos, re_sin, im_sin]
  linear_combination (R.re ^ 2 * (Real.cosh φ.im - 1) ^ 2 + R.im ^ 2 * Real.sinh φ.im ^ 2) *
    Real.sin_sq_add_cos_sq φ.re

/-! ## The complexified torus map -/

/-- The complexified torus embedding with offsets:
`(θ, ψ, z₁, z₂) ↦ cyl(F_{u₁}(θ,ψ) + z₁, ψ, F_{u₂}(θ,ψ) + z₂)`. -/
def torusMapC (u₁ u₂ : ℤ × ℤ → ℂ) (θ ψ z₁ z₂ : ℂ) : CVec :=
  cylC (fourierSumC u₁ θ ψ + z₁) ψ (fourierSumC u₂ θ ψ + z₂)

/-- **Joint holomorphy of the complexified torus map** on `(stripC r ×ˢ stripC r) ×ˢ univ`. -/
theorem differentiableOn_torusMapC {r : ℝ} {u₁ u₂ : ℤ × ℤ → ℂ} (hu₁ : InWeighted r u₁)
    (hu₂ : InWeighted r u₂) :
    DifferentiableOn ℂ (fun p : (ℂ × ℂ) × (ℂ × ℂ) => torusMapC u₁ u₂ p.1.1 p.1.2 p.2.1 p.2.2)
      ((stripC r ×ˢ stripC r) ×ˢ univ) := by
  have hfst : DifferentiableOn ℂ (fun p : (ℂ × ℂ) × (ℂ × ℂ) => p.1)
      ((stripC r ×ˢ stripC r) ×ˢ univ) := differentiableOn_fst
  have hmap : MapsTo (fun p : (ℂ × ℂ) × (ℂ × ℂ) => p.1) ((stripC r ×ˢ stripC r) ×ˢ univ)
      (stripC r ×ˢ stripC r) := fun p hp => hp.1
  have h1 := (differentiableOn_fourierSumC hu₁).comp hfst hmap
  have h2 := (differentiableOn_fourierSumC hu₂).comp hfst hmap
  have hin : DifferentiableOn ℂ (fun p : (ℂ × ℂ) × (ℂ × ℂ) =>
      (fourierSumC u₁ p.1.1 p.1.2 + p.2.1, p.1.2, fourierSumC u₂ p.1.1 p.1.2 + p.2.2))
      ((stripC r ×ˢ stripC r) ×ˢ univ) := by
    refine DifferentiableOn.prodMk (h1.add (by fun_prop)) (DifferentiableOn.prodMk
      (by fun_prop) (h2.add (by fun_prop)))
  exact differentiable_cylC.comp_differentiableOn hin

/-- The torus map is `2π`-periodic in `θ`. -/
theorem torusMapC_add_two_pi_left (u₁ u₂ : ℤ × ℤ → ℂ) (θ ψ z₁ z₂ : ℂ) :
    torusMapC u₁ u₂ (θ + 2 * Real.pi) ψ z₁ z₂ = torusMapC u₁ u₂ θ ψ z₁ z₂ := by
  simp only [torusMapC, fourierSumC_add_two_pi_left]

/-- The torus map is `2π`-periodic in `ψ` (both through the series and the angle). -/
theorem torusMapC_add_two_pi_right (u₁ u₂ : ℤ × ℤ → ℂ) (θ ψ z₁ z₂ : ℂ) :
    torusMapC u₁ u₂ θ (ψ + 2 * Real.pi) z₁ z₂ = torusMapC u₁ u₂ θ ψ z₁ z₂ := by
  simp only [torusMapC, fourierSumC_add_two_pi_right, cylC_add_two_pi]

/-! ## Sanity checks -/

/-- Degenerate case: the zero series vanishes. -/
theorem fourierSumC_zero (θ ψ : ℂ) : fourierSumC (0 : ℤ × ℤ → ℂ) θ ψ = 0 := by
  simp [fourierSumC]

/-- Mode fixture: the series of `δ₀` is the constant `1`, also off the real torus. -/
theorem fourierSumC_delta2 (θ ψ : ℂ) : fourierSumC delta2 θ ψ = 1 := by
  unfold fourierSumC
  rw [tsum_eq_single 0 (fun a ha => by simp [delta2, ha])]
  simp [delta2, fourierModeC]

/-- Degenerate torus: with zero coefficients the torus map is the cylindrical map of the
offsets. -/
theorem torusMapC_zero (θ ψ z₁ z₂ : ℂ) : torusMapC 0 0 θ ψ z₁ z₂ = cylC z₁ ψ z₂ := by
  simp [torusMapC, fourierSumC_zero]

/-- Rejected fixture: off the real torus a mode is not bounded by `1`
(`|e^{iθ}| = e` at `θ = −i`), so the strip weight `e^{r(|k|+|m|)}` cannot be dropped. -/
theorem not_norm_fourierModeC_le_one : ¬ ‖fourierModeC (1, 0) (-I) 0‖ ≤ 1 := by
  have e : fourierModeC (1, 0) (-I) 0 = Complex.exp 1 := by
    unfold fourierModeC; congr 1; push_cast; ring_nf; simp
  rw [e, Complex.norm_exp, Complex.one_re, not_le]
  exact Real.one_lt_exp_iff.2 one_pos

end PlasmaLean.Theory.KAM.FourierSumHolo
