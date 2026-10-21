/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.StripEval
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Paley–Wiener bounds on the strip and certified aliasing

Stage 1 of the coil-field KAM (`notes/theory/after-kam.md` §2.2–2.4, target 1 option (a)):
the bridge from *analytic bounds on a complex strip* plus *finitely many real samples* to the
weighted `ℓ¹_r(ℤ²)` norm of the strip algebra `𝔸` (`Theory/KAM/StripAlgebra`).

**Cauchy / Paley–Wiener direction.**
* `integral_eq_integral_shift`: for a `2π`-periodic function holomorphic on the closed rectangle
  `[0,2π] × [0,y]`, `∫₀^{2π} g(x) dx = ∫₀^{2π} g(x + iy) dx` (Mathlib's rectangle Cauchy theorem;
  the vertical sides cancel by periodicity).
* `iterated_integral_shift`: the two-variable version for `f(θ,ψ)` biperiodic and jointly
  holomorphic on the product strip `|Im θ|, |Im ψ| < ρ'` (Fubini for continuous functions,
  `integral_integral_swap_of_continuous`, between the two shifts).
* `norm_fcoeff2_le`: if moreover `|f| ≤ M` on `|Im θ|, |Im ψ| ≤ ρ` (`0 ≤ ρ < ρ'`), the Fourier
  coefficients satisfy `|f_{k,m}| ≤ M e^{-ρ(|k|+|m|)}`.
* `norm_coeff_le_of_holo`, `Bd_of_holo`: for `x ∈ 𝔸` with `F_x = f` on the real torus,
  `|x_{k,m}| ≤ M e^{-ρ(|k|+|m|)}` and, for `r < ρ`, `‖x‖_r ≤ M ((1+q)/(1-q))²`, `q = e^{-(ρ-r)}`
  (`wnorm_le_of_decay`, with the two-sided geometric sums `hasSum_geoZ`, `hasSum_tailZ`).

**Sampling / aliasing direction.**
* `dft2 F N₁ N₂ n`: the discrete Fourier transform of the `N₁ × N₂` grid samples of `F`.
* `dft2_eval` (aliasing identity): `dft_n(F_x) = ∑_{p ≡ n mod (N₁,N₂)} x_p`, from the discrete
  orthogonality `sum_mode_samples` (roots of unity, `sum_roots_of_unity`).
* `wnorm_le_dft`: for `N_i > 2K_i`,
  `‖x‖_r ≤ ∑_{|k|≤K₁,|m|≤K₂} |dft_{k,m}| e^{r(|k|+|m|)} + 2 ∑_{p ∉ box} |x_p| e^{r(|p_1|+|p_2|)}`
  (aliases of box frequencies are outside the box, have larger weight, and each is counted once).
* `tsum_outMass_le`: with `|x_p| ≤ M e^{-ρ|p|}` the outside mass is at most
  `M · geoZ q · (tailZ q K₁ + tailZ q K₂)`, `tailZ q K = 2q^{K+1}/(1-q)`.
* `Bd_of_samples` (**the residual-certificate interface**): analyticity bound `M` on the strip
  `ρ` + the DFT of the real samples of `f` ⇒ an explicit `Bd r x B`. In stage 2 the samples are
  evaluated exactly (interval arithmetic) and `M` comes from `BiotSavartComplex.segFieldC_bound`.

**Sanity.** `dft2_mode` (the DFT of a mode is the alias indicator), the rejected fixture
`dft2_alias_fixture` (`e^{iNθ}` has DFT `1` at `0` on `N` samples but coefficient `0`: the tail
term cannot be dropped), `geoZ_zero`, `tailZ_zero`, `tailZ_le_geoZ`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM.PaleyWiener

open Complex MeasureTheory intervalIntegral Set WEll1Z2
open scoped Interval

/-- The open complex strip `|Im w| < r`. -/
def stripC (r : ℝ) : Set ℂ := {w | |w.im| < r}

/-- The character `w ↦ e^{-ikw}` at complex arguments. -/
def ex (k : ℤ) (w : ℂ) : ℂ := Complex.exp (-(k : ℂ) * w * I)

/-- `e^{-ikw}` is `2π`-periodic. -/
theorem ex_add_two_pi (k : ℤ) (w : ℂ) : ex k (w + 2 * Real.pi) = ex k w := by
  unfold ex
  have : -(k : ℂ) * (w + 2 * Real.pi) * I =
      -(k : ℂ) * w * I + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `|e^{-ik(x + iy)}| = e^{ky}`. -/
theorem norm_ex (k : ℤ) (x y : ℝ) : ‖ex k (x + y * I)‖ = Real.exp (k * y) := by
  unfold ex
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- At real points the character is the Fourier kernel used in `coeff_eq_integral`. -/
theorem ex_ofReal (k : ℤ) (θ : ℝ) :
    ex k θ = Complex.exp (((-k * θ : ℝ) : ℂ) * I) := by
  unfold ex; push_cast; ring_nf

/-- **Contour shift** for a `2π`-periodic function holomorphic on the closed rectangle
`[0, 2π] × [0, y]`: the integral over `[0, 2π]` can be moved to the line `Im w = y`
(the vertical sides cancel by periodicity). -/
theorem integral_eq_integral_shift {g : ℂ → ℂ} (hper : ∀ w, g (w + 2 * Real.pi) = g w) {y : ℝ}
    (hd : DifferentiableOn ℂ g ([[(0 : ℝ), 2 * Real.pi]] ×ℂ [[(0 : ℝ), y]])) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), g x = ∫ x in (0 : ℝ)..(2 * Real.pi), g (x + y * I) := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn g 0 (((2 * Real.pi : ℝ) : ℂ) + y * I)
    (by simpa using hd)
  have hv : (fun t : ℝ => g ((((2 * Real.pi : ℝ) : ℂ) + y * I).re + t * I)) =
      fun t : ℝ => g (t * I) := by
    funext t
    have : (((2 * Real.pi : ℝ) : ℂ) + y * I).re = 2 * Real.pi := by simp
    rw [this, add_comm]; exact_mod_cast hper (t * I)
  simp only [hv] at h
  simp only [zero_re, zero_im, ofReal_zero, zero_mul, add_zero, add_re, ofReal_re, mul_re, I_re,
    mul_zero, ofReal_im, I_im, mul_one, sub_self, add_im, mul_im, zero_add] at h
  linear_combination h

/-- The closed rectangle of height `y` lies in the strip of width `r > |y|`. -/
theorem rect_subset_strip {y r : ℝ} (hy : |y| < r) :
    [[(0 : ℝ), 2 * Real.pi]] ×ℂ [[(0 : ℝ), y]] ⊆ stripC r := by
  intro w hw
  rw [Complex.mem_reProdIm] at hw
  have h2 := hw.2
  rw [Set.mem_uIcc] at h2
  change |w.im| < r
  have : |w.im| ≤ |y| := by
    rcases h2 with h | h
    · simpa using abs_le_max_abs_abs h.1 h.2
    · simpa using abs_le_max_abs_abs h.1 h.2
  linarith

/-- Contour shift for `h(w) e^{-ikw}` with `h` periodic and holomorphic on the strip `|Im| < r`,
`|y| < r`. -/
theorem integral_mul_ex_shift {h : ℂ → ℂ} {r y : ℝ} (hper : ∀ w, h (w + 2 * Real.pi) = h w)
    (hd : DifferentiableOn ℂ h (stripC r)) (hy : |y| < r) (k : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), h x * ex k x =
      ∫ x in (0 : ℝ)..(2 * Real.pi), h (x + y * I) * ex k (x + y * I) := by
  have hex : Differentiable ℂ (ex k) := fun w => by
    unfold ex
    exact ((differentiableAt_id.const_mul _).mul_const I).cexp
  refine integral_eq_integral_shift (g := fun w => h w * ex k w) (fun w => ?_) ?_
  · simp only [hper, ex_add_two_pi]
  · exact (hd.mono (rect_subset_strip hy)).mul hex.differentiableOn

/-- **Fubini for continuous functions** on a rectangle (interval-integral form). -/
theorem integral_integral_swap_of_continuous {H : ℝ → ℝ → ℂ}
    (hH : Continuous fun q : ℝ × ℝ => H q.1 q.2) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ ψ in c..d, ∫ θ in a..b, H θ ψ = ∫ θ in a..b, ∫ ψ in c..d, H θ ψ := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hint : Integrable (Function.uncurry fun ψ θ => H θ ψ)
      ((volume.restrict (Ioc c d)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : Continuous (Function.uncurry fun ψ θ => H θ ψ) := hH.comp continuous_swap
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact MeasureTheory.integral_integral_swap hint

/-- The real points `x + iy` with `|y| < r` lie in the strip. -/
theorem mem_stripC {x y r : ℝ} (hy : |y| < r) : (x : ℂ) + y * I ∈ stripC r := by
  simpa [stripC] using hy

section TwoD

variable {f : ℂ → ℂ → ℂ} {ρ' : ℝ}

/-- Holomorphy in the first variable, from joint holomorphy on the product strip. -/
theorem differentiableOn_fst
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    {ψ : ℂ} (hψ : ψ ∈ stripC ρ') : DifferentiableOn ℂ (fun θ => f θ ψ) (stripC ρ') := by
  have : DifferentiableOn ℂ (fun θ : ℂ => (θ, ψ)) (stripC ρ') := by fun_prop
  exact hd.comp this fun θ hθ => ⟨hθ, hψ⟩

/-- Holomorphy in the second variable, from joint holomorphy on the product strip. -/
theorem differentiableOn_snd
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    {θ : ℂ} (hθ : θ ∈ stripC ρ') : DifferentiableOn ℂ (fun ψ => f θ ψ) (stripC ρ') := by
  have : DifferentiableOn ℂ (fun ψ : ℂ => (θ, ψ)) (stripC ρ') := by fun_prop
  exact hd.comp this fun ψ hψ => ⟨hθ, hψ⟩

/-- Joint continuity on a horizontal real plane `Im θ = y₁`, `Im ψ = y₂` inside the strip. -/
theorem continuous_shift
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    {y₁ y₂ : ℝ} (h₁ : |y₁| < ρ') (h₂ : |y₂| < ρ') :
    Continuous fun q : ℝ × ℝ => f (q.1 + y₁ * I) (q.2 + y₂ * I) := by
  have hg : Continuous fun q : ℝ × ℝ => ((q.1 : ℂ) + y₁ * I, (q.2 : ℂ) + y₂ * I) := by
    fun_prop
  exact hd.continuousOn.comp_continuous hg fun q => ⟨mem_stripC h₁, mem_stripC h₂⟩

/-- **Two-dimensional contour shift**: for `f` biperiodic and holomorphic on the product strip
`|Im θ|, |Im ψ| < ρ'`, the iterated Fourier integral can be moved to `Im θ = y₁`, `Im ψ = y₂`. -/
theorem iterated_integral_shift
    (hper1 : ∀ θ ψ, f (θ + 2 * Real.pi) ψ = f θ ψ) (hper2 : ∀ θ ψ, f θ (ψ + 2 * Real.pi) = f θ ψ)
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    {y₁ y₂ : ℝ} (h₁ : |y₁| < ρ') (h₂ : |y₂| < ρ') (k m : ℤ) :
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ ψ * ex k θ) * ex m ψ =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ ψ in (0 : ℝ)..(2 * Real.pi),
        f (θ + y₁ * I) (ψ + y₂ * I) * ex k (θ + y₁ * I) * ex m (ψ + y₂ * I) := by
  have hρ0 : |(0 : ℝ)| < ρ' := by simpa using (abs_nonneg y₁).trans_lt h₁
  -- shift in `θ` for each real `ψ`
  have step1 : ∀ ψ : ℝ, (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ ψ * ex k θ) * ex m ψ =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f (θ + y₁ * I) ψ * ex k (θ + y₁ * I) * ex m ψ := by
    intro ψ
    rw [integral_mul_ex_shift (h := fun θ => f θ ψ) (fun w => hper1 w ψ)
      (differentiableOn_fst hd (by simpa using mem_stripC (x := ψ) hρ0)) h₁ k,
      ← intervalIntegral.integral_mul_const]
  simp_rw [step1]
  -- Fubini
  rw [integral_integral_swap_of_continuous (H := fun θ ψ : ℝ =>
      f (θ + y₁ * I) ψ * ex k (θ + y₁ * I) * ex m ψ) ?_ Real.two_pi_pos.le Real.two_pi_pos.le]
  · -- shift in `ψ` for each real `θ`
    refine intervalIntegral.integral_congr fun θ _ => ?_
    exact integral_mul_ex_shift (h := fun ψ => f (θ + y₁ * I) ψ * ex k (θ + y₁ * I))
      (fun w => by simp only [hper2]) ((differentiableOn_snd hd (mem_stripC h₁)).mul_const _) h₂ m
  · have hc := continuous_shift hd h₁ hρ0
    simp only [ofReal_zero, zero_mul, add_zero] at hc
    unfold ex
    exact (hc.mul (by fun_prop)).mul (by fun_prop)

/-- The iterated Fourier coefficient `(4π²)⁻¹ ∫∫ f(θ,ψ) e^{-i(kθ+mψ)}` of a function given at
complex points (only its real values enter). -/
def fcoeff2 (f : ℂ → ℂ → ℂ) (k m : ℤ) : ℂ :=
  ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ ψ * ex k θ) * ex m ψ

/-- The sign choice `y = ∓ρ` making `k y = -ρ|k|`. -/
theorem mul_sgnShift (k : ℤ) (ρ : ℝ) :
    (k : ℝ) * (if 0 ≤ k then -ρ else ρ) = -ρ * |(k : ℝ)| := by
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast h)]; ring
  · rw [abs_of_neg (by exact_mod_cast not_le.1 h)]; ring

/-- `|∓ρ| = ρ`. -/
theorem abs_sgnShift (k : ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) : |(if 0 ≤ k then -ρ else ρ)| = ρ := by
  split_ifs <;> simp [abs_of_nonneg hρ]

/-- **Cauchy / Paley–Wiener estimate on the bi-strip.** If `f` is `2π`-periodic in both
variables, holomorphic on `|Im θ|, |Im ψ| < ρ'` and bounded by `M` on `|Im θ|, |Im ψ| ≤ ρ`
(`0 ≤ ρ < ρ'`), then `|f_{k,m}| ≤ M e^{-ρ(|k|+|m|)}`. -/
theorem norm_fcoeff2_le
    (hper1 : ∀ θ ψ, f (θ + 2 * Real.pi) ψ = f θ ψ) (hper2 : ∀ θ ψ, f θ (ψ + 2 * Real.pi) = f θ ψ)
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    {ρ M : ℝ} (hρ : 0 ≤ ρ) (hρρ : ρ < ρ')
    (hb : ∀ θ ψ : ℂ, |θ.im| ≤ ρ → |ψ.im| ≤ ρ → ‖f θ ψ‖ ≤ M) (k m : ℤ) :
    ‖fcoeff2 f k m‖ ≤ M * Real.exp (-ρ * modeSize (k, m)) := by
  set y₁ : ℝ := if 0 ≤ k then -ρ else ρ
  set y₂ : ℝ := if 0 ≤ m then -ρ else ρ
  have h₁ : |y₁| = ρ := abs_sgnShift k hρ
  have h₂ : |y₂| = ρ := abs_sgnShift m hρ
  unfold fcoeff2
  rw [iterated_integral_shift hper1 hper2 hd (h₁.trans_lt hρρ) (h₂.trans_lt hρρ) k m]
  set E := Real.exp (-ρ * modeSize (k, m))
  have hpt : ∀ θ ψ : ℝ, ‖f (θ + y₁ * I) (ψ + y₂ * I) * ex k (θ + y₁ * I) * ex m (ψ + y₂ * I)‖
      ≤ M * E := by
    intro θ ψ
    rw [norm_mul, norm_mul, norm_ex, norm_ex]
    have hf := hb (θ + y₁ * I) (ψ + y₂ * I) (by simp [h₁]) (by simp [h₂])
    have hE : Real.exp (k * y₁) * Real.exp (m * y₂) = E := by
      rw [← Real.exp_add, mul_sgnShift, mul_sgnShift]; simp only [E, modeSize]; ring_nf
    rw [mul_assoc, hE]
    exact mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 0 (by simp [hρ]) (by simp [hρ]))
  have hin : ∀ θ : ℝ, ‖∫ ψ in (0 : ℝ)..(2 * Real.pi),
      f (θ + y₁ * I) (ψ + y₂ * I) * ex k (θ + y₁ * I) * ex m (ψ + y₂ * I)‖ ≤
        M * E * |2 * Real.pi - 0| := fun θ =>
    intervalIntegral.norm_integral_le_of_norm_le_const fun ψ _ => hpt θ ψ
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    fun θ (_ : θ ∈ Ι 0 (2 * Real.pi)) => hin θ
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpi := Real.pi_pos
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at hout
  calc (4 * Real.pi ^ 2)⁻¹ * ‖_‖ ≤ (4 * Real.pi ^ 2)⁻¹ * (M * E * (2 * Real.pi) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hout (by positivity)
    _ = M * E := by field_simp; ring

end TwoD

/-! ## Geometric sums over `ℤ` -/

/-- `∑_{k ∈ ℤ} q^{|k|} = (1 + q)/(1 - q)`. -/
def geoZ (q : ℝ) : ℝ := (1 + q) / (1 - q)

/-- `∑_{|k| > K} q^{|k|} = 2 q^{K+1}/(1 - q)`. -/
def tailZ (q : ℝ) (K : ℕ) : ℝ := 2 * q ^ (K + 1) / (1 - q)

/-- The two-sided geometric series. -/
theorem hasSum_geoZ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℤ => q ^ k.natAbs) (geoZ q) := by
  have h1 : HasSum (fun n : ℕ => q ^ ((n : ℤ).natAbs)) (1 - q)⁻¹ :=
    (hasSum_geometric_of_lt_one hq0 hq1).congr_fun fun n => by rw [Int.natAbs_natCast]
  have h2 : HasSum (fun n : ℕ => q ^ ((-((n : ℤ) + 1)).natAbs)) (q * (1 - q)⁻¹) := by
    refine ((hasSum_geometric_of_lt_one hq0 hq1).mul_left q).congr_fun fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this, pow_succ, mul_comm]
  have h := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => q ^ k.natAbs) h1 h2
  have e : (1 - q)⁻¹ + q * (1 - q)⁻¹ = geoZ q := by
    unfold geoZ; rw [div_eq_mul_inv]; ring
  rwa [e] at h

/-- The one-sided tail `∑_{n > K} q^n = q^{K+1}/(1 - q)`. -/
theorem hasSum_tail_nat {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    HasSum (fun n : ℕ => if K < n then q ^ n else 0) (q ^ (K + 1) / (1 - q)) := by
  rw [← hasSum_nat_add_iff' (K + 1)]
  have hz : ∑ i ∈ Finset.range (K + 1), (if K < i then q ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi; exact ite_eq_right_iff.2 fun h => absurd h (by omega)
  rw [hz, sub_zero, div_eq_mul_inv]
  refine ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (q ^ (K + 1))).congr_fun fun n => ?_
  split_ifs with h
  · rw [pow_add, mul_comm]
  · omega

/-- The two-sided tail. -/
theorem hasSum_tailZ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    HasSum (fun k : ℤ => if K < k.natAbs then q ^ k.natAbs else 0) (tailZ q K) := by
  have h1 : HasSum (fun n : ℕ => if K < ((n : ℤ).natAbs) then q ^ ((n : ℤ).natAbs) else 0)
      (q ^ (K + 1) / (1 - q)) :=
    (hasSum_tail_nat hq0 hq1 K).congr_fun fun n => by rw [Int.natAbs_natCast]
  have h2 : HasSum (fun n : ℕ => if K < ((-((n : ℤ) + 1)).natAbs) then
      q ^ ((-((n : ℤ) + 1)).natAbs) else 0) (q ^ (K + 1) / (1 - q)) := by
    have h := hasSum_tail_nat hq0 hq1 K
    rw [← hasSum_nat_add_iff' 1] at h
    have hz : ∑ i ∈ Finset.range 1, (if K < i then q ^ i else 0) = 0 := by simp
    rw [hz, sub_zero] at h
    refine h.congr_fun fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this]
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => if K < k.natAbs then q ^ k.natAbs else 0) h1 h2
  have e : q ^ (K + 1) / (1 - q) + q ^ (K + 1) / (1 - q) = tailZ q K := by
    unfold tailZ; ring
  rwa [e] at h

/-- `e^{-a(|k|+|m|)} = (e^{-a})^{|k|} (e^{-a})^{|m|}`. -/
theorem exp_neg_modeSize (a : ℝ) (p : ℤ × ℤ) :
    Real.exp (-a * modeSize p) = Real.exp (-a) ^ p.1.natAbs * Real.exp (-a) ^ p.2.natAbs := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold modeSize
  have h1 : ((p.1.natAbs : ℕ) : ℝ) = |(p.1 : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : ((p.2.natAbs : ℕ) : ℝ) = |(p.2 : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h1, h2]; ring

/-- The product geometric series over `ℤ²`. -/
theorem hasSum_geoZ2 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun p : ℤ × ℤ => q ^ p.1.natAbs * q ^ p.2.natAbs) (geoZ q ^ 2) := by
  have h := hasSum_geoZ hq0 hq1
  rw [sq]
  refine h.mul h ?_
  exact summable_mul_of_summable_norm (f := fun k : ℤ => q ^ k.natAbs)
    (g := fun k : ℤ => q ^ k.natAbs) (by simpa [abs_of_nonneg, hq0, pow_nonneg] using h.summable)
    (by simpa [abs_of_nonneg, hq0, pow_nonneg] using h.summable)

/-! ## From analyticity to weighted norms -/

/-- **Coefficient decay** for an exponentially decaying coefficient family: if
`|c_p| ≤ M e^{-ρ(|k|+|m|)}` and `r < ρ`, then `c ∈ ℓ¹_r` and
`‖c‖_r ≤ M ((1 + q)/(1 - q))²` with `q = e^{-(ρ - r)}`. -/
theorem wnorm_le_of_decay {c : ℤ × ℤ → ℂ} {M ρ r : ℝ} (hr : r < ρ)
    (hc : ∀ p, ‖c p‖ ≤ M * Real.exp (-ρ * modeSize p)) :
    InWeighted r c ∧ wnorm r c ≤ M * geoZ (Real.exp (-(ρ - r))) ^ 2 := by
  set q := Real.exp (-(ρ - r))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hG := (hasSum_geoZ2 hq0 hq1).mul_left M
  have hb : ∀ p, ‖c p‖ * weight r p ≤ M * (q ^ p.1.natAbs * q ^ p.2.natAbs) := fun p => by
    have := mul_le_mul_of_nonneg_right (hc p) (weight_pos r p).le
    refine this.trans (le_of_eq ?_)
    rw [← exp_neg_modeSize, weight, mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hs : InWeighted r c :=
    hG.summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (weight_pos r p).le) hb
  exact ⟨hs, (hs.tsum_le_tsum hb hG.summable).trans hG.tsum_eq.le⟩

/-- **Paley–Wiener for the strip algebra.** If `x ∈ 𝔸` has `F_x = f` on the real torus, where `f`
is biperiodic, holomorphic on `|Im| < ρ'` and bounded by `M` on `|Im| ≤ ρ` (`0 ≤ ρ < ρ'`), then
`|x_{k,m}| ≤ M e^{-ρ(|k|+|m|)}`. -/
theorem norm_coeff_le_of_holo {f : ℂ → ℂ → ℂ} {ρ' ρ M : ℝ} (x : FA)
    (hx : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = f θ ψ)
    (hper1 : ∀ θ ψ, f (θ + 2 * Real.pi) ψ = f θ ψ) (hper2 : ∀ θ ψ, f θ (ψ + 2 * Real.pi) = f θ ψ)
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    (hρ : 0 ≤ ρ) (hρρ : ρ < ρ') (hb : ∀ θ ψ : ℂ, |θ.im| ≤ ρ → |ψ.im| ≤ ρ → ‖f θ ψ‖ ≤ M)
    (n : ℤ × ℤ) : ‖WEll1Z2.coeff x n‖ ≤ M * Real.exp (-ρ * modeSize n) := by
  obtain ⟨k, m⟩ := n
  have : WEll1Z2.coeff x (k, m) = fcoeff2 f k m := by
    rw [coeff_eq_integral]; unfold fcoeff2
    simp_rw [hx, ← ex_ofReal]
  rw [this]
  exact norm_fcoeff2_le hper1 hper2 hd hρ hρρ hb k m

/-- **Weighted-norm bound from analyticity** (`Bd` form): under the hypotheses of
`norm_coeff_le_of_holo`, for `r < ρ`, `‖x‖_r ≤ M ((1 + q)/(1 - q))²`, `q = e^{-(ρ - r)}`. -/
theorem Bd_of_holo {f : ℂ → ℂ → ℂ} {ρ' ρ r M : ℝ} (x : FA)
    (hx : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = f θ ψ)
    (hper1 : ∀ θ ψ, f (θ + 2 * Real.pi) ψ = f θ ψ) (hper2 : ∀ θ ψ, f θ (ψ + 2 * Real.pi) = f θ ψ)
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    (hρ : 0 ≤ ρ) (hρρ : ρ < ρ') (hb : ∀ θ ψ : ℂ, |θ.im| ≤ ρ → |ψ.im| ≤ ρ → ‖f θ ψ‖ ≤ M)
    (hr : r < ρ) : Bd r x (M * geoZ (Real.exp (-(ρ - r))) ^ 2) :=
  wnorm_le_of_decay hr (norm_coeff_le_of_holo x hx hper1 hper2 hd hρ hρρ hb)

/-! ## Sampling and aliasing -/

/-- `∑_{j<N} e^{i l (2πj/N)} = N` if `N ∣ l`, and `0` otherwise (`N > 0`). -/
theorem sum_roots_of_unity {N : ℕ} (hN : 0 < N) (l : ℤ) :
    ∑ j ∈ Finset.range N, Complex.exp (((l * (2 * Real.pi * j / N) : ℝ) : ℂ) * I) =
      if (N : ℤ) ∣ l then (N : ℂ) else 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * I * l / N)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterm : ∀ j : ℕ, Complex.exp (((l * (2 * Real.pi * j / N) : ℝ) : ℂ) * I) = ζ ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; field_simp
  simp_rw [hterm]
  split_ifs with hd
  · obtain ⟨a, ha⟩ := hd
    have : ζ = 1 := by
      have e : 2 * Real.pi * I * l / N = (a : ℂ) * (2 * Real.pi * I) := by
        rw [ha]; push_cast; field_simp
      simp only [ζ, e, Complex.exp_int_mul_two_pi_mul_I]
    simp [this]
  · have hζ : ζ ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
      apply hd
      refine ⟨n, ?_⟩
      have : (l : ℂ) = N * n := by
        field_simp at hn
        linear_combination hn
      exact_mod_cast this
    have hζN : ζ ^ N = 1 := by
      rw [← Complex.exp_nat_mul]
      have e : (N : ℂ) * (2 * Real.pi * I * l / N) = (l : ℂ) * (2 * Real.pi * I) := by
        field_simp
      rw [e, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hζ, hζN, sub_self, zero_div]

/-- The `j`-th of `N` equally spaced sample points `2πj/N`. -/
def samplePt (N j : ℕ) : ℝ := 2 * Real.pi * j / N

/-- The **discrete Fourier transform** of the `N₁ × N₂` samples of `F` at frequency `n`:
`(N₁N₂)⁻¹ ∑_{j₁,j₂} F(2πj₁/N₁, 2πj₂/N₂) e^{-i(k θ_{j₁} + m ψ_{j₂})}`. -/
def dft2 (F : ℝ → ℝ → ℂ) (N₁ N₂ : ℕ) (n : ℤ × ℤ) : ℂ :=
  ((N₁ : ℂ) * N₂)⁻¹ * ∑ j₁ ∈ Finset.range N₁, ∑ j₂ ∈ Finset.range N₂,
    F (samplePt N₁ j₁) (samplePt N₂ j₂) * fourierMode (-n) (samplePt N₁ j₁) (samplePt N₂ j₂)

/-- The congruence indicator `[p ≡ n mod (N₁, N₂)]`. -/
def congInd (N₁ N₂ : ℕ) (n p : ℤ × ℤ) : ℝ :=
  if (N₁ : ℤ) ∣ p.1 - n.1 ∧ (N₂ : ℤ) ∣ p.2 - n.2 then 1 else 0

/-- The discrete orthogonality relation on the sample grid. -/
theorem sum_mode_samples {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) (l : ℤ × ℤ) :
    ((N₁ : ℂ) * N₂)⁻¹ * ∑ j₁ ∈ Finset.range N₁, ∑ j₂ ∈ Finset.range N₂,
      fourierMode l (samplePt N₁ j₁) (samplePt N₂ j₂) =
    if (N₁ : ℤ) ∣ l.1 ∧ (N₂ : ℤ) ∣ l.2 then 1 else 0 := by
  have hsplit : ∀ j₁ j₂ : ℕ, fourierMode l (samplePt N₁ j₁) (samplePt N₂ j₂) =
      Complex.exp (((l.1 * (2 * Real.pi * j₁ / N₁) : ℝ) : ℂ) * I) *
        Complex.exp (((l.2 * (2 * Real.pi * j₂ / N₂) : ℝ) : ℂ) * I) := by
    intro j₁ j₂
    unfold fourierMode samplePt
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hsplit, ← Finset.sum_mul_sum, sum_roots_of_unity h₁, sum_roots_of_unity h₂]
  have hN₁ : (N₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hN₂ : (N₂ : ℂ) ≠ 0 := by exact_mod_cast h₂.ne'
  by_cases a : (N₁ : ℤ) ∣ l.1
  · by_cases b : (N₂ : ℤ) ∣ l.2
    · simp only [a, b, and_self, ite_true]; field_simp
    · simp [a, b]
  · simp [a]

/-- **Aliasing identity.** The DFT of the samples of `F_x` is the sum of the aliased
coefficients: `dft_n = ∑_{p ≡ n} x_p`. -/
theorem dft2_eval (x : FA) {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) (n : ℤ × ℤ) :
    dft2 (WEll1Z2.eval x) N₁ N₂ n = ∑' p, coeff x p * (congInd N₁ N₂ n p : ℂ) := by
  have hs := summable_norm_coeff le_rfl x
  have hsum : ∀ θ ψ : ℝ, Summable fun p => coeff x p * fourierMode p θ ψ := fun θ ψ =>
    Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hs)
  unfold dft2 WEll1Z2.eval fourierSum
  have e1 : ∀ j₁ j₂ : ℕ, (∑' p, coeff x p * fourierMode p (samplePt N₁ j₁) (samplePt N₂ j₂)) *
      fourierMode (-n) (samplePt N₁ j₁) (samplePt N₂ j₂) =
      ∑' p, coeff x p * fourierMode (p + -n) (samplePt N₁ j₁) (samplePt N₂ j₂) := by
    intro j₁ j₂
    rw [← tsum_mul_right]
    refine tsum_congr fun p => ?_
    rw [fourierMode_add]; ring
  simp_rw [e1]
  have hs2 : ∀ j₁ j₂ : ℕ, Summable fun p =>
      coeff x p * fourierMode (p + -n) (samplePt N₁ j₁) (samplePt N₂ j₂) := fun j₁ j₂ =>
    Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hs)
  rw [Finset.sum_congr rfl fun j₁ _ => (Summable.tsum_finsetSum fun j₂ _ => hs2 j₁ j₂).symm,
    ← Summable.tsum_finsetSum fun j₁ _ => summable_sum fun j₂ _ => hs2 j₁ j₂, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp_rw [← Finset.mul_sum]
  rw [mul_left_comm, sum_mode_samples h₁ h₂]
  unfold congInd
  simp only [← sub_eq_add_neg, Prod.fst_sub, Prod.snd_sub]
  split_ifs <;> simp

/-- The DFT of a single Fourier mode: `1` exactly on the aliases of its frequency. -/
theorem dft2_mode (km : ℤ × ℤ) {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) (n : ℤ × ℤ) :
    dft2 (fourierMode km) N₁ N₂ n =
      if (N₁ : ℤ) ∣ km.1 - n.1 ∧ (N₂ : ℤ) ∣ km.2 - n.2 then 1 else 0 := by
  unfold dft2
  simp_rw [← fourierMode_add]
  rw [sum_mode_samples h₁ h₂]
  simp [sub_eq_add_neg]

/-- **Rejected fixture: aliasing is real.** The mode `e^{iNθ}` has zero `(0,0)` coefficient, but
its DFT on `N × 1` samples at frequency `(0,0)` is `1`; so the DFT alone does not bound the
coefficients without the aliasing tail. -/
theorem dft2_alias_fixture {N : ℕ} (hN : 0 < N) :
    dft2 (fourierMode ((N : ℤ), 0)) N 1 (0, 0) = 1 ∧ coeff (mode 0 ((N : ℤ), 0)) (0, 0) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [dft2_mode _ hN one_pos]; simp
  · simp only [coeff_mode, Pi.single_apply]
    rw [ite_eq_right_iff]
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega

/-- The frequency box `|k| ≤ K₁`, `|m| ≤ K₂`. -/
def box (K₁ K₂ : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(K₁ : ℤ)) K₁ ×ˢ Finset.Icc (-(K₂ : ℤ)) K₂

/-- Membership in the box. -/
theorem mem_box {K₁ K₂ : ℕ} {n : ℤ × ℤ} : n ∈ box K₁ K₂ ↔ |n.1| ≤ K₁ ∧ |n.2| ≤ K₂ := by
  simp [box, Finset.mem_product, Finset.mem_Icc, abs_le]

/-- An alias of a frequency `|a| ≤ K` modulo `N > 2K` is at least as large. -/
theorem abs_le_abs_of_dvd {N K : ℕ} {a b : ℤ} (hNK : 2 * K < N) (ha : |a| ≤ K)
    (hd : (N : ℤ) ∣ b - a) : |a| ≤ |b| := by
  by_cases h : |b - a| < N
  · have := Int.eq_zero_of_abs_lt_dvd hd h
    have hb : b = a := by omega
    rw [hb]
  · rw [not_lt] at h
    have := abs_sub b a
    omega

/-- Two frequencies of the box congruent modulo `N > 2K` are equal. -/
theorem eq_of_dvd_of_abs {N K : ℕ} {a a' b : ℤ} (hNK : 2 * K < N) (ha : |a| ≤ K)
    (ha' : |a'| ≤ K) (hd : (N : ℤ) ∣ b - a) (hd' : (N : ℤ) ∣ b - a') : a = a' := by
  have h := dvd_sub hd hd'
  rw [show b - a - (b - a') = a' - a by ring] at h
  have := Int.eq_zero_of_abs_lt_dvd h (by have := abs_sub a' a; omega)
  omega

/-- Aliases of box frequencies have larger weight. -/
theorem weight_le_of_cong {r : ℝ} (hr : 0 ≤ r) {K₁ K₂ N₁ N₂ : ℕ} (h₁ : 2 * K₁ < N₁)
    (h₂ : 2 * K₂ < N₂) {n p : ℤ × ℤ} (hn : n ∈ box K₁ K₂)
    (hc : (N₁ : ℤ) ∣ p.1 - n.1 ∧ (N₂ : ℤ) ∣ p.2 - n.2) : weight r n ≤ weight r p := by
  rw [mem_box] at hn
  have e1 := abs_le_abs_of_dvd h₁ hn.1 hc.1
  have e2 := abs_le_abs_of_dvd h₂ hn.2 hc.2
  unfold weight modeSize
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hr)
  have c1 : |(n.1 : ℝ)| ≤ |(p.1 : ℝ)| := by rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast e1
  have c2 : |(n.2 : ℝ)| ≤ |(p.2 : ℝ)| := by rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast e2
  linarith

/-- At most one box frequency is congruent to a given `p`. -/
theorem sum_congInd_le_one {K₁ K₂ N₁ N₂ : ℕ} (h₁ : 2 * K₁ < N₁) (h₂ : 2 * K₂ < N₂)
    (p : ℤ × ℤ) : ∑ n ∈ box K₁ K₂, congInd N₁ N₂ n p ≤ 1 := by
  by_cases hex : ∃ n₀ ∈ box K₁ K₂, (N₁ : ℤ) ∣ p.1 - n₀.1 ∧ (N₂ : ℤ) ∣ p.2 - n₀.2
  · obtain ⟨n₀, hn₀, hc₀⟩ := hex
    have : ∀ n ∈ box K₁ K₂, congInd N₁ N₂ n p = if n₀ = n then 1 else 0 := by
      intro n hn
      unfold congInd
      by_cases hc : (N₁ : ℤ) ∣ p.1 - n.1 ∧ (N₂ : ℤ) ∣ p.2 - n.2
      · have hb := mem_box.1 hn; have hb₀ := mem_box.1 hn₀
        have e : n₀ = n := Prod.ext (eq_of_dvd_of_abs h₁ hb₀.1 hb.1 hc₀.1 hc.1)
          (eq_of_dvd_of_abs h₂ hb₀.2 hb.2 hc₀.2 hc.2)
        simp [hc, e]
      · have e : n₀ ≠ n := fun e => hc (e ▸ hc₀)
        simp [hc, e]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [hn₀]
  · simp only [not_exists, not_and] at hex
    rw [Finset.sum_eq_zero fun n hn => by
      unfold congInd; rw [ite_eq_right_iff]; intro hc; exact absurd hc.2 (hex n hn hc.1)]
    norm_num

/-- The weighted `ℓ¹_r` mass of the coefficient `p` outside the box (zero inside). -/
def outMass (K₁ K₂ : ℕ) (r : ℝ) (c : ℤ × ℤ → ℂ) (p : ℤ × ℤ) : ℝ :=
  if p ∈ box K₁ K₂ then 0 else ‖c p‖ * weight r p

/-- `outMass` is nonnegative. -/
theorem outMass_nonneg (K₁ K₂ : ℕ) (r : ℝ) (c : ℤ × ℤ → ℂ) (p : ℤ × ℤ) :
    0 ≤ outMass K₁ K₂ r c p := by
  unfold outMass; split_ifs
  · exact le_rfl
  · exact mul_nonneg (norm_nonneg _) (weight_pos r p).le

/-- `outMass` is dominated by the full weighted mass. -/
theorem outMass_le (K₁ K₂ : ℕ) (r : ℝ) (c : ℤ × ℤ → ℂ) (p : ℤ × ℤ) :
    outMass K₁ K₂ r c p ≤ ‖c p‖ * weight r p := by
  unfold outMass; split_ifs
  · exact mul_nonneg (norm_nonneg _) (weight_pos r p).le
  · exact le_rfl

/-- **Weighted norm from samples.** For `x ∈ ℓ¹_r` (`r ≥ 0`) and grids with `N_i > 2K_i`:
`‖x‖_r ≤ ∑_{n ∈ box} |dft_n| e^{r|n|} + 2 ∑_{p ∉ box} |x_p| e^{r|p|}`.
(Each box coefficient differs from its DFT value by its aliases, which lie outside the box, have
larger weight, and are counted at most once.) -/
theorem wnorm_le_dft (x : FA) {r : ℝ} (hr : 0 ≤ r) (hx : InWeighted r (coeff x))
    {K₁ K₂ N₁ N₂ : ℕ} (h₁ : 2 * K₁ < N₁) (h₂ : 2 * K₂ < N₂) :
    wnorm r (coeff x) ≤ ∑ n ∈ box K₁ K₂, ‖dft2 (WEll1Z2.eval x) N₁ N₂ n‖ * weight r n +
      2 * ∑' p, outMass K₁ K₂ r (coeff x) p := by
  set c := coeff x
  set B := box K₁ K₂
  have hN₁ : 0 < N₁ := by omega
  have hN₂ : 0 < N₂ := by omega
  have hout : Summable (outMass K₁ K₂ r c) :=
    hx.of_nonneg_of_le (outMass_nonneg K₁ K₂ r c) (outMass_le K₁ K₂ r c)
  set T := ∑' p, outMass K₁ K₂ r c p
  -- split the norm into box and outside
  have hsplit : wnorm r c = ∑ n ∈ B, ‖c n‖ * weight r n + T := by
    have e : ∀ p, ‖c p‖ * weight r p =
        (if p ∈ B then ‖c p‖ * weight r p else 0) + outMass K₁ K₂ r c p := by
      intro p; unfold outMass; split_ifs <;> simp
    have hfin : Summable fun p => if p ∈ B then ‖c p‖ * weight r p else 0 :=
      summable_of_ne_finset_zero (s := B) fun p hp => by simp [hp]
    unfold wnorm
    rw [tsum_congr e, Summable.tsum_add hfin hout, tsum_eq_sum (s := B) fun p hp => (by simp [hp])]
    congr 1
    exact Finset.sum_congr rfl fun p hp => by simp [hp]
  -- each box coefficient against its DFT value
  have key : ∀ n ∈ B, ‖c n‖ * weight r n ≤ ‖dft2 (WEll1Z2.eval x) N₁ N₂ n‖ * weight r n +
      ∑' p, outMass K₁ K₂ r c p * congInd N₁ N₂ n p := by
    intro n hn
    have hd := dft2_eval x hN₁ hN₂ n
    set S2 : ℤ × ℤ → ℂ := fun p => if p ∈ B then 0 else c p * (congInd N₁ N₂ n p : ℂ)
    have hci : ∀ p, congInd N₁ N₂ n p = 0 ∨ congInd N₁ N₂ n p = 1 := fun p => by
      unfold congInd; split_ifs <;> simp
    have hdec : ∀ p, c p * (congInd N₁ N₂ n p : ℂ) = (if p = n then c n else 0) + S2 p := by
      intro p
      by_cases hpn : p = n
      · subst hpn
        have h1 : congInd N₁ N₂ p p = 1 := by simp [congInd]
        simp [S2, h1, hn]
      · by_cases hpB : p ∈ B
        · have h0 : congInd N₁ N₂ n p = 0 := by
            unfold congInd
            rw [ite_eq_right_iff]
            intro hc
            exfalso; apply hpn
            have hb := mem_box.1 hn; have hp := mem_box.1 hpB
            exact (Prod.ext (eq_of_dvd_of_abs h₁ hb.1 hp.1 hc.1 (by simp))
              (eq_of_dvd_of_abs h₂ hb.2 hp.2 hc.2 (by simp))).symm
          simp [S2, hpn, hpB, h0]
        · simp [S2, hpn, hpB]
    have hS2n : Summable fun p => ‖S2 p‖ := by
      refine (summable_norm_coeff le_rfl x).of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
      simp only [S2]; split_ifs
      · simp
      · rw [norm_mul, Complex.norm_real]
        rcases hci p with h | h <;> simp [h, c]
    have hS1 : Summable fun p : ℤ × ℤ => if p = n then c n else 0 :=
      summable_of_ne_finset_zero (s := {n}) fun p hp => by simp_all
    rw [tsum_congr hdec, Summable.tsum_add hS1 hS2n.of_norm, tsum_ite_eq] at hd
    have hcn : ‖c n‖ ≤ ‖dft2 (WEll1Z2.eval x) N₁ N₂ n‖ + ∑' p, ‖S2 p‖ := by
      have : c n = dft2 (WEll1Z2.eval x) N₁ N₂ n - ∑' p, S2 p := by rw [hd]; ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_tsum_le_tsum_norm hS2n))
    have hterm : ∀ p, weight r n * ‖S2 p‖ ≤ outMass K₁ K₂ r c p * congInd N₁ N₂ n p := by
      intro p
      simp only [S2, outMass]
      split_ifs with hpB
      · simp
      · rw [norm_mul, Complex.norm_real]
        rcases hci p with h | h
        · simp [h]
        · rw [h]
          have hc : (N₁ : ℤ) ∣ p.1 - n.1 ∧ (N₂ : ℤ) ∣ p.2 - n.2 := by
            by_contra hc; simp [congInd, hc] at h
          have hw := weight_le_of_cong hr h₁ h₂ hn hc
          simp only [norm_one, mul_one]
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    have hRs : Summable fun p => outMass K₁ K₂ r c p * congInd N₁ N₂ n p :=
      hout.of_nonneg_of_le (fun p => mul_nonneg (outMass_nonneg _ _ _ _ _)
          (by rcases hci p with h | h <;> simp [h]))
        fun p => by rcases hci p with h | h <;> simp [h, outMass_nonneg]
    calc ‖c n‖ * weight r n ≤ (‖dft2 (WEll1Z2.eval x) N₁ N₂ n‖ + ∑' p, ‖S2 p‖) * weight r n :=
          mul_le_mul_of_nonneg_right hcn (weight_pos r n).le
      _ = ‖dft2 (WEll1Z2.eval x) N₁ N₂ n‖ * weight r n + ∑' p, weight r n * ‖S2 p‖ := by
          rw [add_mul, tsum_mul_left, mul_comm (∑' p, ‖S2 p‖)]
      _ ≤ _ := add_le_add le_rfl ((hS2n.mul_left _).tsum_le_tsum hterm hRs)
  -- the aliases are counted at most once
  have hswap : ∑ n ∈ B, ∑' p, outMass K₁ K₂ r c p * congInd N₁ N₂ n p ≤ T := by
    have hs : ∀ n ∈ B, Summable fun p => outMass K₁ K₂ r c p * congInd N₁ N₂ n p :=
      fun n _ => hout.of_nonneg_of_le
        (fun p => mul_nonneg (outMass_nonneg _ _ _ _ _) (by unfold congInd; split_ifs <;> simp))
        fun p => mul_le_of_le_one_right (outMass_nonneg _ _ _ _ _)
          (by unfold congInd; split_ifs <;> simp)
    rw [← Summable.tsum_finsetSum hs]
    refine Summable.tsum_le_tsum (fun p => ?_) (summable_sum hs) hout
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right (outMass_nonneg _ _ _ _ _) (sum_congInd_le_one h₁ h₂ p)
  rw [hsplit]
  have := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib] at this
  linarith

/-- **Closed-form tail.** If `|c_p| ≤ M e^{-ρ(|k|+|m|)}` and `r < ρ`, the weighted mass outside the
box is at most `M · geoZ q · (tailZ q K₁ + tailZ q K₂)`, `q = e^{-(ρ - r)}`. -/
theorem tsum_outMass_le {c : ℤ × ℤ → ℂ} {M ρ r : ℝ} (hr : r < ρ)
    (hc : ∀ p, ‖c p‖ ≤ M * Real.exp (-ρ * modeSize p)) (K₁ K₂ : ℕ) :
    ∑' p, outMass K₁ K₂ r c p ≤
      M * geoZ (Real.exp (-(ρ - r))) * (tailZ (Real.exp (-(ρ - r))) K₁ +
        tailZ (Real.exp (-(ρ - r))) K₂) := by
  set q := Real.exp (-(ρ - r))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hc 0)
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  set g : ℤ → ℝ := fun k => q ^ k.natAbs
  set t : ℕ → ℤ → ℝ := fun K k => if K < k.natAbs then q ^ k.natAbs else 0
  have hg0 : ∀ k, 0 ≤ g k := fun k => pow_nonneg hq0 _
  have ht0 : ∀ K k, 0 ≤ t K k := fun K k => by simp only [t]; split_ifs <;> simp [hq0]
  have hG := hasSum_geoZ hq0 hq1
  have hT := hasSum_tailZ hq0 hq1
  have hprod : ∀ {u v : ℤ → ℝ} {U V : ℝ}, (∀ k, 0 ≤ u k) → (∀ k, 0 ≤ v k) → HasSum u U →
      HasSum v V → HasSum (fun p : ℤ × ℤ => u p.1 * v p.2) (U * V) := by
    intro u v U V hu hv hU hV
    refine hU.mul hV (summable_mul_of_summable_norm ?_ ?_)
    · simpa [Real.norm_eq_abs, abs_of_nonneg (hu _)] using hU.summable
    · simpa [Real.norm_eq_abs, abs_of_nonneg (hv _)] using hV.summable
  have hR := ((hprod (ht0 K₁) hg0 (hT K₁) hG).add (hprod hg0 (ht0 K₂) hG (hT K₂))).mul_left M
  have hb : ∀ p, outMass K₁ K₂ r c p ≤ M * (t K₁ p.1 * g p.2 + g p.1 * t K₂ p.2) := by
    intro p
    unfold outMass
    split_ifs with hp
    · exact mul_nonneg hM (add_nonneg (mul_nonneg (ht0 _ _) (hg0 _)) (mul_nonneg (hg0 _) (ht0 _ _)))
    · have hw : ‖c p‖ * weight r p ≤ M * (g p.1 * g p.2) := by
        have := mul_le_mul_of_nonneg_right (hc p) (weight_pos r p).le
        refine this.trans (le_of_eq ?_)
        simp only [g]
        rw [← exp_neg_modeSize, weight, mul_assoc, ← Real.exp_add]
        congr 2; ring
      refine hw.trans (mul_le_mul_of_nonneg_left ?_ hM)
      rw [mem_box, not_and_or] at hp
      have c1 : ((p.1.natAbs : ℤ)) = |p.1| := Int.natCast_natAbs p.1
      have c2 : ((p.2.natAbs : ℤ)) = |p.2| := Int.natCast_natAbs p.2
      rcases hp with hp | hp
      · have : K₁ < p.1.natAbs := by omega
        have e : t K₁ p.1 = g p.1 := by simp [t, g, this]
        rw [e]
        nlinarith [mul_nonneg (hg0 p.1) (ht0 K₂ p.2)]
      · have : K₂ < p.2.natAbs := by omega
        have e : t K₂ p.2 = g p.2 := by simp [t, g, this]
        rw [e]
        nlinarith [mul_nonneg (ht0 K₁ p.1) (hg0 p.2)]
  have hout : Summable (outMass K₁ K₂ r c) :=
    hR.summable.of_nonneg_of_le (outMass_nonneg K₁ K₂ r c) hb
  refine (hout.tsum_le_tsum hb hR.summable).trans (le_of_eq ?_)
  rw [hR.tsum_eq]; ring

/-- **Certified weighted norm from samples plus analyticity** (the stage-2 residual
certificate interface). Let `x ∈ 𝔸` agree on the real torus with `f`, biperiodic and holomorphic
on `|Im| < ρ'`, bounded by `M` on `|Im| ≤ ρ`, and let `0 ≤ r < ρ < ρ'`, `N_i > 2K_i`. Then
`‖x‖_r ≤ ∑_{|k|≤K₁,|m|≤K₂} |dft_{k,m}(f)| e^{r(|k|+|m|)} + 2 M geoZ(q) (tailZ q K₁ + tailZ q K₂)`
with `q = e^{-(ρ - r)}`, where `dft` uses only the `N₁ × N₂` real samples of `f`. -/
theorem Bd_of_samples {f : ℂ → ℂ → ℂ} {ρ' ρ r M : ℝ} (x : FA)
    (hx : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = f θ ψ)
    (hper1 : ∀ θ ψ, f (θ + 2 * Real.pi) ψ = f θ ψ) (hper2 : ∀ θ ψ, f θ (ψ + 2 * Real.pi) = f θ ψ)
    (hd : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (stripC ρ' ×ˢ stripC ρ'))
    (hρ : 0 ≤ ρ) (hρρ : ρ < ρ') (hb : ∀ θ ψ : ℂ, |θ.im| ≤ ρ → |ψ.im| ≤ ρ → ‖f θ ψ‖ ≤ M)
    (hr0 : 0 ≤ r) (hr : r < ρ) {K₁ K₂ N₁ N₂ : ℕ} (h₁ : 2 * K₁ < N₁) (h₂ : 2 * K₂ < N₂) :
    Bd r x (∑ n ∈ box K₁ K₂, ‖dft2 (fun θ ψ : ℝ => f θ ψ) N₁ N₂ n‖ * weight r n +
      2 * (M * geoZ (Real.exp (-(ρ - r))) * (tailZ (Real.exp (-(ρ - r))) K₁ +
        tailZ (Real.exp (-(ρ - r))) K₂))) := by
  have hc := norm_coeff_le_of_holo x hx hper1 hper2 hd hρ hρρ hb
  have hin := (wnorm_le_of_decay hr hc).1
  refine ⟨hin, ?_⟩
  have hfx : (fun θ ψ : ℝ => f θ ψ) = WEll1Z2.eval x := by funext θ ψ; rw [hx]
  rw [hfx]
  exact (wnorm_le_dft x hr0 hin h₁ h₂).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (tsum_outMass_le hr hc K₁ K₂) (by norm_num)))

/-! ## Sanity checks -/

/-- `geoZ 0 = 1`: only the zero mode survives. -/
theorem geoZ_zero : geoZ 0 = 1 := by simp [geoZ]

/-- `tailZ 0 K = 0`. -/
theorem tailZ_zero (K : ℕ) : tailZ 0 K = 0 := by simp [tailZ]

/-- The tail is smaller than the full sum. -/
theorem tailZ_le_geoZ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) : tailZ q K ≤ geoZ q := by
  refine hasSum_le (fun k => ?_) (hasSum_tailZ hq0 hq1 K) (hasSum_geoZ hq0 hq1)
  split_ifs
  · exact le_rfl
  · exact pow_nonneg hq0 _

end PlasmaLean.Theory.KAM.PaleyWiener
