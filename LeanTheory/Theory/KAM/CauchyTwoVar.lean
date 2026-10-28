/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.AnalyticComposition
public import LeanTheory.Theory.KAM.StripPaleyWiener
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Two-variable Cauchy formula and analytic fields from holomorphic ones

KAM for non-polynomial (analytic) fields: building the
`AnaFieldAt` interface of `Theory/KAM/AnalyticComposition` from a **holomorphic bounded field**.
Mathlib has the one-variable Cauchy integral formula only; this file iterates it.

**Fourier coefficients on the real torus.** `fc2 g k m` is the double Fourier coefficient with
the characters `em k θ = e^{-ikθ}`; `coeff_eq_fc2` (elements of `𝔸`), `fcoeff2_eq_fc2`,
`norm_fc2_le` (sup bound), `fc2_sub`, `fc2_const_mul`, and **`fc2_fc2_swap`** (Fubini on
`[0, 2π]⁴` for jointly continuous integrands, by four adjacent swaps).

**Uniqueness.** `eq_zero_of_coeff_zero` (one variable, from Mathlib's uniform convergence of
Fourier series on `AddCircle`) and `eq_zero_of_fc2_zero` (continuous biperiodic functions on
`ℝ²` with vanishing double Fourier coefficients vanish).

**Two-variable Cauchy formula.** `cauchyCoeff f R α = R^{-|α|} fc2 (f(Re^{is}, Re^{it})) α₁ α₂`,
i.e. `(2πi)⁻² ∮∮ f ζ^{-α-1}`;
* `norm_cauchyCoeff_le`: `|c_α| ≤ M/R^{|α|}` for `|f| ≤ M` on the torus `|ζ₁| = |ζ₂| = R`;
* **`hasSum_cauchyCoeff`**: `f` jointly holomorphic on the bidisc of radius `R' > R` ⇒
  `f(z₁, z₂) = ∑ c_α z₁^{α₁} z₂^{α₂}` for `|zᵢ| < R`. Proof: the one-variable formula
  (`cauchy1`) in each variable, geometric expansion of the kernel (`hasSum_ckern`) and termwise
  integration (`integral_tsum_bdd`).

**Analytic fields.** `HoloData G ρ' ρ r d d' M`: `G(θ, ψ, z₁, z₂)` jointly holomorphic on
`|Im θ|, |Im ψ| < ρ'`, `|zᵢ| < d'`, biperiodic, `|G| ≤ M` on `|Im| ≤ ρ`, `|zᵢ| ≤ d`
(`0 ≤ r < ρ < ρ'`, `0 < d < d'`). Then:
* `taylorFA G h α ∈ 𝔸` has coefficients `fc2 (c_α(θ, ψ))` with `c_α(θ, ψ)` the Cauchy
  coefficients of `G(θ, ψ, ·, ·)`; their decay `|·| ≤ M d^{-|α|} e^{-ρ|n|}`
  (`HoloData.norm_fc2_coeffFun_le`) is Paley–Wiener (`norm_fcoeff2_le`) applied *inside* the
  Cauchy integral after `fc2_fc2_swap`;
* `eval_taylorFA`: its function is `c_α(θ, ψ)` (uniqueness);
* **`AnaFieldAt.of_holomorphic`**: `AnaFieldAt r (M ((1+q)/(1-q))²) d X`, `q = e^{-(ρ-r)}`,
  for any `X` agreeing with `G` at real `θ, ψ`, `|zᵢ| < d`.
Auxiliary: `continuous_eval`, `eval_add_two_pi_left/right`, `continuous_fc2_param`.

**Sanity.** `fc2_const`, `cauchyCoeff_zero_fun` (degenerate), `cauchyCoeff_const` (special case),
`hasSum_cauchyCoeff_const` (accepted fixture), `not_cauchy_bound_half` (rejected fixture: the
Cauchy estimate fails with a constant below the sup).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM.CauchyTwoVar

open Complex MeasureTheory intervalIntegral Set Metric WEll1Z2
open LeanTheory.Theory.KAM.PaleyWiener LeanTheory.Theory.KAM.AnalyticComposition
open scoped Interval

/-! ## Fourier coefficients of functions on the real torus -/

/-- The character `e^{-ikθ}`. -/
def em (k : ℤ) (θ : ℝ) : ℂ := Complex.exp (((-k * θ : ℝ) : ℂ) * I)

/-- Characters are unimodular. -/
theorem norm_em (k : ℤ) (θ : ℝ) : ‖em k θ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- Characters are continuous. -/
@[fun_prop]
theorem continuous_em (k : ℤ) : Continuous (em k) := by unfold em; fun_prop

/-- The double Fourier coefficient
`(4π²)⁻¹ ∫₀^{2π} ∫₀^{2π} g(θ, ψ) e^{-ikθ} e^{-imψ} dθ dψ` of a function on `ℝ²`. -/
def fc2 (g : ℝ → ℝ → ℂ) (k m : ℤ) : ℂ :=
  ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ ψ * em k θ) * em m ψ

/-- The coefficients of an element of `𝔸` are the double Fourier coefficients of its function. -/
theorem coeff_eq_fc2 (x : FA) (k m : ℤ) : coeff x (k, m) = fc2 (WEll1Z2.eval x) k m :=
  coeff_eq_integral x k m

/-- `fcoeff2` (of `StripPaleyWiener`) is `fc2` of the restriction to real points. -/
theorem fcoeff2_eq_fc2 (f : ℂ → ℂ → ℂ) (k m : ℤ) :
    fcoeff2 f k m = fc2 (fun θ ψ => f θ ψ) k m := by
  simp only [fcoeff2, fc2, ex_ofReal, em]

/-- `4π² ≠ 0`. -/
theorem four_pi_sq_ne_zero : ((4 * Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 := by
  have := Real.pi_pos; exact_mod_cast (by positivity : (4 * Real.pi ^ 2) ≠ 0)

/-- **Sup bound**: `|fc2 g k m| ≤ M` if `|g| ≤ M` everywhere. -/
theorem norm_fc2_le {g : ℝ → ℝ → ℂ} {M : ℝ} (hg : ∀ θ ψ, ‖g θ ψ‖ ≤ M) (k m : ℤ) :
    ‖fc2 g k m‖ ≤ M := by
  have hpi := Real.pi_pos
  have hin : ∀ ψ : ℝ, ‖(∫ θ in (0 : ℝ)..(2 * Real.pi), g θ ψ * em k θ) * em m ψ‖ ≤
      M * |2 * Real.pi - 0| := fun ψ => by
    rw [norm_mul, norm_em, mul_one]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
      rw [norm_mul, norm_em, mul_one]; exact hg θ ψ
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    fun ψ (_ : ψ ∈ Ι 0 (2 * Real.pi)) => hin ψ
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at hout
  unfold fc2
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc (4 * Real.pi ^ 2)⁻¹ * ‖_‖ ≤ (4 * Real.pi ^ 2)⁻¹ * (M * (2 * Real.pi) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hout (by positivity)
    _ = M := by field_simp; ring

/-- `fc2` of a scalar multiple. -/
theorem fc2_const_mul (c : ℂ) (g : ℝ → ℝ → ℂ) (k m : ℤ) :
    fc2 (fun θ ψ => c * g θ ψ) k m = c * fc2 g k m := by
  unfold fc2
  have e : ∀ ψ, (∫ θ in (0 : ℝ)..(2 * Real.pi), c * g θ ψ * em k θ) * em m ψ =
      c * ((∫ θ in (0 : ℝ)..(2 * Real.pi), g θ ψ * em k θ) * em m ψ) := fun ψ => by
    simp_rw [mul_assoc]; rw [intervalIntegral.integral_const_mul, mul_assoc]
  simp_rw [e, intervalIntegral.integral_const_mul]; ring

/-- Continuity of parametric integrals over `[0, 2π]`. -/
theorem continuous_param {X : Type*} [TopologicalSpace X] {f : X → ℝ → ℂ}
    (hf : Continuous fun p : X × ℝ => f p.1 p.2) :
    Continuous fun x => ∫ t in (0 : ℝ)..(2 * Real.pi), f x t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _

/-- `fc2` of a difference of continuous functions. -/
theorem fc2_sub {g h : ℝ → ℝ → ℂ} (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hh : Continuous fun p : ℝ × ℝ => h p.1 p.2) (k m : ℤ) :
    fc2 (fun θ ψ => g θ ψ - h θ ψ) k m = fc2 g k m - fc2 h k m := by
  unfold fc2
  rw [← mul_sub, ← intervalIntegral.integral_sub]
  · congr 1
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    simp only
    rw [← sub_mul, ← intervalIntegral.integral_sub]
    · simp_rw [sub_mul]
    · exact ((hg.comp (by fun_prop : Continuous fun θ : ℝ => (θ, ψ))).mul
        (continuous_em k)).intervalIntegrable _ _
    · exact ((hh.comp (by fun_prop : Continuous fun θ : ℝ => (θ, ψ))).mul
        (continuous_em k)).intervalIntegrable _ _
  · refine (Continuous.mul ?_ (continuous_em m)).intervalIntegrable _ _
    exact continuous_param (f := fun ψ θ => g θ ψ * em k θ)
      ((hg.comp continuous_swap).mul ((continuous_em k).comp continuous_snd))
  · refine (Continuous.mul ?_ (continuous_em m)).intervalIntegrable _ _
    exact continuous_param (f := fun ψ θ => h θ ψ * em k θ)
      ((hh.comp continuous_swap).mul ((continuous_em k).comp continuous_snd))

/-- Fubini on `[0, 2π]²` for a jointly continuous function (wrapper). -/
theorem swap2 {Φ : ℝ → ℝ → ℂ} (hΦ : Continuous fun p : ℝ × ℝ => Φ p.1 p.2) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), ∫ y in (0 : ℝ)..(2 * Real.pi), Φ x y =
      ∫ y in (0 : ℝ)..(2 * Real.pi), ∫ x in (0 : ℝ)..(2 * Real.pi), Φ x y :=
  integral_integral_swap_of_continuous (H := fun y x => Φ x y) (hΦ.comp continuous_swap)
    Real.two_pi_pos.le Real.two_pi_pos.le

/-- `fc2` written as a single iterated integral of the product with both characters. -/
theorem fc2_eq_iter (g : ℝ → ℝ → ℂ) (k m : ℤ) :
    fc2 g k m = ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ ψ * em k θ * em m ψ := by
  unfold fc2
  congr 1
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  exact (intervalIntegral.integral_mul_const _ _).symm

/-- **Fubini for double Fourier coefficients**: for `H` jointly continuous on `ℝ⁴`, the Fourier
coefficients in `(θ, ψ)` and in `(s, t)` commute. -/
theorem fc2_fc2_swap {H : ℝ → ℝ → ℝ → ℝ → ℂ}
    (hH : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => H q.1.1 q.1.2 q.2.1 q.2.2) (a b k m : ℤ) :
    fc2 (fun θ ψ => fc2 (fun s t => H θ ψ s t) a b) k m =
      fc2 (fun s t => fc2 (fun θ ψ => H θ ψ s t) k m) a b := by
  set A : ℝ → ℝ → ℝ → ℝ → ℂ := fun θ ψ s t => H θ ψ s t * em a s * em b t * em k θ * em m ψ
  have hA : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => A q.1.1 q.1.2 q.2.1 q.2.2 :=
    (((hH.mul ((continuous_em a).comp (by fun_prop))).mul ((continuous_em b).comp
      (by fun_prop))).mul ((continuous_em k).comp (by fun_prop))).mul
      ((continuous_em m).comp (by fun_prop))
  have keyL : ∀ θ ψ : ℝ, (((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi),
      ∫ s in (0 : ℝ)..(2 * Real.pi), H θ ψ s t * em a s * em b t) * em k θ * em m ψ =
      ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi),
        ∫ s in (0 : ℝ)..(2 * Real.pi), A θ ψ s t := fun θ ψ => by
    rw [mul_assoc, mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [A]; ring
  have keyR : ∀ s t : ℝ, (((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∫ ψ in (0 : ℝ)..(2 * Real.pi),
      ∫ θ in (0 : ℝ)..(2 * Real.pi), H θ ψ s t * em k θ * em m ψ) * em a s * em b t =
      ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∫ ψ in (0 : ℝ)..(2 * Real.pi),
        ∫ θ in (0 : ℝ)..(2 * Real.pi), A θ ψ s t := fun s t => by
    rw [mul_assoc, mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 1
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [A]; ring
  rw [fc2_eq_iter, fc2_eq_iter]
  simp_rw [fc2_eq_iter, keyL, keyR, intervalIntegral.integral_const_mul]
  congr 2
  -- step 1: swap `θ` and `t` (inner `s`-integral as a function of `(θ, t)`)
  have s1 : ∀ ψ : ℝ, ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ t in (0 : ℝ)..(2 * Real.pi),
      ∫ s in (0 : ℝ)..(2 * Real.pi), A θ ψ s t =
      ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
        ∫ θ in (0 : ℝ)..(2 * Real.pi), A θ ψ s t := fun ψ => by
    rw [swap2 (Φ := fun θ t => ∫ s in (0 : ℝ)..(2 * Real.pi), A θ ψ s t)]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      exact swap2 (Φ := fun θ s => A θ ψ s t)
        (hA.comp (by fun_prop : Continuous fun p : ℝ × ℝ => ((p.1, ψ), (p.2, t))))
    · exact continuous_param (f := fun p : ℝ × ℝ => fun s => A p.1 ψ s p.2)
        (hA.comp (by fun_prop :
          Continuous fun p : (ℝ × ℝ) × ℝ => ((p.1.1, ψ), (p.2, p.1.2))))
  simp_rw [s1]
  -- step 2: swap `ψ` and `t`, then `ψ` and `s`
  rw [swap2 (Φ := fun ψ t => ∫ s in (0 : ℝ)..(2 * Real.pi),
      ∫ θ in (0 : ℝ)..(2 * Real.pi), A θ ψ s t)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    refine swap2 (Φ := fun ψ s => ∫ θ in (0 : ℝ)..(2 * Real.pi), A θ ψ s t) ?_
    exact continuous_param (f := fun p : ℝ × ℝ => fun θ => A θ p.1 p.2 t)
      (hA.comp (by fun_prop :
        Continuous fun p : (ℝ × ℝ) × ℝ => ((p.2, p.1.1), (p.1.2, t))))
  · refine continuous_param (f := fun p : ℝ × ℝ => fun s =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), A θ p.1 s p.2) ?_
    exact continuous_param (f := fun q : (ℝ × ℝ) × ℝ => fun θ => A θ q.1.1 q.2 q.1.2)
      (hA.comp (by fun_prop :
        Continuous fun p : ((ℝ × ℝ) × ℝ) × ℝ => ((p.2, p.1.1.1), (p.1.2, p.1.1.2))))

/-! ## Uniqueness of Fourier coefficients of continuous functions -/

/-- **One-dimensional uniqueness**: a continuous `2π`-periodic function all of whose Fourier
coefficients vanish is zero (Mathlib's uniform convergence of Fourier series on `AddCircle`). -/
theorem eq_zero_of_coeff_zero {g : ℝ → ℂ} (hc : Continuous g) (hp : ∀ x, g (x + 2 * Real.pi) = g x)
    (h : ∀ k : ℤ, ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ * em k θ = 0) (θ : ℝ) : g θ = 0 := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIco (2 * Real.pi) 0 g,
      AddCircle.liftIco_continuous (by rw [zero_add]; simpa using (hp 0).symm) hc.continuousOn⟩
  have hcoef : ∀ n, fourierCoeff F n = 0 := by
    intro n
    change fourierCoeff (AddCircle.liftIco (2 * Real.pi) 0 g) n = 0
    rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
    have e : ∀ x : ℝ, fourier (-n) (x : AddCircle (0 + 2 * Real.pi - 0)) • g x = g x * em n x := by
      intro x
      rw [fourier_coe_apply, smul_eq_mul, mul_comm, em]
      congr 1; congr 1
      have := Real.pi_pos
      field_simp
      push_cast; ring
    simp_rw [e]
    simp [h n]
  have hsum := hasSum_fourier_series_of_summable (f := F)
    (by convert (summable_zero : Summable fun _ : ℤ => (0 : ℂ)) with n; exact hcoef n)
  have hF : F = 0 := hsum.unique (by
    convert (hasSum_zero : HasSum (fun _ : ℤ => (0 : C(AddCircle (2 * Real.pi), ℂ))) 0) with n
    rw [hcoef n, zero_smul])
  have hIco : ∀ x ∈ Ico (0 : ℝ) (2 * Real.pi), g x = 0 := by
    intro x hx
    have h1 : F x = g x := AddCircle.liftIco_coe_apply (by simpa using hx)
    rw [← h1, hF]; rfl
  have hper : Function.Periodic g (2 * Real.pi) := hp
  set n : ℤ := ⌊θ / (2 * Real.pi)⌋
  have hpi := Real.two_pi_pos
  rw [← hper.sub_int_mul_eq n]
  apply hIco
  constructor
  · have := Int.floor_le (θ / (2 * Real.pi))
    rw [le_div_iff₀ hpi] at this
    linarith
  · have := Int.lt_floor_add_one (θ / (2 * Real.pi))
    rw [div_lt_iff₀ hpi] at this
    linarith

/-- **Two-dimensional uniqueness**: a jointly continuous biperiodic function on `ℝ²` all of
whose double Fourier coefficients vanish is zero. -/
theorem eq_zero_of_fc2_zero {g : ℝ → ℝ → ℂ} (hc : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hp1 : ∀ θ ψ, g (θ + 2 * Real.pi) ψ = g θ ψ) (hp2 : ∀ θ ψ, g θ (ψ + 2 * Real.pi) = g θ ψ)
    (h : ∀ k m, fc2 g k m = 0) (θ ψ : ℝ) : g θ ψ = 0 := by
  have hk : ∀ k : ℤ, ∀ ψ, ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ ψ * em k θ = 0 := by
    intro k
    refine eq_zero_of_coeff_zero ?_ ?_ ?_
    · exact continuous_param (f := fun ψ θ => g θ ψ * em k θ)
        ((hc.comp continuous_swap).mul ((continuous_em k).comp continuous_snd))
    · intro ψ; simp only [hp2]
    · intro m
      have := h k m
      rw [fc2, mul_eq_zero] at this
      exact this.resolve_left (inv_ne_zero four_pi_sq_ne_zero)
  exact eq_zero_of_coeff_zero (hc.comp (by fun_prop : Continuous fun θ : ℝ => (θ, ψ)))
    (fun θ => hp1 θ ψ) (fun k => hk k ψ) θ

/-! ## The two-variable Cauchy formula on a bidisc -/

/-- Termwise integration over `[0, 2π]` of an absolutely summable series (countable index) of
continuous functions with a uniform bound. -/
theorem integral_tsum_bdd {ι : Type*} [Countable ι] {g : ι → ℂ} (hg : Summable fun n => ‖g n‖)
    {φ : ι → ℝ → ℂ} (hφc : ∀ n, Continuous (φ n)) {C : ℝ} (hφb : ∀ n t, ‖φ n t‖ ≤ C) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n, g n * φ n t =
      ∑' n, g n * ∫ t in (0 : ℝ)..(2 * Real.pi), φ n t := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * Real.pi) (F := fun n t => g n * φ n t)
    (f := fun t => ∑' n, g n * φ n t) (fun n _ => ‖g n‖ * C)
    (fun n => ((continuous_const.mul (hφc n)).aestronglyMeasurable))
    (fun n => ae_of_all _ fun t _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hφb n t) (norm_nonneg _))
    (ae_of_all _ fun t _ => hg.mul_right C)
    intervalIntegrable_const
    (ae_of_all _ fun t _ => (Summable.of_norm_bounded (hg.mul_right C) fun n => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hφb n t) (norm_nonneg _)).hasSum)
  rw [← h.tsum_eq]
  refine tsum_congr fun n => ?_
  exact intervalIntegral.integral_const_mul _ _

/-- The **Cauchy kernel** `ζ/(ζ - w)` on the circle `ζ = R e^{is}`. -/
def ckern (R : ℝ) (w : ℂ) (s : ℝ) : ℂ := circleMap 0 R s / (circleMap 0 R s - w)

/-- **One-variable Cauchy formula** in parametrised form:
`g(w) = (2π)⁻¹ ∫₀^{2π} ζ/(ζ - w) g(ζ) ds`, `ζ = R e^{is}`, for `|w| < R`. -/
theorem cauchy1 {g : ℂ → ℂ} {R : ℝ} (hd : DifferentiableOn ℂ g (closedBall 0 R)) {w : ℂ}
    (hw : ‖w‖ < R) :
    g w = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ s in (0 : ℝ)..(2 * Real.pi), ckern R w s * g (circleMap 0 R s) := by
  have h := hd.circleIntegral_sub_inv_smul (mem_ball_zero_iff.2 hw)
  unfold circleIntegral at h
  simp only [deriv_circleMap, smul_eq_mul] at h
  have e : ∀ s : ℝ, circleMap 0 R s * I * ((circleMap 0 R s - w)⁻¹ * g (circleMap 0 R s)) =
      I * (ckern R w s * g (circleMap 0 R s)) := fun s => by
    unfold ckern; ring
  simp_rw [e, intervalIntegral.integral_const_mul] at h
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have h' : ∫ s in (0 : ℝ)..(2 * Real.pi), ckern R w s * g (circleMap 0 R s) =
      ((2 * Real.pi : ℝ) : ℂ) * g w := by
    have := congrArg (fun z => I⁻¹ * z) h
    rw [← mul_assoc, inv_mul_cancel₀ hI, one_mul] at this
    rw [this]; push_cast; field_simp
  rw [h', ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

/-- The **geometric expansion** of the Cauchy kernel:
`ζ/(ζ - w) = ∑ₙ (w/R)ⁿ e^{-ins}` for `|w| < R`. -/
theorem hasSum_ckern {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ < R) (s : ℝ) :
    HasSum (fun n : ℕ => (w / R) ^ n * em n s) (ckern R w s) := by
  set ξ : ℂ := w / R * Complex.exp (-(s * I))
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hξ : ‖ξ‖ < 1 := by
    simp only [ξ, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
    rw [show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, div_lt_one hR]
    exact hw
  have e1 : (fun n : ℕ => (w / R) ^ n * em n s) = fun n : ℕ => ξ ^ n := by
    funext n
    simp only [ξ, mul_pow, em]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have e2 : ckern R w s = (1 - ξ)⁻¹ := by
    have hE : Complex.exp (s * I) ≠ 0 := Complex.exp_ne_zero _
    have hζ : circleMap 0 R s = R * Complex.exp (s * I) := circleMap_zero R s
    have hne : (R : ℂ) * Complex.exp (s * I) - w ≠ 0 := by
      intro h0
      have : ‖(R : ℂ) * Complex.exp (s * I)‖ = ‖w‖ := by rw [sub_eq_zero.1 h0]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le,
        Complex.norm_exp_ofReal_mul_I, mul_one] at this
      linarith
    unfold ckern
    rw [hζ]
    simp only [ξ, Complex.exp_neg]
    field_simp
  rw [e1, e2]
  exact hasSum_geometric_of_norm_lt_one hξ

/-- The **Cauchy coefficients** of a function of two complex variables on the torus
`|ζ₁| = |ζ₂| = R`: `c_α = R^{-|α|} fc2 (f(R e^{is}, R e^{it})) α₁ α₂`, i.e.
`c_α = (2πi)⁻² ∮∮ f(ζ₁, ζ₂) ζ₁^{-α₁-1} ζ₂^{-α₂-1} dζ₁ dζ₂`. -/
def cauchyCoeff (f : ℂ → ℂ → ℂ) (R : ℝ) (α : ℕ × ℕ) : ℂ :=
  ((R ^ (α.1 + α.2) : ℝ) : ℂ)⁻¹ *
    fc2 (fun s t => f (circleMap 0 R s) (circleMap 0 R t)) α.1 α.2

/-- **Cauchy estimate** on the bidisc: `|c_α| ≤ M/R^{|α|}` if `|f| ≤ M` on the torus
`|ζ₁| = |ζ₂| = R`. -/
theorem norm_cauchyCoeff_le {f : ℂ → ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ s t : ℝ, ‖f (circleMap 0 R s) (circleMap 0 R t)‖ ≤ M) (α : ℕ × ℕ) :
    ‖cauchyCoeff f R α‖ ≤ M / R ^ (α.1 + α.2) := by
  unfold cauchyCoeff
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv,
    mul_comm M]
  exact mul_le_mul_of_nonneg_left (norm_fc2_le hM _ _) (by positivity)


/-- Summability of `‖w/R‖ⁿ` for `|w| < R`. -/
theorem summable_norm_geom {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ < R) :
    Summable fun n : ℕ => ‖(w / R) ^ n‖ := by
  simp only [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
  exact summable_geometric_of_lt_one (by positivity) ((div_lt_one hR).2 hw)

/-- **Two-variable Cauchy formula (power-series form).** If `f` is holomorphic on the bidisc
`|z₁|, |z₂| < R'` and bounded by `M` on the torus `|ζ₁| = |ζ₂| = R < R'`, then for
`|z₁|, |z₂| < R` the double power series with the Cauchy coefficients converges to `f`:
`f(z₁, z₂) = ∑_α c_α z₁^{α₁} z₂^{α₂}`. -/
theorem hasSum_cauchyCoeff {f : ℂ → ℂ → ℂ} {R R' M : ℝ} (hR : 0 < R) (hRR : R < R')
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (ball 0 R' ×ˢ ball 0 R'))
    (hM : ∀ s t : ℝ, ‖f (circleMap 0 R s) (circleMap 0 R t)‖ ≤ M)
    {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ < R) (h₂ : ‖z₂‖ < R) :
    HasSum (fun α : ℕ × ℕ => cauchyCoeff f R α * z₁ ^ α.1 * z₂ ^ α.2) (f z₁ z₂) := by
  have hζ : ∀ s, circleMap 0 R s ∈ ball (0 : ℂ) R' := fun s => by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hR]; exact hRR
  have hcb : closedBall (0 : ℂ) R ⊆ ball 0 R' := closedBall_subset_ball hRR
  have hd1 : ∀ w ∈ ball (0 : ℂ) R', DifferentiableOn ℂ (fun z => f z w) (closedBall 0 R) :=
    fun w hw => hf.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => (z, w)) _)
      (fun z hz => ⟨hcb hz, hw⟩)
  have hd2 : ∀ w ∈ ball (0 : ℂ) R', DifferentiableOn ℂ (fun z => f w z) (closedBall 0 R) :=
    fun w hw => hf.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => (w, z)) _)
      (fun z hz => ⟨hw, hcb hz⟩)
  have hz₁ : z₁ ∈ ball (0 : ℂ) R' := mem_ball_zero_iff.2 (h₁.trans hRR)
  have hFc : Continuous fun p : ℝ × ℝ => f (circleMap 0 R p.1) (circleMap 0 R p.2) :=
    hf.continuousOn.comp_continuous
      (((continuous_circleMap 0 R).comp continuous_fst).prodMk
        ((continuous_circleMap 0 R).comp continuous_snd)) (fun p => ⟨hζ _, hζ _⟩)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  have hpi := Real.pi_pos
  have hq₁ := summable_norm_geom hR h₁
  have hq₂ := summable_norm_geom hR h₂
  -- the inner coefficients `I₁ a t = ∫ F(s, t) e^{-ias} ds`
  have hI₁c : ∀ a : ℕ, Continuous fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
      f (circleMap 0 R s) (circleMap 0 R t) * em a s := fun a =>
    continuous_param (f := fun t s => f (circleMap 0 R s) (circleMap 0 R t) * em a s)
      ((hFc.comp continuous_swap).mul ((continuous_em a).comp continuous_snd))
  have hI₁b : ∀ (a : ℕ) (t : ℝ), ‖∫ s in (0 : ℝ)..(2 * Real.pi),
      f (circleMap 0 R s) (circleMap 0 R t) * em a s‖ ≤ M * (2 * Real.pi) := fun a t => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
      (C := M) (f := fun s => f (circleMap 0 R s) (circleMap 0 R t) * em a s)
      fun s _ => by rw [norm_mul, norm_em, mul_one]; exact hM s t
    rwa [sub_zero, abs_of_pos Real.two_pi_pos] at this
  -- step 1: iterated one-variable Cauchy formulas
  have step1 : f z₁ z₂ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi),
      ckern R z₂ t * (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ s in (0 : ℝ)..(2 * Real.pi),
        ckern R z₁ s * f (circleMap 0 R s) (circleMap 0 R t)) := by
    rw [cauchy1 (hd2 z₁ hz₁) h₂]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← cauchy1 (hd1 _ (hζ t)) h₁]
  -- step 2: expand the inner kernel
  have step2 : ∀ t, ∫ s in (0 : ℝ)..(2 * Real.pi),
      ckern R z₁ s * f (circleMap 0 R s) (circleMap 0 R t) =
      ∑' a : ℕ, (z₁ / R) ^ a * ∫ s in (0 : ℝ)..(2 * Real.pi),
        f (circleMap 0 R s) (circleMap 0 R t) * em a s := by
    intro t
    have e : ∀ s, ckern R z₁ s * f (circleMap 0 R s) (circleMap 0 R t) =
        ∑' a : ℕ, (z₁ / R) ^ a * (f (circleMap 0 R s) (circleMap 0 R t) * em a s) := by
      intro s
      rw [← (hasSum_ckern hR h₁ s).tsum_eq, ← tsum_mul_right]
      exact tsum_congr fun a => by ring
    simp_rw [e]
    exact integral_tsum_bdd hq₁
      (fun a => (hFc.comp (by fun_prop : Continuous fun s : ℝ => (s, t))).mul (continuous_em a))
      (C := M) (fun a s => by rw [norm_mul, norm_em, mul_one]; exact hM s t)
  -- step 3: multiply by the outer kernel
  have hprod : Summable fun α : ℕ × ℕ => ‖(z₁ / R) ^ α.1 * (z₂ / R) ^ α.2‖ := by
    simp_rw [norm_mul]
    exact hq₁.mul_of_nonneg hq₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have step3 : ∀ t, ckern R z₂ t * ∑' a : ℕ, (z₁ / R) ^ a * ∫ s in (0 : ℝ)..(2 * Real.pi),
      f (circleMap 0 R s) (circleMap 0 R t) * em a s =
      ∑' α : ℕ × ℕ, ((z₁ / R) ^ α.1 * (z₂ / R) ^ α.2) *
        ((∫ s in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 R s) (circleMap 0 R t) * em α.1 s) *
          em α.2 t) := by
    intro t
    have hA : Summable fun a : ℕ => ‖(z₁ / R) ^ a * ∫ s in (0 : ℝ)..(2 * Real.pi),
        f (circleMap 0 R s) (circleMap 0 R t) * em a s‖ :=
      (hq₁.mul_right (M * (2 * Real.pi))).of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun a => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hI₁b a t) (norm_nonneg _))
    have hB : Summable fun b : ℕ => ‖(z₂ / R) ^ b * em b t‖ := by
      simpa only [norm_mul, norm_em, mul_one] using hq₂
    rw [← (hasSum_ckern hR h₂ t).tsum_eq, mul_comm, tsum_mul_tsum_of_summable_norm hA hB]
    exact tsum_congr fun α => by ring
  -- step 4: integrate termwise in `t`
  have step4 : ∫ t in (0 : ℝ)..(2 * Real.pi), ∑' α : ℕ × ℕ,
      ((z₁ / R) ^ α.1 * (z₂ / R) ^ α.2) *
        ((∫ s in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 R s) (circleMap 0 R t) * em α.1 s) *
          em α.2 t) =
      ∑' α : ℕ × ℕ, ((z₁ / R) ^ α.1 * (z₂ / R) ^ α.2) *
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          (∫ s in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 R s) (circleMap 0 R t) * em α.1 s) *
            em α.2 t :=
    integral_tsum_bdd hprod (fun α => (hI₁c α.1).mul (continuous_em α.2))
      (C := M * (2 * Real.pi)) (fun α t => by rw [norm_mul, norm_em, mul_one]; exact hI₁b _ _)
  have hval : f z₁ z₂ = ∑' α : ℕ × ℕ, cauchyCoeff f R α * z₁ ^ α.1 * z₂ ^ α.2 := by
    rw [step1]
    simp_rw [step2]
    have e5 : ∀ t, ckern R z₂ t * (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∑' a : ℕ, (z₁ / R) ^ a *
        ∫ s in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 R s) (circleMap 0 R t) * em a s) =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∑' α : ℕ × ℕ, ((z₁ / R) ^ α.1 * (z₂ / R) ^ α.2) *
          ((∫ s in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 R s) (circleMap 0 R t) * em α.1 s) *
            em α.2 t) := fun t => by
      rw [mul_left_comm, step3]
    simp_rw [e5, intervalIntegral.integral_const_mul, step4]
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun α => ?_
    unfold cauchyCoeff fc2
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    rw [div_pow, div_pow, pow_add]
    field_simp
    ring
  have hsum : Summable fun α : ℕ × ℕ => cauchyCoeff f R α * z₁ ^ α.1 * z₂ ^ α.2 := by
    refine (hprod.mul_left M).of_norm_bounded fun α => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow, norm_div, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hR.le, div_pow, div_pow]
    have hc := norm_cauchyCoeff_le hR hM α
    have : M / R ^ (α.1 + α.2) * ‖z₁‖ ^ α.1 * ‖z₂‖ ^ α.2 =
        M * (‖z₁‖ ^ α.1 / R ^ α.1 * (‖z₂‖ ^ α.2 / R ^ α.2)) := by
      rw [pow_add]; field_simp
    rw [← this]
    gcongr
  exact hval ▸ hsum.hasSum

/-! ## Analytic fields along the torus from holomorphic fields -/

/-- Continuity of `fc2` in a parameter. -/
theorem continuous_fc2_param {X : Type*} [TopologicalSpace X] {H : X → ℝ → ℝ → ℂ}
    (hH : Continuous fun q : X × ℝ × ℝ => H q.1 q.2.1 q.2.2) (k m : ℤ) :
    Continuous fun x => fc2 (H x) k m := by
  unfold fc2
  refine continuous_const.mul (continuous_param (f := fun x ψ =>
    (∫ θ in (0 : ℝ)..(2 * Real.pi), H x θ ψ * em k θ) * em m ψ) ?_)
  refine Continuous.mul ?_ ((continuous_em m).comp continuous_snd)
  exact continuous_param (f := fun q : X × ℝ => fun θ => H q.1 θ q.2 * em k θ)
    ((hH.comp (by fun_prop : Continuous fun p : (X × ℝ) × ℝ => (p.1.1, p.2, p.1.2))).mul
      ((continuous_em k).comp continuous_snd))

/-- The function of an element of `𝔸` is jointly continuous on the real torus. -/
theorem continuous_eval (x : FA) : Continuous fun p : ℝ × ℝ => WEll1Z2.eval x p.1 p.2 := by
  unfold WEll1Z2.eval fourierSum
  refine continuous_tsum (fun n => continuous_const.mul ?_) (summable_norm_coeff le_rfl x)
    (fun n p => by rw [norm_mul, norm_fourierMode, mul_one])
  unfold fourierMode; fun_prop

/-- The function of an element of `𝔸` is `2π`-periodic in `θ`. -/
theorem eval_add_two_pi_left (x : FA) (θ ψ : ℝ) :
    WEll1Z2.eval x (θ + 2 * Real.pi) ψ = WEll1Z2.eval x θ ψ := by
  unfold WEll1Z2.eval fourierSum
  refine tsum_congr fun n => ?_
  congr 1
  unfold fourierMode
  rw [show ((n.1 * (θ + 2 * Real.pi) + n.2 * ψ : ℝ) : ℂ) * I =
      ((n.1 * θ + n.2 * ψ : ℝ) : ℂ) * I + (n.1 : ℂ) * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The function of an element of `𝔸` is `2π`-periodic in `ψ`. -/
theorem eval_add_two_pi_right (x : FA) (θ ψ : ℝ) :
    WEll1Z2.eval x θ (ψ + 2 * Real.pi) = WEll1Z2.eval x θ ψ := by
  unfold WEll1Z2.eval fourierSum
  refine tsum_congr fun n => ?_
  congr 1
  unfold fourierMode
  rw [show ((n.1 * θ + n.2 * (ψ + 2 * Real.pi) : ℝ) : ℂ) * I =
      ((n.1 * θ + n.2 * ψ : ℝ) : ℂ) * I + (n.2 : ℂ) * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

section OfHolomorphic

variable {G : ℂ → ℂ → ℂ → ℂ → ℂ} {ρ' ρ r d d' M : ℝ}

/-- Hypotheses for `AnaFieldAt.of_holomorphic`: `G(θ, ψ, z₁, z₂)` is jointly holomorphic on the
product of the strips `|Im θ|, |Im ψ| < ρ'` with the bidisc `|z₁|, |z₂| < d'`, `2π`-periodic in
`θ` and `ψ`, and bounded by `M` on `|Im θ|, |Im ψ| ≤ ρ`, `|z₁|, |z₂| ≤ d`, with
`0 ≤ r < ρ < ρ'` and `0 < d < d'`. -/
structure HoloData (G : ℂ → ℂ → ℂ → ℂ → ℂ) (ρ' ρ r d d' M : ℝ) : Prop where
  /-- Joint holomorphy on the strip–bidisc product. -/
  holo : DifferentiableOn ℂ (fun p : (ℂ × ℂ) × (ℂ × ℂ) => G p.1.1 p.1.2 p.2.1 p.2.2)
    ((stripC ρ' ×ˢ stripC ρ') ×ˢ (ball 0 d' ×ˢ ball 0 d'))
  /-- `2π`-periodicity in `θ`. -/
  per1 : ∀ θ ψ z₁ z₂, G (θ + 2 * Real.pi) ψ z₁ z₂ = G θ ψ z₁ z₂
  /-- `2π`-periodicity in `ψ`. -/
  per2 : ∀ θ ψ z₁ z₂, G θ (ψ + 2 * Real.pi) z₁ z₂ = G θ ψ z₁ z₂
  /-- The sup bound on the closed strip times the closed bidisc. -/
  bound : ∀ θ ψ z₁ z₂ : ℂ, |θ.im| ≤ ρ → |ψ.im| ≤ ρ → ‖z₁‖ ≤ d → ‖z₂‖ ≤ d → ‖G θ ψ z₁ z₂‖ ≤ M
  /-- `0 ≤ r`. -/
  r_nonneg : 0 ≤ r
  /-- `r < ρ`. -/
  r_lt : r < ρ
  /-- `ρ < ρ'`. -/
  ρ_lt : ρ < ρ'
  /-- `0 < d`. -/
  d_pos : 0 < d
  /-- `d < d'`. -/
  d_lt : d < d'

namespace HoloData

variable (h : HoloData G ρ' ρ r d d' M)
include h

/-- `0 ≤ ρ`. -/
theorem ρ_nonneg : 0 ≤ ρ := h.r_nonneg.trans h.r_lt.le

/-- Real points lie in the open strip. -/
theorem real_mem (θ : ℝ) : (θ : ℂ) ∈ stripC ρ' := by
  simp only [stripC, mem_ofPred_eq, ofReal_im, abs_zero]
  exact h.ρ_nonneg.trans_lt h.ρ_lt

/-- Points of the circle `|ζ| = d` lie in the open disc of radius `d'`. -/
theorem circle_mem (s : ℝ) : circleMap 0 d s ∈ ball (0 : ℂ) d' := by
  rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos h.d_pos]; exact h.d_lt

/-- Points of the circle have norm `d`. -/
theorem norm_circle (s : ℝ) : ‖circleMap 0 d s‖ ≤ d := by
  rw [norm_circleMap_zero, abs_of_pos h.d_pos]

/-- Joint continuity of `(θ, ψ, s, t) ↦ G(θ, ψ, d e^{is}, d e^{it})` on `ℝ⁴`. -/
theorem continuous_H :
    Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G q.1.1 q.1.2 (circleMap 0 d q.2.1) (circleMap 0 d q.2.2) := by
  refine h.holo.continuousOn.comp_continuous (f := fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
    ((((q.1.1 : ℝ) : ℂ), ((q.1.2 : ℝ) : ℂ)), (circleMap 0 d q.2.1, circleMap 0 d q.2.2)))
    (by fun_prop) fun q => ?_
  exact ⟨⟨h.real_mem _, h.real_mem _⟩, ⟨h.circle_mem _, h.circle_mem _⟩⟩

/-- Holomorphy of `(z₁, z₂) ↦ G(θ, ψ, z₁, z₂)` at real `θ, ψ`. -/
theorem holo_z (θ ψ : ℝ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => G θ ψ p.1 p.2) (ball 0 d' ×ˢ ball 0 d') :=
  h.holo.comp (by fun_prop : DifferentiableOn ℂ (fun p : ℂ × ℂ => (((θ : ℂ), (ψ : ℂ)), p)) _)
    fun p hp => ⟨⟨h.real_mem θ, h.real_mem ψ⟩, hp⟩

/-- Holomorphy of `(θ, ψ) ↦ G(θ, ψ, z₁, z₂)` for `|z₁|, |z₂| < d'`. -/
theorem holo_θψ {z₁ z₂ : ℂ} (h₁ : z₁ ∈ ball (0 : ℂ) d') (h₂ : z₂ ∈ ball (0 : ℂ) d') :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => G p.1 p.2 z₁ z₂) (stripC ρ' ×ˢ stripC ρ') :=
  h.holo.comp (by fun_prop : DifferentiableOn ℂ (fun p : ℂ × ℂ => (p, (z₁, z₂))) _)
    fun p hp => ⟨hp, ⟨h₁, h₂⟩⟩

/-- The Taylor coefficient functions `c_α(θ, ψ)` (real `θ, ψ`) are jointly continuous. -/
theorem continuous_coeffFun (α : ℕ × ℕ) :
    Continuous fun p : ℝ × ℝ => cauchyCoeff (G p.1 p.2) d α := by
  unfold cauchyCoeff
  exact continuous_const.mul (continuous_fc2_param (X := ℝ × ℝ)
    (H := fun p s t => G p.1 p.2 (circleMap 0 d s) (circleMap 0 d t))
    (h.continuous_H.comp (by fun_prop)) _ _)

/-- **Exponential decay of the Fourier coefficients of the Taylor coefficients** (Fubini plus
Paley–Wiener): `|(c_α)_{k,m}| ≤ M d^{-|α|} e^{-ρ(|k|+|m|)}`. -/
theorem norm_fc2_coeffFun_le (α : ℕ × ℕ) (n : ℤ × ℤ) :
    ‖fc2 (fun θ ψ : ℝ => cauchyCoeff (G θ ψ) d α) n.1 n.2‖ ≤
      M / d ^ (α.1 + α.2) * Real.exp (-ρ * modeSize n) := by
  obtain ⟨k, m⟩ := n
  unfold cauchyCoeff
  rw [fc2_const_mul, fc2_fc2_swap (H := fun θ ψ s t => G θ ψ (circleMap 0 d s)
    (circleMap 0 d t)) h.continuous_H]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (pow_pos h.d_pos _).le,
    div_eq_inv_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left (norm_fc2_le (fun s t => ?_) _ _) (by
    have := h.d_pos; positivity)
  rw [← fcoeff2_eq_fc2 (fun θ ψ => G θ ψ (circleMap 0 d s) (circleMap 0 d t))]
  exact norm_fcoeff2_le (fun θ ψ => h.per1 θ ψ _ _) (fun θ ψ => h.per2 θ ψ _ _)
    (h.holo_θψ (h.circle_mem s) (h.circle_mem t)) h.ρ_nonneg h.ρ_lt
    (fun θ ψ hθ hψ => h.bound θ ψ _ _ hθ hψ (h.norm_circle s) (h.norm_circle t)) k m

/-- The coefficient family lies in `ℓ¹_r` with the Paley–Wiener bound. -/
theorem decay (α : ℕ × ℕ) :
    InWeighted r (fun n : ℤ × ℤ => fc2 (fun θ ψ : ℝ => cauchyCoeff (G θ ψ) d α) n.1 n.2) ∧
      wnorm r (fun n : ℤ × ℤ => fc2 (fun θ ψ : ℝ => cauchyCoeff (G θ ψ) d α) n.1 n.2) ≤
        M / d ^ (α.1 + α.2) * geoZ (Real.exp (-(ρ - r))) ^ 2 :=
  wnorm_le_of_decay h.r_lt (h.norm_fc2_coeffFun_le α)

end HoloData

/-- The Taylor coefficient `c_α ∈ 𝔸` along the torus: the element of `𝔸` with Fourier
coefficients `fc2 (c_α(θ, ψ))`, `c_α(θ, ψ)` the Cauchy coefficient of `G(θ, ψ, ·, ·)` on the
bidisc of radius `d`. -/
def taylorFA (G : ℂ → ℂ → ℂ → ℂ → ℂ) (h : HoloData G ρ' ρ r d d' M) (α : ℕ × ℕ) : FA :=
  ofCoeff (fun n : ℤ × ℤ => fc2 (fun θ ψ : ℝ => cauchyCoeff (G θ ψ) d α) n.1 n.2)
    ((h.decay α).1.mono h.r_nonneg)

/-- The coefficients of `taylorFA`. -/
theorem coeff_taylorFA (h : HoloData G ρ' ρ r d d' M) (α : ℕ × ℕ) :
    coeff (taylorFA G h α) = fun n : ℤ × ℤ =>
      fc2 (fun θ ψ : ℝ => cauchyCoeff (G θ ψ) d α) n.1 n.2 :=
  funext fun n => coeff_ofCoeff _ _ n

/-- **The function of `taylorFA` is the Taylor coefficient function** (uniqueness of Fourier
coefficients of continuous functions). -/
theorem eval_taylorFA (h : HoloData G ρ' ρ r d d' M) (α : ℕ × ℕ) (θ ψ : ℝ) :
    WEll1Z2.eval (taylorFA G h α) θ ψ = cauchyCoeff (G θ ψ) d α := by
  have hc1 := continuous_eval (taylorFA G h α)
  have hc2 := h.continuous_coeffFun α
  have hper : ∀ (θ ψ : ℝ), cauchyCoeff (G ↑(θ + 2 * Real.pi) ψ) d α = cauchyCoeff (G θ ψ) d α ∧
      cauchyCoeff (G θ ↑(ψ + 2 * Real.pi)) d α = cauchyCoeff (G θ ψ) d α := fun θ ψ => by
    push_cast
    constructor
    · congr 1; funext z₁ z₂; exact h.per1 _ _ _ _
    · congr 1; funext z₁ z₂; exact h.per2 _ _ _ _
  have := eq_zero_of_fc2_zero (g := fun θ ψ : ℝ =>
      WEll1Z2.eval (taylorFA G h α) θ ψ - cauchyCoeff (G θ ψ) d α) (hc1.sub hc2)
    (fun θ ψ => by rw [eval_add_two_pi_left, (hper θ ψ).1])
    (fun θ ψ => by rw [eval_add_two_pi_right, (hper θ ψ).2])
    (fun k m => by
      rw [fc2_sub hc1 hc2, ← coeff_eq_fc2, coeff_taylorFA, sub_self]) θ ψ
  exact sub_eq_zero.1 this

/-- **`AnaFieldAt` from a holomorphic field** (closes stage-1 gap 1). Let `G(θ, ψ, z₁, z₂)` be
jointly holomorphic on `|Im θ|, |Im ψ| < ρ'`, `|z₁|, |z₂| < d'`, biperiodic, and bounded by `M`
on `|Im θ|, |Im ψ| ≤ ρ`, `|zᵢ| ≤ d` (`HoloData`), and let `X` agree with `G` at real `θ, ψ` and
`|zᵢ| < d`. Then `X` is an analytic field along the torus with strip `r` and Cauchy majorants
`C/d^{|α|}`, `C = M ((1+q)/(1-q))²`, `q = e^{-(ρ-r)}`: the Taylor coefficients are the
two-variable Cauchy coefficients (`hasSum_cauchyCoeff`), and their strip norms come from the
Paley–Wiener bound (`norm_fcoeff2_le`) after exchanging the Cauchy and Fourier integrals
(`fc2_fc2_swap`). -/
def _root_.LeanTheory.Theory.KAM.AnalyticComposition.AnaFieldAt.of_holomorphic
    {X : ℝ → ℝ → ℂ → ℂ → ℂ} (h : HoloData G ρ' ρ r d d' M)
    (hX : ∀ (θ ψ : ℝ) (z₁ z₂ : ℂ), ‖z₁‖ < d → ‖z₂‖ < d → X θ ψ z₁ z₂ = G θ ψ z₁ z₂) :
    AnaFieldAt r (M * geoZ (Real.exp (-(ρ - r))) ^ 2) d X where
  c := taylorFA G h
  bound α := by
    refine ⟨?_, ?_⟩
    · rw [coeff_taylorFA]; exact (h.decay α).1
    · rw [coeff_taylorFA]
      refine (h.decay α).2.trans (le_of_eq ?_)
      ring
  hasSum_eval θ ψ z₁ z₂ h₁ h₂ := by
    rw [hX θ ψ z₁ z₂ h₁ h₂]
    simp_rw [eval_taylorFA]
    exact hasSum_cauchyCoeff h.d_pos h.d_lt (h.holo_z θ ψ)
      (fun s t => h.bound _ _ _ _ (by simp [h.ρ_nonneg]) (by simp [h.ρ_nonneg])
        (h.norm_circle s) (h.norm_circle t)) h₁ h₂

end OfHolomorphic

/-! ## Sanity checks -/

/-- `fc2` of a constant at the zero mode is the constant. -/
theorem fc2_const (c : ℂ) : fc2 (fun _ _ => c) 0 0 = c := by
  have hpi := Real.pi_pos
  simp only [fc2, em, Int.cast_zero, neg_zero, zero_mul, ofReal_zero, Complex.exp_zero,
    mul_one, intervalIntegral.integral_const, sub_zero]
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp
  ring

/-- Degenerate case: the zero function has zero Cauchy coefficients. -/
theorem cauchyCoeff_zero_fun (R : ℝ) (α : ℕ × ℕ) : cauchyCoeff (fun _ _ => 0) R α = 0 := by
  simp [cauchyCoeff, fc2]

/-- Special case: the constant term of a constant function is the constant. -/
theorem cauchyCoeff_const (c : ℂ) (R : ℝ) : cauchyCoeff (fun _ _ => c) R (0, 0) = c := by
  simp only [cauchyCoeff, add_zero, pow_zero, ofReal_one, inv_one, one_mul]
  exact_mod_cast fc2_const c

/-- Accepted fixture: the Cauchy expansion of a constant on the unit bidisc (from
`hasSum_cauchyCoeff`) sums to the constant. -/
theorem hasSum_cauchyCoeff_const (c z₁ z₂ : ℂ) (h₁ : ‖z₁‖ < 1) (h₂ : ‖z₂‖ < 1) :
    HasSum (fun α : ℕ × ℕ => cauchyCoeff (fun _ _ => c) 1 α * z₁ ^ α.1 * z₂ ^ α.2) c :=
  hasSum_cauchyCoeff (R' := 2) (M := ‖c‖) one_pos one_lt_two
    (differentiableOn_const c) (fun _ _ => le_rfl) h₁ h₂

/-- Rejected fixture: the Cauchy estimate fails with a constant below the sup of `f` (the
constant `1` has `c₀₀ = 1 > 1/2`), so the bound `M` in `norm_cauchyCoeff_le` cannot be dropped. -/
theorem not_cauchy_bound_half :
    ¬ ∀ α : ℕ × ℕ, ‖cauchyCoeff (fun _ _ => (1 : ℂ)) 1 α‖ ≤ 1 / 2 / 1 ^ (α.1 + α.2) := by
  intro h
  have := h (0, 0)
  rw [cauchyCoeff_const] at this
  norm_num at this

end LeanTheory.Theory.KAM.CauchyTwoVar
