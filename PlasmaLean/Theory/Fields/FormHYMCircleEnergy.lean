/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMEnergy
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Yang–Mills minimality of the anti-self-dual lift on `Ω × S¹`

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, paragraph
"A positive auxiliary energy and its exact scope" (lines 49–59): on `M = Ω × S¹`, "If `a₁` is a
real one-form whose tangential trace on `∂M` vanishes, then `d*ℱ = 0` and integration by parts
give `∫_M |ℱ + da₁|² - ∫_M |ℱ|² = ∫_M |da₁|² ≥ 0`. Thus the lift minimizes the Abelian
Yang–Mills energy against these fixed-boundary connection variations." Assessment claim S-13.

`Theory/Fields/FormHYMEnergy` proved this identity on the cover `Ω × ℝ` for variations with
compact support in `Ω × ℝ`. This file proves the circle version: the variation is periodic in
the circle variable and the integrals are over one period.

## Conventions

* `ℓ > 0` is the length of the circle. A 1-form on `ℝ³ × S¹` is a field `a : ℝ³ × ℝ → LiftForm 1`
  that is `ℓ`-periodic in `τ`: `a (x, τ + ℓ) = a (x, τ)`. Its curvature `da = extDeriv a` is
  then `ℓ`-periodic (`extDeriv_tau_periodic`).
* The integral over `ℝ³ × S¹` is the integral over the fundamental domain
  `ℝ³ × (0, ℓ]`, the set `Set.univ ×ˢ Set.Ioc 0 ℓ` of `ℝ³ × ℝ`, for Lebesgue measure. The
  covering map `liftCover ℓ` restricted to this set is a measure-preserving bijection onto
  `ℝ³ × (ℝ/ℓℤ)` with the product of Lebesgue measure and the Haar measure of mass `ℓ`
  (`integral_circle_eq_integral_slab`, `setIntegral_circle_eq_setIntegral_slab`), so these are
  the integrals over `ℝ³ × S¹` of the descended functions; the final section states the results
  on `ℝ³ × AddCircle ℓ` in that form.
* Metric, star, inner product `liftInner` and density `ymDensity` are those of `FormHYMStar`,
  `FormHYMCircle` and `FormHYMEnergy`.

## Hypotheses of the main statements

`Ω ⊆ ℝ³` is open; `G` is a field of 2-forms that is `C¹` and co-closed (`d(⋆G) = 0`) on `Ω × ℝ`
and `ℓ`-periodic in `τ` over `Ω`; `a` is a `C¹` field of 1-forms on `ℝ³ × ℝ`, `ℓ`-periodic in
`τ`, vanishing at `(x, τ)` whenever `x` is outside a compact set `K ⊆ Ω`.

## What is proved

* `integral_slab_liftInner_extDeriv_eq_zero`: the cross term over one period vanishes,
  `∫_{ℝ³ × (0,ℓ]} ⟨G, da⟩ = 0`.
* `integral_slab_energy_perturbation`: `∫_{ℝ³ × (0,ℓ]} (|G + da|² - |G|²) = ∫_{ℝ³ × (0,ℓ]} |da|²`;
  `integral_slab_energy_perturbation_nonneg` (`≥ 0`);
  `integral_slab_energy_perturbation_eq_zero_iff` (`= 0` exactly when `da = 0` everywhere);
  `integral_slab_ymDensity_perturbation` for the density `½|F|²`.
* For the lift `ℱ = hymLift ω` of a vacuum form `ω` on `Ω`:
  `VacuumForm.integral_slab_liftInner_hymLift_extDeriv`,
  `VacuumForm.integral_slab_energy_hymLift_perturbation`, `…_nonneg`, `…_eq_zero_iff`, and
  `VacuumField.integral_slab_ymDensity_hymLift_perturbation` in vector language.
* With finite magnetic energy, `‖B‖²` integrable on `Ω` (`B = flux⁻¹ ω`): the two energies
  separately, `integral_slab_liftInner_hymLift` (`∫_{Ω × (0,ℓ]} |ℱ|² = 2ℓ ∫_Ω |B|²`),
  `VacuumForm.integral_slab_energy_hymLift_add`
  (`∫_{Ω × (0,ℓ]} |ℱ + da|² = 2ℓ ∫_Ω |B|² + ∫_{Ω × (0,ℓ]} |da|²`) and
  `VacuumForm.integral_slab_energy_hymLift_le`
  (`∫_{Ω × (0,ℓ]} |ℱ|² ≤ ∫_{Ω × (0,ℓ]} |ℱ + da|²`): the lift minimises the Abelian Yang–Mills
  energy over `Ω × S¹` against these variations.
* On `ℝ³ × AddCircle ℓ`: `VacuumForm.integral_circle_energy_hymLift_perturbation`,
  `VacuumForm.integral_circle_energy_hymLift_add`, `VacuumForm.integral_circle_energy_hymLift_le`,
  for a field `D` of 2-forms on `ℝ³ × (ℝ/ℓℤ)` with `D (x, [τ]) = da (x, τ)`.

## Proof

The compact-support theorem of `FormHYMEnergy` is applied to `χ(τ) a`, where
`χ(τ) = Φ(τ) - Φ(τ - ℓ)` (`tauCutoff`) and `Φ` is a smooth step from `0` to `1` on `[0, 1]`.
By the Leibniz rule `⟨G, d(χ a)⟩ = χ ⟨G, da⟩ + χ' ⟨G, dτ ∧ a⟩`. For continuous `ℓ`-periodic
`f`, `g` of `τ`, `∫_ℝ (χ f + χ' g) = ∫_{(0,ℓ]} f` (`integral_tauCutoff_periodic`): `χ` differs
from the indicator of `(0, ℓ]` by `u(τ) - u(τ - ℓ)` with `u` bounded of compact support, `χ'`
is `Φ'(τ) - Φ'(τ - ℓ)`, and `∫ (v(τ) - v(τ - ℓ)) h(τ) dτ = 0` for periodic `h` by translation
invariance. Fubini's theorem on `ℝ³ × ℝ` then gives the cross term.

## Integrability

Every integrand of the slab statements is proved integrable on `ℝ³ × (0, ℓ]`
(`integrableOn_slab_liftInner_extDeriv`, `integrableOn_slab_liftInner_extDeriv_self`,
`integrableOn_slab_energy_perturbation`), without any integrability hypothesis on `G`: the
integrands are continuous and vanish for `x` outside the compact `K`. The separate energies need
`‖B‖²` integrable on `Ω`, which is a hypothesis there, and the perturbed energy is proved
integrable. `integral_slab_liftInner_hymLift` alone is stated without that hypothesis; when
`‖B‖²` is not integrable on `Ω` both of its sides are the junk value `0`.

## Relation to the source and what is not formalized

* The source's class is 1-forms on `M = Ω × S¹` with vanishing tangential trace on
  `∂M = ∂Ω × S¹`. The class here is 1-forms on `Ω × S¹` (periodic in `τ`) that vanish outside
  `K × S¹` for a compact `K ⊆ Ω`, extended by zero. These have vanishing trace, and the
  periodicity in the circle variable is now exactly the source's. Variations that are nonzero
  up to `∂Ω` with only the tangential part vanishing there are NOT covered: that needs a
  boundary `∂Ω`, a trace and Stokes' theorem on a manifold with boundary.
* The 1-form on the circle product is represented by its pullback to the cover (a periodic
  field); TauCeti's manifold exterior derivative `mextDeriv` on `ℝ³ × AddCircle ℓ` is not used.
  In the circle statements the curvature of the variation is a field `D` on `ℝ³ × (ℝ/ℓℤ)` with
  `D ∘ liftCover ℓ = da`, given as a hypothesis; that `D` is `mextDeriv` of the descended
  1-form is not proved.
* No bundle, no functional on a space of connections: as in `FormHYMEnergy`.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix Module MeasureTheory TauCeti Set
open scoped RealInnerProductSpace

/-! ## A cutoff in the circle variable -/

/-- **The cutoff** `χ(τ) = Φ(τ) - Φ(τ - ℓ)` with `Φ` Mathlib's smooth step
(`Real.smoothTransition`: `0` for `τ ≤ 0`, `1` for `τ ≥ 1`). For `0 < ℓ` it is smooth, vanishes
outside `[0, ℓ + 1]`, and its translates by multiples of `ℓ` add up to `1`; the last property is
used only in the integrated form `integral_tauCutoff_periodic`. -/
noncomputable def tauCutoff (ℓ τ : ℝ) : ℝ :=
  Real.smoothTransition τ - Real.smoothTransition (τ - ℓ)

/-- The cutoff is of class `C¹`. -/
theorem contDiff_tauCutoff (ℓ : ℝ) : ContDiff ℝ 1 (tauCutoff ℓ) := by
  have h : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  exact h.sub (h.comp (contDiff_id.sub contDiff_const))

/-- The cutoff vanishes outside `[0, ℓ + 1]`. -/
theorem tauCutoff_eq_zero {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : τ ∉ Icc 0 (ℓ + 1)) :
    tauCutoff ℓ τ = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hτ
  rcases hτ with h | h
  · rw [tauCutoff, Real.smoothTransition.zero_of_nonpos h.le,
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]
  · rw [tauCutoff, Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), sub_self]

/-- The derivative of the smooth step vanishes outside `[0, 1]`. -/
theorem deriv_smoothTransition_eq_zero {τ : ℝ} (hτ : τ ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition τ = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hτ
  rcases hτ with h | h
  · have e : Real.smoothTransition =ᶠ[nhds τ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
    rw [e.deriv_eq, deriv_const]
  · have e : Real.smoothTransition =ᶠ[nhds τ] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
    rw [e.deriv_eq, deriv_const]

/-- The derivative of the cutoff: `χ'(τ) = Φ'(τ) - Φ'(τ - ℓ)`. -/
theorem deriv_tauCutoff (ℓ τ : ℝ) :
    deriv (tauCutoff ℓ) τ =
      deriv Real.smoothTransition τ - deriv Real.smoothTransition (τ - ℓ) := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have h1 : DifferentiableAt ℝ Real.smoothTransition τ := hd τ
  have h2 : DifferentiableAt ℝ (fun s => Real.smoothTransition (s - ℓ)) τ := by fun_prop
  have e2 : deriv (fun s => Real.smoothTransition (s - ℓ)) τ =
      deriv Real.smoothTransition (τ - ℓ) := by
    rw [deriv_comp_sub_const]
  exact (h1.hasDerivAt.sub h2.hasDerivAt).deriv.trans (by rw [e2])

/-- **Translation by a period.** For `h` of period `ℓ` and `v h` integrable on the line,
`τ ↦ v(τ - ℓ) h(τ)` is integrable with the same integral (translation invariance of Lebesgue
measure). -/
theorem integral_shift_mul_periodic {ℓ : ℝ} {v h : ℝ → ℝ} (hp : ∀ τ, h (τ + ℓ) = h τ)
    (hint : Integrable fun τ => v τ * h τ) :
    Integrable (fun τ => v (τ - ℓ) * h τ) ∧ ∫ τ, v (τ - ℓ) * h τ = ∫ τ, v τ * h τ := by
  have e : (fun τ => v (τ - ℓ) * h τ) = fun τ => (fun s => v s * h s) (τ - ℓ) := by
    funext τ
    have := hp (τ - ℓ)
    rw [sub_add_cancel] at this
    simp only [this]
  rw [e]
  exact ⟨hint.comp_sub_right ℓ, integral_sub_right_eq_self (μ := volume) (fun s => v s * h s) ℓ⟩

/-- **The cutoff unfolds an integral over the line to an integral over one period.** For
continuous functions `f`, `g` of period `ℓ > 0`,

`∫_ℝ (χ(τ) f(τ) + χ'(τ) g(τ)) dτ = ∫_{(0, ℓ]} f(τ) dτ`.

The left integrand is continuous with compact support, and the right one is continuous on a
bounded interval, so both integrals are integrals of integrable functions. -/
theorem integral_tauCutoff_periodic {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfp : ∀ τ, f (τ + ℓ) = f τ) (hgp : ∀ τ, g (τ + ℓ) = g τ) :
    ∫ τ, (tauCutoff ℓ τ * f τ + deriv (tauCutoff ℓ) τ * g τ) = ∫ τ in Ioc 0 ℓ, f τ := by
  let u : ℝ → ℝ := fun τ => Real.smoothTransition τ - (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) τ
  have hu : Integrable fun τ => u τ * f τ := by
    have hsupp : Function.support (fun τ => u τ * f τ) ⊆ Icc (0 : ℝ) 1 := by
      intro τ hτ
      by_contra hmem
      apply hτ
      have h0 : u τ = 0 := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hmem
        rcases hmem with h | h
        · simp [u, Real.smoothTransition.zero_of_nonpos h.le, not_lt.2 h.le]
        · simp [u, Real.smoothTransition.one_of_one_le h.le, zero_lt_one.trans h]
      simp [h0]
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    have e : (fun τ => u τ * f τ) =
        fun τ => Real.smoothTransition τ * f τ - (Ioi (0 : ℝ)).indicator f τ := by
      funext τ
      by_cases h : 0 < τ <;> simp [u, h, sub_mul]
    rw [e]
    exact ((Real.smoothTransition.continuous.mul hf).integrableOn_Icc).sub
      ((hf.integrableOn_Icc).indicator measurableSet_Ioi)
  have hv : Integrable fun τ => deriv Real.smoothTransition τ * g τ := by
    have hc : Continuous fun τ => deriv Real.smoothTransition τ * g τ :=
      ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by simp)).mul hg
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc
      fun τ hτ => by rw [deriv_smoothTransition_eq_zero hτ, zero_mul])
  obtain ⟨hu', eu⟩ := integral_shift_mul_periodic hfp hu
  obtain ⟨hv', ev⟩ := integral_shift_mul_periodic hgp hv
  have hI : Integrable ((Ioc 0 ℓ).indicator f) :=
    (hf.integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  have e : (fun τ => tauCutoff ℓ τ * f τ + deriv (tauCutoff ℓ) τ * g τ) =
      fun τ => ((Ioc 0 ℓ).indicator f τ + (u τ * f τ - u (τ - ℓ) * f τ)) +
        (deriv Real.smoothTransition τ * g τ - deriv Real.smoothTransition (τ - ℓ) * g τ) := by
    funext τ
    have hind : (Ioc 0 ℓ).indicator (fun _ => (1 : ℝ)) τ =
        (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) τ -
          (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (τ - ℓ) := by
      simp only [Set.indicator, mem_Ioc, mem_Ioi, sub_pos]
      by_cases h0 : 0 < τ
      · by_cases h1 : ℓ < τ
        · simp [h0, h1, not_le.2 h1]
        · simp [h0, h1, not_lt.1 h1]
      · have h1 : ¬ ℓ < τ := fun h => h0 (hℓ.trans h)
        simp [h0, h1]
    have hif : (Ioc 0 ℓ).indicator f τ = (Ioc 0 ℓ).indicator (fun _ => (1 : ℝ)) τ * f τ := by
      by_cases h : τ ∈ Ioc 0 ℓ <;> simp [h]
    have hi : tauCutoff ℓ τ = (Ioc 0 ℓ).indicator (fun _ => (1 : ℝ)) τ + (u τ - u (τ - ℓ)) := by
      rw [hind]
      simp only [tauCutoff, u]
      ring
    rw [deriv_tauCutoff, hi, hif]
    ring
  have h1 : Integrable fun τ => (Ioc 0 ℓ).indicator f τ + (u τ * f τ - u (τ - ℓ) * f τ) :=
    hI.add (hu.sub hu')
  have h2 : Integrable fun τ => deriv Real.smoothTransition τ * g τ -
      deriv Real.smoothTransition (τ - ℓ) * g τ := hv.sub hv'
  have h3 : Integrable fun τ => u τ * f τ - u (τ - ℓ) * f τ := hu.sub hu'
  rw [e, integral_add h1 h2, integral_add hI h3, integral_sub hu hu', integral_sub hv hv', eu,
    ev, integral_indicator measurableSet_Ioc]
  ring

/-! ## The form `dτ ∧ α` and the Leibniz rule for the cutoff -/

/-- **The 2-form `dτ ∧ α`** for a 1-form `α` on `ℝ³ × ℝ`, as the alternatization of
`v ↦ dτ(v) α`; a continuous linear map of `α`. It is the second term of the Leibniz rule
`d(χ(τ) a) = χ da + χ' dτ ∧ a`. -/
noncomputable def tauWedge : LiftForm 1 →L[ℝ] LiftForm 2 :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ LiftSpace ℝ).comp
    (ContinuousLinearMap.smulRightL ℝ LiftSpace (LiftForm 1) (ContinuousLinearMap.snd ℝ Space ℝ))

/-- `tauWedge α` is the alternatization of `v ↦ dτ(v) α`. -/
theorem tauWedge_apply (α : LiftForm 1) :
    tauWedge α = ContinuousAlternatingMap.alternatizeUncurryFin
      ((ContinuousLinearMap.snd ℝ Space ℝ).smulRight α) := rfl

/-- **Leibniz rule for the cutoff**: `d(χ(τ) a) = χ(τ) da + χ'(τ) dτ ∧ a` for a `C¹` field of
1-forms `a`. -/
theorem extDeriv_tauCutoff_smul (ℓ : ℝ) {a : LiftSpace → LiftForm 1} (ha : ContDiff ℝ 1 a)
    (p : LiftSpace) :
    extDeriv (fun q : LiftSpace => tauCutoff ℓ q.2 • a q) p =
      tauCutoff ℓ p.2 • extDeriv a p + deriv (tauCutoff ℓ) p.2 • tauWedge (a p) := by
  have hc : HasFDerivAt (fun q : LiftSpace => tauCutoff ℓ q.2)
      (deriv (tauCutoff ℓ) p.2 • ContinuousLinearMap.snd ℝ Space ℝ) p :=
    (((contDiff_tauCutoff ℓ).differentiable one_ne_zero p.2).hasDerivAt).comp_hasFDerivAt p
      hasFDerivAt_snd
  have h := extDeriv_function_smul (c := fun q : LiftSpace => tauCutoff ℓ q.2)
    hc.differentiableAt (ha.differentiable one_ne_zero p)
  have e : ((deriv (tauCutoff ℓ) p.2 • ContinuousLinearMap.snd ℝ Space ℝ).smulRight (a p) :
      LiftSpace →L[ℝ] LiftForm 1) =
      deriv (tauCutoff ℓ) p.2 • (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (a p) :=
    ContinuousLinearMap.ext fun v => by simp [mul_smul]
  rw [hc.fderiv, e, ContinuousAlternatingMap.alternatizeUncurryFin_smul] at h
  exact h

/-! ## Periodic fields vanishing outside a compact set of `ℝ³` -/

section Slab

variable {ℓ : ℝ} {Ω K : Set Space} {G : LiftSpace → LiftForm 2} {a : LiftSpace → LiftForm 1}

/-- A field on `ℝ³ × ℝ` that vanishes at `(x, τ)` for `x` outside a compact `K` has closed
support in `K × ℝ`. -/
theorem tsupport_subset_prod_univ {E : Type*} [Zero E] {φ : LiftSpace → E} (hK : IsCompact K)
    (h0 : ∀ x τ, x ∉ K → φ (x, τ) = 0) : tsupport φ ⊆ K ×ˢ (univ : Set ℝ) :=
  closure_minimal (fun p hp => ⟨not_not.1 fun h => hp (h0 p.1 p.2 h), mem_univ _⟩)
    (hK.isClosed.prod isClosed_univ)

/-- The curvature `da` vanishes at `(x, τ)` for `x` outside the compact `K`, when `a` does. -/
theorem extDeriv_eq_zero_of_notMem (hK : IsCompact K) (haK : ∀ x τ, x ∉ K → a (x, τ) = 0)
    {x : Space} (hx : x ∉ K) (τ : ℝ) : extDeriv a (x, τ) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    hx (tsupport_subset_prod_univ hK haK (tsupport_extDeriv_subset h)).1

/-- **The curvature of a periodic field is periodic**: if `a (x, τ + ℓ) = a (x, τ)` then
`da (x, τ + ℓ) = da (x, τ)`. No regularity is needed. -/
theorem extDeriv_tau_periodic (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (x : Space) (τ : ℝ) :
    extDeriv a (x, τ + ℓ) = extDeriv a (x, τ) := by
  have e : (fun p : LiftSpace => a (p + ((0 : Space), ℓ))) = a := by
    funext p
    obtain ⟨y, s⟩ := p
    simpa using hap y s
  have h : extDeriv (fun p : LiftSpace => a (p + ((0 : Space), ℓ))) (x, τ) =
      extDeriv a ((x, τ) + ((0 : Space), ℓ)) := by
    rw [extDeriv, extDeriv, fderiv_comp_add_right]
  rw [e] at h
  rw [h]
  simp

/-- A continuous function on `ℝ³ × ℝ` that vanishes at `(x, τ)` for `x` outside a compact `K` is
integrable on the slab `ℝ³ × (0, ℓ]`. -/
theorem integrableOn_slab_of_continuous {φ : LiftSpace → ℝ} (hφ : Continuous φ)
    (hK : IsCompact K) (h0 : ∀ x τ, x ∉ K → φ (x, τ) = 0) (ℓ : ℝ) :
    IntegrableOn φ ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) := by
  have h1 : IntegrableOn φ (K ×ˢ Icc (0 : ℝ) ℓ) :=
    hφ.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  have h2 : IntegrableOn φ ((univ : Set Space) ×ˢ Icc (0 : ℝ) ℓ) :=
    h1.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc) fun p hp =>
      h0 p.1 p.2 fun hx => hp.2 ⟨hx, hp.1.2⟩
  exact h2.mono_set (prod_mono subset_rfl Ioc_subset_Icc_self)

/-- A function that vanishes at `(x, τ)` for `x` outside `K ⊆ Ω` has the same integral over
`Ω × (0, ℓ]` and over `ℝ³ × (0, ℓ]`. No measurability of `Ω` and no integrability is needed (if
the function is not integrable on one set it is not integrable on the other, and both
integrals are `0`). -/
theorem setIntegral_region_slab_eq {φ : LiftSpace → ℝ} (hKΩ : K ⊆ Ω)
    (h0 : ∀ x τ, x ∉ K → φ (x, τ) = 0) (ℓ : ℝ) :
    ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ, φ p = ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, φ p :=
  (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Ioc)
    (prod_mono (subset_univ _) subset_rfl) fun p hp =>
      h0 p.1 p.2 fun hx => hp.2 ⟨hKΩ hx, hp.1.2⟩).symm

/-- The cross term `⟨G, da⟩` is continuous on `ℝ³ × ℝ` under the hypotheses of
`integral_slab_liftInner_extDeriv_eq_zero` (periodicity is not used): it is the top coefficient
of `d(⋆G ∧ a)` and `⋆G ∧ a` is `C¹`. -/
theorem continuous_liftInner_extDeriv (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (ha : ContDiff ℝ 1 a) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    Continuous fun p => liftInner (G p) (extDeriv a p) := by
  have hU : IsOpen (Ω ×ˢ (univ : Set ℝ)) := hΩ.prod isOpen_univ
  have hs : tsupport a ⊆ Ω ×ˢ (univ : Set ℝ) :=
    (tsupport_subset_prod_univ hK haK).trans (prod_mono hKΩ subset_rfl)
  have hc := contDiff_extDeriv (r := 0) (contDiff_starWedge hU hG ha hs) (by simp)
  have e : (fun p => liftInner (G p) (extDeriv a p)) =
      fun p => extDeriv (starWedge G a) p liftBasis :=
    funext fun p => (extDeriv_starWedge_apply hU hG hcc ha hs p).symm
  rw [e]
  exact hc.continuous.eval_const _

/-- **The cross term is integrable on one period**: `⟨G, da⟩` is integrable on `ℝ³ × (0, ℓ]`. -/
theorem integrableOn_slab_liftInner_extDeriv (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (ha : ContDiff ℝ 1 a) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) (ℓ : ℝ) :
    IntegrableOn (fun p => liftInner (G p) (extDeriv a p))
      ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) :=
  integrableOn_slab_of_continuous (continuous_liftInner_extDeriv hΩ hG hcc ha hK hKΩ haK) hK
    (fun x τ hx => by rw [extDeriv_eq_zero_of_notMem hK haK hx, liftInner_zero_right]) ℓ

/-- **The energy density of the variation is integrable on one period**: `|da|²` is integrable
on `ℝ³ × (0, ℓ]`. -/
theorem integrableOn_slab_liftInner_extDeriv_self (ha : ContDiff ℝ 1 a) (hK : IsCompact K)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) (ℓ : ℝ) :
    IntegrableOn (fun p => liftInner (extDeriv a p) (extDeriv a p))
      ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) := by
  have hd : Continuous (extDeriv a) := (contDiff_extDeriv (r := 0) ha (by simp)).continuous
  exact integrableOn_slab_of_continuous (continuous_liftInner hd hd) hK
    (fun x τ hx => by rw [extDeriv_eq_zero_of_notMem hK haK hx, liftInner_zero_right]) ℓ

/-! ## The cross term over one period -/

/-- **Orthogonality of a co-closed periodic form to periodic exact forms, over one period.**
Let `0 < ℓ`, `Ω ⊆ ℝ³` open, `G` a field of 2-forms on `ℝ³ × ℝ` that is `C¹` and co-closed
(`d(⋆G) = 0`) on `Ω × ℝ` and `ℓ`-periodic in `τ` over `Ω`, and `a` a `C¹` field of 1-forms that
is `ℓ`-periodic in `τ` and vanishes at `(x, τ)` for `x` outside a compact `K ⊆ Ω`. Then

`∫_{ℝ³ × (0, ℓ]} ⟨G, da⟩ = 0`,

for Lebesgue measure. This is the cross term on `Ω × S¹`: the integrand is periodic and
vanishes outside `K × ℝ`. The integrand is integrable on the slab
(`integrableOn_slab_liftInner_extDeriv`), so `0` is not a junk value. Without periodicity of `a`
the statement fails (`Sanity.FormHYMCircleEnergy.nonperiodic_cross_term`). -/
theorem integral_slab_liftInner_extDeriv_eq_zero (hℓ : 0 < ℓ) (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (hGp : ∀ x ∈ Ω, ∀ τ, G (x, τ + ℓ) = G (x, τ)) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, liftInner (G p) (extDeriv a p) = 0 := by
  have hU : IsOpen (Ω ×ˢ (univ : Set ℝ)) := hΩ.prod isOpen_univ
  let b : LiftSpace → LiftForm 1 := fun q => tauCutoff ℓ q.2 • a q
  have hbC : ContDiff ℝ 1 b := ((contDiff_tauCutoff ℓ).comp contDiff_snd).smul ha
  have hb0 : ∀ p : LiftSpace, p ∉ K ×ˢ Icc (0 : ℝ) (ℓ + 1) → b p = 0 := by
    intro p hp
    by_cases hx : p.1 ∈ K
    · have h0 : tauCutoff ℓ p.2 = 0 := tauCutoff_eq_zero hℓ fun h => hp ⟨hx, h⟩
      simp [b, h0]
    · simp [b, haK p.1 p.2 hx]
  have hbc : HasCompactSupport b := HasCompactSupport.intro (hK.prod isCompact_Icc) hb0
  have hbs : tsupport b ⊆ Ω ×ˢ (univ : Set ℝ) :=
    (tsupport_subset_prod_univ hK fun x τ hx => by simp [b, haK x τ hx]).trans
      (prod_mono hKΩ subset_rfl)
  have hF := integrable_liftInner_extDeriv hU hG hcc hbC hbc hbs
  have h0 := integral_liftInner_extDeriv_eq_zero hU hG hcc hbC hbc hbs
  have hexp (p : LiftSpace) : liftInner (G p) (extDeriv b p) =
      tauCutoff ℓ p.2 * liftInner (G p) (extDeriv a p) +
        deriv (tauCutoff ℓ) p.2 * liftInner (G p) (tauWedge (a p)) := by
    rw [extDeriv_tauCutoff_smul ℓ ha p, liftInner_add_right, liftInner_smul_right,
      liftInner_smul_right]
  have hfc := continuous_liftInner_extDeriv hΩ hG hcc ha hK hKΩ haK
  have hin (x : Space) : ∫ τ, liftInner (G (x, τ)) (extDeriv b (x, τ)) =
      ∫ τ in Ioc 0 ℓ, liftInner (G (x, τ)) (extDeriv a (x, τ)) := by
    simp only [hexp]
    by_cases hx : x ∈ K
    · have hxΩ := hKΩ hx
      have hm : Continuous fun τ : ℝ => ((x, τ) : LiftSpace) := by fun_prop
      have hGc : Continuous fun τ : ℝ => G (x, τ) :=
        hG.continuousOn.comp_continuous hm fun τ => ⟨hxΩ, mem_univ _⟩
      have hf : Continuous fun τ : ℝ => liftInner (G (x, τ)) (extDeriv a (x, τ)) :=
        hfc.comp hm
      have hg : Continuous fun τ : ℝ => liftInner (G (x, τ)) (tauWedge (a (x, τ))) :=
        continuous_liftInner hGc (tauWedge.continuous.comp (ha.continuous.comp hm))
      exact integral_tauCutoff_periodic hℓ hf hg
        (fun τ => by rw [hGp x hxΩ, extDeriv_tau_periodic hap])
        (fun τ => by rw [hGp x hxΩ, hap])
    · simp [fun τ => haK x τ hx, fun τ => extDeriv_eq_zero_of_notMem hK haK hx τ]
  have h1 := integral_prod (μ := (volume : Measure Space)) (ν := (volume : Measure ℝ))
    (fun p : LiftSpace => liftInner (G p) (extDeriv b p)) hF
  have h2 : ∫ x : Space, ∫ τ, liftInner (G (x, τ)) (extDeriv b (x, τ)) = 0 := h1.symm.trans h0
  have h3 := setIntegral_prod (μ := (volume : Measure Space)) (ν := (volume : Measure ℝ))
    (fun p : LiftSpace => liftInner (G p) (extDeriv a p)) (s := univ) (t := Ioc (0 : ℝ) ℓ)
    (integrableOn_slab_liftInner_extDeriv hΩ hG hcc ha hK hKΩ haK ℓ)
  refine h3.trans ?_
  rw [setIntegral_univ]
  refine Eq.trans ?_ h2
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hin x).symm)

/-! ## The energy identity over one period -/

/-- **The change of the energy density is integrable on one period**: `|G + da|² - |G|²` is
integrable on `ℝ³ × (0, ℓ]`, with no integrability hypothesis on `G`. -/
theorem integrableOn_slab_energy_perturbation (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (ha : ContDiff ℝ 1 a) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) (ℓ : ℝ) :
    IntegrableOn (fun p => liftInner (G p + extDeriv a p) (G p + extDeriv a p) -
      liftInner (G p) (G p)) ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) := by
  refine (Integrable.add (integrableOn_slab_liftInner_extDeriv_self ha hK haK ℓ)
    (Integrable.const_mul (integrableOn_slab_liftInner_extDeriv hΩ hG hcc ha hK hKΩ haK ℓ) 2)).congr
    (Filter.Eventually.of_forall fun p => ?_)
  exact (liftInner_add_self_sub (G p) (extDeriv a p)).symm

/-- **Energy identity for a periodic variation of the connection, over one period.** Under the
hypotheses of `integral_slab_liftInner_extDeriv_eq_zero`,

`∫_{ℝ³ × (0, ℓ]} (|G + da|² - |G|²) = ∫_{ℝ³ × (0, ℓ]} |da|²`.

Both integrands are integrable on the slab (`integrableOn_slab_energy_perturbation`,
`integrableOn_slab_liftInner_extDeriv_self`); no integrability of `G` is assumed. Both
integrands vanish at `(x, τ)` for `x` outside `K`, so the integrals are integrals over
`Ω × (0, ℓ]` (`setIntegral_region_slab_eq`), that is, over `Ω × S¹`. -/
theorem integral_slab_energy_perturbation (hℓ : 0 < ℓ) (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (hGp : ∀ x ∈ Ω, ∀ τ, G (x, τ + ℓ) = G (x, τ)) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) =
      ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, liftInner (extDeriv a p) (extDeriv a p) := by
  have e : ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) =
      ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (extDeriv a p) (extDeriv a p) + 2 * liftInner (G p) (extDeriv a p)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p =>
      liftInner_add_self_sub (G p) (extDeriv a p))
  rw [e, integral_add (integrableOn_slab_liftInner_extDeriv_self ha hK haK ℓ)
    (Integrable.const_mul (integrableOn_slab_liftInner_extDeriv hΩ hG hcc ha hK hKΩ haK ℓ) 2),
    integral_const_mul,
    integral_slab_liftInner_extDeriv_eq_zero hℓ hΩ hG hcc hGp ha hap hK hKΩ haK]
  ring

/-- **Minimality over one period**: a periodic variation of the connection of a co-closed
periodic curvature does not decrease the energy over `ℝ³ × (0, ℓ]`. -/
theorem integral_slab_energy_perturbation_nonneg (hℓ : 0 < ℓ) (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (hGp : ∀ x ∈ Ω, ∀ τ, G (x, τ + ℓ) = G (x, τ)) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    0 ≤ ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) := by
  rw [integral_slab_energy_perturbation hℓ hΩ hG hcc hGp ha hap hK hKΩ haK]
  exact integral_nonneg fun p => liftInner_self_nonneg _

/-- For a periodic `C¹` variation vanishing outside `K × ℝ`, the energy `∫_{ℝ³ × (0, ℓ]} |da|²`
of the variation over one period vanishes exactly when `da = 0` everywhere on `ℝ³ × ℝ`. -/
theorem integral_slab_liftInner_extDeriv_self_eq_zero_iff (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, liftInner (extDeriv a p) (extDeriv a p) = 0 ↔
      ∀ p, extDeriv a p = 0 := by
  have hd : Continuous (extDeriv a) := (contDiff_extDeriv (r := 0) ha (by simp)).continuous
  have hsub : (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ ⊆
      closure (interior ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ)) := by
    rw [interior_prod_eq, interior_univ, interior_Ioc, closure_prod_eq, closure_univ,
      closure_Ioo hℓ.ne]
    exact prod_mono subset_rfl Ioc_subset_Icc_self
  rw [integral_eq_zero_iff_of_nonneg (fun p => liftInner_self_nonneg _)
    (integrableOn_slab_liftInner_extDeriv_self ha hK haK ℓ)]
  constructor
  · intro h p
    have hEq := Measure.eqOn_of_ae_eq h (continuous_liftInner hd hd).continuousOn
      (continuous_const (y := (0 : ℝ))).continuousOn hsub
    obtain ⟨x, τ⟩ := p
    have hmem : ((x, toIocMod hℓ 0 τ) : LiftSpace) ∈ (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ :=
      ⟨mem_univ _, by simpa using toIocMod_mem_Ioc hℓ 0 τ⟩
    have hz : extDeriv a (x, toIocMod hℓ 0 τ) = 0 := liftInner_self_eq_zero.1 (hEq hmem)
    have hper : Function.Periodic (fun s => extDeriv a (x, s)) ℓ :=
      fun s => extDeriv_tau_periodic hap x s
    have hs := hper.sub_zsmul_eq (toIocDiv hℓ 0 τ) (x := τ)
    rw [self_sub_toIocDiv_zsmul] at hs
    exact hs.symm.trans hz
  · intro h
    refine Filter.Eventually.of_forall fun p => ?_
    change liftInner (extDeriv a p) (extDeriv a p) = 0
    rw [h p]
    exact liftInner_zero_left _

/-- **Strictness over one period**: the energy over `ℝ³ × (0, ℓ]` is unchanged exactly when the
variation does not change the curvature, `da = 0` everywhere on `ℝ³ × ℝ`. -/
theorem integral_slab_energy_perturbation_eq_zero_iff (hℓ : 0 < ℓ) (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (hGp : ∀ x ∈ Ω, ∀ τ, G (x, τ + ℓ) = G (x, τ)) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) = 0 ↔
      ∀ p, extDeriv a p = 0 := by
  rw [integral_slab_energy_perturbation hℓ hΩ hG hcc hGp ha hap hK hKΩ haK]
  exact integral_slab_liftInner_extDeriv_self_eq_zero_iff hℓ ha hap hK haK

/-- The same identity for the Yang–Mills density `½ |F|²` over one period:
`∫ (ym(G + da) - ym(G)) = ∫ ym(da)` on `ℝ³ × (0, ℓ]`, and it is non-negative. Both integrands
are integrable (they are half of those of `integral_slab_energy_perturbation`). -/
theorem integral_slab_ymDensity_perturbation (hℓ : 0 < ℓ) (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ (univ : Set ℝ)))
    (hcc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), extDeriv (fun q => liftStar (G q)) p = 0)
    (hGp : ∀ x ∈ Ω, ∀ τ, G (x, τ + ℓ) = G (x, τ)) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (ymDensity (G p + extDeriv a p) - ymDensity (G p)) =
      ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, ymDensity (extDeriv a p) ∧
    0 ≤ ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, ymDensity (extDeriv a p) := by
  have e (p : LiftSpace) : ymDensity (G p + extDeriv a p) - ymDensity (G p) =
      (1 / 2 : ℝ) * (liftInner (G p + extDeriv a p) (G p + extDeriv a p) -
        liftInner (G p) (G p)) := by
    rw [ymDensity, ymDensity]; ring
  have e' (p : LiftSpace) : ymDensity (extDeriv a p) =
      (1 / 2 : ℝ) * liftInner (extDeriv a p) (extDeriv a p) := by
    rw [ymDensity]; ring
  refine ⟨?_, integral_nonneg fun p => ymDensity_nonneg _⟩
  simp only [e, e']
  rw [integral_const_mul, integral_const_mul,
    integral_slab_energy_perturbation hℓ hΩ hG hcc hGp ha hap hK hKΩ haK]

/-! ## The lift of a vacuum field on `Ω × S¹` -/

/-- **The cross term vanishes for the lift of a vacuum field, over one period**:
`∫_{ℝ³ × (0, ℓ]} ⟨ℱ, da⟩ = 0` for every `C¹` field of 1-forms `a` that is `ℓ`-periodic in `τ` and
vanishes outside `K × ℝ`, `K ⊆ Ω` compact. The integrand is integrable on the slab. -/
theorem VacuumForm.integral_slab_liftInner_hymLift_extDeriv {w : Space → Form 2}
    (h : VacuumForm Ω w) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, liftInner (hymLift w p) (extDeriv a p) = 0 :=
  integral_slab_liftInner_extDeriv_eq_zero hℓ h.isOpen h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift (fun _ _ _ => rfl) ha hap hK hKΩ haK

/-- **Yang–Mills minimality of the lift on `Ω × S¹`, energy identity.** Let `ω` be a vacuum
form on an open `Ω ⊆ ℝ³`, `ℱ = hymLift ω` its anti-self-dual lift, `0 < ℓ`, and `a` a `C¹` field
of 1-forms on `ℝ³ × ℝ` that is `ℓ`-periodic in `τ` (a 1-form on `ℝ³ × S¹`) and vanishes at
`(x, τ)` for `x` outside a compact `K ⊆ Ω`. Then, over one period,

`∫_{ℝ³ × (0, ℓ]} (|ℱ + da|² - |ℱ|²) = ∫_{ℝ³ × (0, ℓ]} |da|²`.

Both integrands are integrable on the slab and vanish outside `K × ℝ`, so these are integrals
over `Ω × S¹`; `ℱ` need not be integrable. This is the source's identity
`∫_M |ℱ + da₁|² - ∫_M |ℱ|² = ∫_M |da₁|²` on `M = Ω × S¹`, for variations vanishing near `∂M`. -/
theorem VacuumForm.integral_slab_energy_hymLift_perturbation {w : Space → Form 2}
    (h : VacuumForm Ω w) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
          liftInner (hymLift w p) (hymLift w p)) =
      ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, liftInner (extDeriv a p) (extDeriv a p) :=
  integral_slab_energy_perturbation hℓ h.isOpen h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift (fun _ _ _ => rfl) ha hap hK hKΩ haK

/-- **Yang–Mills minimality of the lift on `Ω × S¹`**: the change of energy over one period
under a periodic variation vanishing outside `K × ℝ` is non-negative. The integrand is
integrable (`VacuumForm.integrableOn_slab_energy_hymLift_perturbation`). -/
theorem VacuumForm.integral_slab_energy_hymLift_perturbation_nonneg {w : Space → Form 2}
    (h : VacuumForm Ω w) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    0 ≤ ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
          liftInner (hymLift w p) (hymLift w p)) :=
  integral_slab_energy_perturbation_nonneg hℓ h.isOpen h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift (fun _ _ _ => rfl) ha hap hK hKΩ haK

/-- The change of the energy density of the lift under a variation vanishing outside `K × ℝ` is
integrable on one period (periodicity is not needed for this). -/
theorem VacuumForm.integrableOn_slab_energy_hymLift_perturbation {w : Space → Form 2}
    (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) (ℓ : ℝ) :
    IntegrableOn (fun p => liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
      liftInner (hymLift w p) (hymLift w p)) ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) :=
  integrableOn_slab_energy_perturbation h.isOpen h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift ha hK hKΩ haK ℓ

/-- **Strict minimality of the lift on `Ω × S¹`**: the energy over one period is unchanged
exactly when the variation does not change the curvature, `da = 0` everywhere. -/
theorem VacuumForm.integral_slab_energy_hymLift_perturbation_eq_zero_iff {w : Space → Form 2}
    (h : VacuumForm Ω w) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
          liftInner (hymLift w p) (hymLift w p)) = 0 ↔ ∀ p, extDeriv a p = 0 :=
  integral_slab_energy_perturbation_eq_zero_iff hℓ h.isOpen h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift (fun _ _ _ => rfl) ha hap hK hKΩ haK

/-- **Yang–Mills minimality of the lift on `Ω × S¹`, vector language**: for a vacuum field `B`
on `Ω`, `ℱ` the lift of its flux form and `a` as above, over one period
`∫ (ym(ℱ + da) - ym(ℱ)) = ∫ ym(da) ≥ 0`, with `ym(F) = ½ |F|²`. Both integrands are integrable
on the slab. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.integral_slab_ymDensity_hymLift_perturbation
    {B : Space → Space} (h : VacuumField Ω B) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        (ymDensity (hymLift (fluxField B) p + extDeriv a p) -
          ymDensity (hymLift (fluxField B) p)) =
      ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, ymDensity (extDeriv a p) ∧
    0 ≤ ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, ymDensity (extDeriv a p) := by
  have hv := vacuumForm_flux_iff.2 h
  exact integral_slab_ymDensity_perturbation hℓ hv.isOpen hv.contDiffOn_hymLift
    hv.extDeriv_liftStar_hymLift (fun _ _ _ => rfl) ha hap hK hKΩ haK

/-! ## The two energies separately, for finite magnetic energy -/

/-- The energy density of the lift is integrable on `Ω × (0, ℓ]` when `‖B‖²` is integrable on
`Ω`, with `B = flux⁻¹ ω` the vector field of `ω`. -/
theorem integrableOn_slab_liftInner_hymLift (w : Space → Form 2) (ℓ : ℝ)
    (hB : IntegrableOn (fun x => ‖flux.symm (w x)‖ ^ 2) Ω) :
    IntegrableOn (fun p => liftInner (hymLift w p) (hymLift w p)) (Ω ×ˢ Ioc (0 : ℝ) ℓ) := by
  have e : (fun p : LiftSpace => liftInner (hymLift w p) (hymLift w p)) =
      fun p => (fun x => 2 * ‖flux.symm (w x)‖ ^ 2) p.1 :=
    funext fun p => liftInner_hymLiftAt_self (w p.1)
  have hm : (volume : Measure LiftSpace).restrict (Ω ×ˢ Ioc (0 : ℝ) ℓ) =
      (volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) ℓ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, hm, e]
  exact (Integrable.const_mul hB 2).comp_fst _

/-- **The energy of the lift over one period**: `∫_{Ω × (0, ℓ]} |ℱ|² = 2ℓ ∫_Ω |B|²`, with
`B = flux⁻¹ ω`, for `0 ≤ ℓ`, every set `Ω` and every `ω`. Both sides are Bochner integrals: when
`‖B‖²` is not integrable on `Ω` both are the junk value `0`
(`integrableOn_slab_liftInner_hymLift` gives integrability of the left integrand from that of
`‖B‖²`). This is `integral_liftInner_hymLiftCircle` on the fundamental domain. -/
theorem integral_slab_liftInner_hymLift (hℓ : 0 ≤ ℓ) (w : Space → Form 2) (Ω : Set Space) :
    ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ, liftInner (hymLift w p) (hymLift w p) =
      2 * ℓ * ∫ x in Ω, ‖flux.symm (w x)‖ ^ 2 := by
  have e : (fun p : LiftSpace => liftInner (hymLift w p) (hymLift w p)) =
      fun p => (fun x => 2 * ‖flux.symm (w x)‖ ^ 2) p.1 :=
    funext fun p => liftInner_hymLiftAt_self (w p.1)
  have hm : (volume : Measure LiftSpace).restrict (Ω ×ˢ Ioc (0 : ℝ) ℓ) =
      (volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) ℓ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hr : (volume.restrict (Ioc (0 : ℝ) ℓ)).real univ = ℓ := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hℓ]
  rw [e, hm, integral_fun_fst (fun x : Space => 2 * ‖flux.symm (w x)‖ ^ 2), hr,
    integral_const_mul, smul_eq_mul]
  ring

/-- **The energy of the varied connection on `Ω × S¹`.** Let `ω` be a vacuum form on `Ω` with
finite magnetic energy (`‖B‖²` integrable on `Ω`, `B = flux⁻¹ ω`), `ℱ` its lift, `0 < ℓ`, and
`a` a `C¹` field of 1-forms, `ℓ`-periodic in `τ`, vanishing outside `K × ℝ` for a compact
`K ⊆ Ω`. Then `|ℱ + da|²` is integrable on `Ω × (0, ℓ]` and

`∫_{Ω × (0, ℓ]} |ℱ + da|² = 2ℓ ∫_Ω |B|² + ∫_{Ω × (0, ℓ]} |da|²`.

All three integrals are integrals of integrable functions. -/
theorem VacuumForm.integral_slab_energy_hymLift_add {w : Space → Form 2}
    (h : VacuumForm Ω w) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0)
    (hB : IntegrableOn (fun x => ‖flux.symm (w x)‖ ^ 2) Ω) :
    IntegrableOn (fun p => liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p))
        (Ω ×ˢ Ioc (0 : ℝ) ℓ) ∧
      ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ,
          liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) =
        2 * ℓ * (∫ x in Ω, ‖flux.symm (w x)‖ ^ 2) +
          ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ, liftInner (extDeriv a p) (extDeriv a p) := by
  have hE := integrableOn_slab_liftInner_hymLift (Ω := Ω) w ℓ hB
  have hD : IntegrableOn (fun p => liftInner (hymLift w p + extDeriv a p)
      (hymLift w p + extDeriv a p) - liftInner (hymLift w p) (hymLift w p))
      (Ω ×ˢ Ioc (0 : ℝ) ℓ) :=
    (h.integrableOn_slab_energy_hymLift_perturbation ha hK hKΩ haK ℓ).mono_set
      (prod_mono (subset_univ _) subset_rfl)
  have e : (fun p => liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p)) =
      fun p => liftInner (hymLift w p) (hymLift w p) +
        (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
          liftInner (hymLift w p) (hymLift w p)) := by
    funext p; ring
  have hda (x : Space) (τ : ℝ) (hx : x ∉ K) : extDeriv a (x, τ) = 0 :=
    extDeriv_eq_zero_of_notMem hK haK hx τ
  refine ⟨by rw [e]; exact Integrable.add hE hD, ?_⟩
  rw [e, integral_add hE hD, integral_slab_liftInner_hymLift hℓ.le,
    setIntegral_region_slab_eq hKΩ (fun x τ hx => by rw [hda x τ hx, add_zero, sub_self]),
    h.integral_slab_energy_hymLift_perturbation hℓ ha hap hK hKΩ haK,
    setIntegral_region_slab_eq hKΩ
      (φ := fun p => liftInner (extDeriv a p) (extDeriv a p))
      (fun x τ hx => by rw [hda x τ hx, liftInner_zero_right])]

/-- **The lift minimises the Abelian Yang–Mills energy on `Ω × S¹`.** For a vacuum form `ω` on
`Ω` with finite magnetic energy, its lift `ℱ`, and every `C¹` field of 1-forms `a` that is
`ℓ`-periodic in `τ` and vanishes outside `K × ℝ` for a compact `K ⊆ Ω`,

`∫_{Ω × (0, ℓ]} |ℱ|² ≤ ∫_{Ω × (0, ℓ]} |ℱ + da|²`.

Both integrands are integrable (`integrableOn_slab_liftInner_hymLift`,
`VacuumForm.integral_slab_energy_hymLift_add`), and the left side is `2ℓ ∫_Ω |B|²`. This is the
source's sentence "the lift minimizes the Abelian Yang–Mills energy against these
fixed-boundary connection variations", for variations vanishing near `∂Ω × S¹`. -/
theorem VacuumForm.integral_slab_energy_hymLift_le {w : Space → Form 2}
    (h : VacuumForm Ω w) (hℓ : 0 < ℓ) (ha : ContDiff ℝ 1 a)
    (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (haK : ∀ x τ, x ∉ K → a (x, τ) = 0)
    (hB : IntegrableOn (fun x => ‖flux.symm (w x)‖ ^ 2) Ω) :
    ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ, liftInner (hymLift w p) (hymLift w p) ≤
      ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ,
        liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) := by
  rw [(h.integral_slab_energy_hymLift_add hℓ ha hap hK hKΩ haK hB).2,
    integral_slab_liftInner_hymLift hℓ.le]
  have h0 : 0 ≤ ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ, liftInner (extDeriv a p) (extDeriv a p) :=
    integral_nonneg fun p => liftInner_self_nonneg _
  linarith

end Slab

/-! ## The statements on `ℝ³ × (ℝ/ℓℤ)` -/

section Circle

variable (ℓ : ℝ) [Fact (0 < ℓ)]

/-- **The section of the covering map over the fundamental domain**: `(x, θ) ↦ (x, τ)` with
`τ` the representative of `θ` in `(0, ℓ]`. -/
noncomputable def circleSection : Space × AddCircle ℓ → LiftSpace :=
  Prod.map id fun θ => ((AddCircle.equivIoc ℓ 0 θ : Ioc (0 : ℝ) (0 + ℓ)) : ℝ)

/-- `circleSection` is a section of the covering map. -/
theorem liftCover_circleSection (q : Space × AddCircle ℓ) :
    liftCover ℓ (circleSection ℓ q) = q :=
  Prod.ext rfl AddCircle.coe_equivIoc

/-- The section is a measurable embedding. -/
theorem measurableEmbedding_circleSection : MeasurableEmbedding (circleSection ℓ) :=
  MeasurableEmbedding.id.prodMap ((MeasurableEmbedding.subtype_coe measurableSet_Ioc).comp
    (AddCircle.measurableEquivIoc ℓ 0).measurableEmbedding)

/-- **The section is measure preserving** from `ℝ³ × (ℝ/ℓℤ)`, with the product of Lebesgue
measure and the Haar measure of total mass `ℓ`, to `ℝ³ × ℝ` with Lebesgue measure restricted to
the fundamental domain `ℝ³ × (0, ℓ]`. -/
theorem measurePreserving_circleSection :
    MeasurePreserving (circleSection ℓ) volume
      ((volume : Measure LiftSpace).restrict ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ)) := by
  have h2 : MeasurePreserving (fun θ : AddCircle ℓ =>
      ((AddCircle.equivIoc ℓ 0 θ : Ioc (0 : ℝ) (0 + ℓ)) : ℝ)) volume
      (volume.restrict (Ioc (0 : ℝ) (0 + ℓ))) :=
    (measurePreserving_subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurePreserving_equivIoc ℓ)
  have h := (MeasurePreserving.id (volume : Measure Space)).prod h2
  have e : (volume : Measure LiftSpace).restrict ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) =
      (volume : Measure Space).prod (volume.restrict (Ioc (0 : ℝ) (0 + ℓ))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, zero_add]
  rw [e]
  exact h

/-- The section is measure preserving from `Ω × S¹` to the fundamental domain `Ω × (0, ℓ]`, for
every set `Ω ⊆ ℝ³` (measurable or not). -/
theorem measurePreserving_circleSection_restrict (Ω : Set Space) :
    MeasurePreserving (circleSection ℓ)
      ((volume : Measure (Space × AddCircle ℓ)).restrict (Ω ×ˢ (univ : Set (AddCircle ℓ))))
      ((volume : Measure LiftSpace).restrict (Ω ×ˢ Ioc (0 : ℝ) ℓ)) := by
  have hp := (measurePreserving_circleSection ℓ).restrict_preimage_emb
    (measurableEmbedding_circleSection ℓ) (Ω ×ˢ (univ : Set ℝ))
  have e1 : circleSection ℓ ⁻¹' (Ω ×ˢ (univ : Set ℝ)) = Ω ×ˢ (univ : Set (AddCircle ℓ)) := by
    ext q
    simp [circleSection]
  have e2 : ((volume : Measure LiftSpace).restrict ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ)).restrict
      (Ω ×ˢ (univ : Set ℝ)) = (volume : Measure LiftSpace).restrict (Ω ×ˢ Ioc (0 : ℝ) ℓ) := by
    rw [Measure.restrict_restrict' (MeasurableSet.univ.prod measurableSet_Ioc), prod_inter_prod,
      inter_univ, univ_inter]
  rw [e1, e2] at hp
  exact hp

/-- **Integrals over `Ω × S¹` are integrals over the fundamental domain `Ω × (0, ℓ]`** of the
pulled-back function, for every set `Ω` and every function `φ` on `ℝ³ × (ℝ/ℓℤ)`. No
measurability or integrability is needed: `circleSection` is a measure-preserving measurable
embedding, so the two integrands are integrable together
(`integrableOn_circle_iff_integrableOn_slab`) and otherwise both integrals are `0`. -/
theorem setIntegral_circle_eq_setIntegral_slab (Ω : Set Space) (φ : Space × AddCircle ℓ → ℝ) :
    ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)), φ q =
      ∫ p in Ω ×ˢ Ioc (0 : ℝ) ℓ, φ (liftCover ℓ p) := by
  have h := (measurePreserving_circleSection_restrict ℓ Ω).integral_comp
    (measurableEmbedding_circleSection ℓ) (fun p => φ (liftCover ℓ p))
  simp only [liftCover_circleSection] at h
  exact h

/-- A function is integrable on `Ω × S¹` exactly when its pullback is integrable on the
fundamental domain `Ω × (0, ℓ]`. -/
theorem integrableOn_circle_iff_integrableOn_slab (Ω : Set Space)
    (φ : Space × AddCircle ℓ → ℝ) :
    IntegrableOn φ (Ω ×ˢ (univ : Set (AddCircle ℓ))) ↔
      IntegrableOn (fun p => φ (liftCover ℓ p)) (Ω ×ˢ Ioc (0 : ℝ) ℓ) := by
  have h := (measurePreserving_circleSection_restrict ℓ Ω).integrable_comp_emb
    (measurableEmbedding_circleSection ℓ) (g := fun p => φ (liftCover ℓ p))
  have e : (fun p => φ (liftCover ℓ p)) ∘ circleSection ℓ = φ :=
    funext fun q => by simp [liftCover_circleSection]
  rw [e] at h
  exact h

/-- Integrals over `ℝ³ × S¹` are integrals over the fundamental domain `ℝ³ × (0, ℓ]`. -/
theorem integral_circle_eq_integral_slab (φ : Space × AddCircle ℓ → ℝ) :
    ∫ q, φ q = ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ, φ (liftCover ℓ p) := by
  rw [← setIntegral_circle_eq_setIntegral_slab, univ_prod_univ, setIntegral_univ]

variable {ℓ} {Ω K : Set Space} {a : LiftSpace → LiftForm 1} {w : Space → Form 2}
  {D : Space × AddCircle ℓ → LiftForm 2}

/-- The circle form pulled back along the covering map is the lifted form. -/
theorem hymLiftCircle_liftCover (ℓ : ℝ) (w : Space → Form 2) (p : LiftSpace) :
    hymLiftCircle ℓ w (liftCover ℓ p) = hymLift w p :=
  hymLiftCircle_eq ℓ w _

/-- **Yang–Mills minimality of the lift on the manifold `Ω × S¹`, energy identity.** Let `ω`
be a vacuum form on an open `Ω ⊆ ℝ³` and `ℱ = hymLiftCircle ℓ ω` its lift on `ℝ³ × (ℝ/ℓℤ)`. Let
`a` be a `C¹` field of 1-forms on `ℝ³ × ℝ`, `ℓ`-periodic in `τ` (the pullback of a 1-form on
`ℝ³ × S¹`), vanishing at `(x, τ)` for `x` outside a compact `K ⊆ Ω`, and let `D` be the field of
2-forms on `ℝ³ × (ℝ/ℓℤ)` whose pullback is `da` (`D (x, [τ]) = da (x, τ)`). Then

`∫_{Ω × S¹} (|ℱ + D|² - |ℱ|²) = ∫_{Ω × S¹} |D|²`,

for the product of Lebesgue measure and the Haar measure of mass `ℓ`. Both integrands are
integrable (by `integrableOn_circle_iff_integrableOn_slab` and the slab statements). That `D` is
TauCeti's `mextDeriv` of the descended 1-form is not proved; `D` is determined by `a` through
the hypothesis. -/
theorem VacuumForm.integral_circle_energy_hymLift_perturbation
    (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (haK : ∀ x τ, x ∉ K → a (x, τ) = 0)
    (hD : ∀ p, D (liftCover ℓ p) = extDeriv a p) :
    ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)),
        (liftInner (hymLiftCircle ℓ w q + D q) (hymLiftCircle ℓ w q + D q) -
          liftInner (hymLiftCircle ℓ w q) (hymLiftCircle ℓ w q)) =
      ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)), liftInner (D q) (D q) := by
  have hℓ : 0 < ℓ := Fact.out
  have hda (x : Space) (τ : ℝ) (hx : x ∉ K) : extDeriv a (x, τ) = 0 :=
    extDeriv_eq_zero_of_notMem hK haK hx τ
  rw [setIntegral_circle_eq_setIntegral_slab, setIntegral_circle_eq_setIntegral_slab]
  simp only [hymLiftCircle_liftCover, hD]
  rw [setIntegral_region_slab_eq hKΩ (fun x τ hx => by rw [hda x τ hx, add_zero, sub_self]),
    setIntegral_region_slab_eq hKΩ (φ := fun p => liftInner (extDeriv a p) (extDeriv a p))
      (fun x τ hx => by rw [hda x τ hx, liftInner_zero_right])]
  exact h.integral_slab_energy_hymLift_perturbation hℓ ha hap hK hKΩ haK

/-- **The energy of the varied connection on the manifold `Ω × S¹`**, for finite magnetic
energy (`‖B‖²` integrable on `Ω`, `B = flux⁻¹ ω`): with the notation of
`VacuumForm.integral_circle_energy_hymLift_perturbation`, `|ℱ + D|²` is integrable on `Ω × S¹`
and `∫_{Ω × S¹} |ℱ + D|² = 2ℓ ∫_Ω |B|² + ∫_{Ω × S¹} |D|²`. -/
theorem VacuumForm.integral_circle_energy_hymLift_add
    (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (haK : ∀ x τ, x ∉ K → a (x, τ) = 0)
    (hD : ∀ p, D (liftCover ℓ p) = extDeriv a p)
    (hB : IntegrableOn (fun x => ‖flux.symm (w x)‖ ^ 2) Ω) :
    IntegrableOn (fun q => liftInner (hymLiftCircle ℓ w q + D q) (hymLiftCircle ℓ w q + D q))
        (Ω ×ˢ (univ : Set (AddCircle ℓ))) ∧
      ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)),
          liftInner (hymLiftCircle ℓ w q + D q) (hymLiftCircle ℓ w q + D q) =
        2 * ℓ * (∫ x in Ω, ‖flux.symm (w x)‖ ^ 2) +
          ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)), liftInner (D q) (D q) := by
  have hℓ : 0 < ℓ := Fact.out
  obtain ⟨h1, h2⟩ := h.integral_slab_energy_hymLift_add hℓ ha hap hK hKΩ haK hB
  constructor
  · rw [integrableOn_circle_iff_integrableOn_slab]
    simp only [hymLiftCircle_liftCover, hD]
    exact h1
  · rw [setIntegral_circle_eq_setIntegral_slab, setIntegral_circle_eq_setIntegral_slab]
    simp only [hymLiftCircle_liftCover, hD]
    exact h2

/-- **The lift minimises the Abelian Yang–Mills energy on the manifold `Ω × S¹`**: for a vacuum
form `ω` on `Ω` with finite magnetic energy and every variation as in
`VacuumForm.integral_circle_energy_hymLift_perturbation`,

`∫_{Ω × S¹} |ℱ|² ≤ ∫_{Ω × S¹} |ℱ + D|²`.

Both integrands are integrable; the left side is `2ℓ ∫_Ω |B|²`
(`integral_liftInner_hymLiftCircle`). -/
theorem VacuumForm.integral_circle_energy_hymLift_le
    (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hap : ∀ x τ, a (x, τ + ℓ) = a (x, τ))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (haK : ∀ x τ, x ∉ K → a (x, τ) = 0)
    (hD : ∀ p, D (liftCover ℓ p) = extDeriv a p)
    (hB : IntegrableOn (fun x => ‖flux.symm (w x)‖ ^ 2) Ω) :
    ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)),
        liftInner (hymLiftCircle ℓ w q) (hymLiftCircle ℓ w q) ≤
      ∫ q in Ω ×ˢ (univ : Set (AddCircle ℓ)),
        liftInner (hymLiftCircle ℓ w q + D q) (hymLiftCircle ℓ w q + D q) := by
  have hℓ : 0 < ℓ := Fact.out
  rw [setIntegral_circle_eq_setIntegral_slab, setIntegral_circle_eq_setIntegral_slab]
  simp only [hymLiftCircle_liftCover, hD]
  exact h.integral_slab_energy_hymLift_le hℓ ha hap hK hKΩ haK hB

end Circle

end PlasmaLean.Forms
