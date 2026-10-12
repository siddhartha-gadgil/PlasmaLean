/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.ThermalSlab
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exact steady slab heat model

Source: the complete elementary derivation specified in note 07, “First exact
thermal theorem”. SI units: Tc K, q W/m², Q W/m³, h m, k W/(m K), hc W/(m² K).
The model has constant coefficients, uniform volumetric heating, an incoming
surface flux, and convection at x=0. It does not model 3-D cooling or qualification
of any particular material. All physical inputs remain explicit parameters.
-/
public section

noncomputable section
namespace PlasmaLean.Engineering

/-- Closed-form surface maximum for the constant-coefficient slab model. -/
@[expose] def slabMaximum (Tc q Q h k hc : ℝ) : ℝ :=
  Tc + (q + Q * h) / hc + q * h / k + Q * h ^ 2 / (2 * k)

/-- Analytic temperature profile on the slab, with x=0 the cooled face. -/
@[expose] def slabTemperature (Tc q Q h k hc x : ℝ) : ℝ :=
  Tc + (q + Q * h) / hc + (q + Q * h) * x / k - Q * x ^ 2 / (2 * k)

/-- First spatial derivative of the exact slab profile. -/
theorem slab_derivative (Tc q Q h k hc x : ℝ) :
    HasDerivAt (slabTemperature Tc q Q h k hc) ((q + Q * h - Q * x) / k) x := by
  convert (((hasDerivAt_id x).const_mul ((q + Q * h) / k)).const_add
    (Tc + (q + Q * h) / hc)).sub
      (((hasDerivAt_id x).pow 2).const_mul (Q / (2 * k))) using 1
  · funext y
    dsimp [slabTemperature]
    ring
  · dsimp
    ring

/-- The second derivative is constant and satisfies -k T'' = Q when k is nonzero. -/
theorem slab_second_derivative (q Q h k x : ℝ) :
    HasDerivAt (fun x : ℝ => (q + Q * h - Q * x) / k) (-Q / k) x := by
  convert ((hasDerivAt_const x (q + Q * h)).sub
    ((hasDerivAt_id x).const_mul Q)).div_const k using 1 <;> simp

/-- Incoming hot-face flux has the prescribed sign convention. -/
theorem slab_hot_flux (q Q h k : ℝ) (hk : k ≠ 0) :
    k * ((q + Q * h - Q * h) / k) = q := by field_simp; ring

/-- The cooled-face flux equals the convective boundary flux. -/
theorem slab_cold_flux (Tc q Q h k hc : ℝ) (hk : k ≠ 0) (hhc : hc ≠ 0) :
    k * ((q + Q * h) / k) = hc * (slabTemperature Tc q Q h k hc 0 - Tc) := by
  simp [slabTemperature]
  field_simp

/-- Exact factorization of the difference from the hot-face maximum. -/
theorem slab_gap (Tc q Q h k hc x : ℝ) (hk : k ≠ 0) :
    slabMaximum Tc q Q h k hc - slabTemperature Tc q Q h k hc x =
    (h - x) * (2 * q + Q * (h - x)) / (2 * k) := by
  unfold slabMaximum slabTemperature
  field_simp
  ring

/-- The claimed maximum is attained at the hot face. -/
theorem slab_at_hot_face (Tc q Q h k hc : ℝ) (hk : k ≠ 0) :
    slabTemperature Tc q Q h k hc h = slabMaximum Tc q Q h k hc := by
  have hh := slab_gap Tc q Q h k hc h hk
  simp at hh
  linarith

/-- Every point in the slab is bounded by the stated surface maximum. -/
theorem slab_le_maximum (Tc q Q h k hc x : ℝ)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hk : 0 < k) (hx : x ≤ h) :
    slabTemperature Tc q Q h k hc x ≤ slabMaximum Tc q Q h k hc := by
  have hp : 0 ≤ (h-x) * (2*q + Q*(h-x)) / (2*k) := by positivity
  rw [← slab_gap Tc q Q h k hc x (ne_of_gt hk)] at hp
  linarith

/-- A zero heat load gives the coolant temperature everywhere. -/
theorem slab_zero_load (Tc h k hc x : ℝ) : slabTemperature Tc 0 0 h k hc x = Tc := by
  simp [slabTemperature]

/-- Monotonicity across an entire uncertainty box, using lower cooling coefficients. -/
theorem slabMaximum_mono {Tc q Q h k hc Tc' q' Q' h' k' hc' : ℝ}
    (hTc : Tc ≤ Tc') (hq : 0 ≤ q) (hqq : q ≤ q')
    (hQ : 0 ≤ Q) (hQQ : Q ≤ Q') (hh : 0 ≤ h) (hhh : h ≤ h')
    (hk : 0 < k') (hkk : k' ≤ k) (hcpos : 0 < hc') (hcc : hc' ≤ hc) :
    slabMaximum Tc q Q h k hc ≤ slabMaximum Tc' q' Q' h' k' hc' := by
  have hq' := hq.trans hqq
  have hQ' := hQ.trans hQQ
  have hh' := hh.trans hhh
  have hp := mul_le_mul hQQ hhh hh hQ'
  have hr := mul_le_mul hqq hhh hh hq'
  have hs : h ^ 2 ≤ h' ^ 2 := by nlinarith
  have ht := mul_le_mul hQQ hs (sq_nonneg h) hQ'
  have hd₁ := div_le_div₀ (by positivity : 0 ≤ q' + Q' * h') (add_le_add hqq hp) hcpos hcc
  have hd₂ := div_le_div₀ (mul_nonneg hq' hh') hr hk hkk
  have hd₃ := div_le_div₀ (mul_nonneg hQ' (sq_nonneg h')) ht
    (by positivity : 0 < 2 * k') (by linarith : 2 * k' ≤ 2 * k)
  unfold slabMaximum
  linarith

/-- The explicit profile really satisfies both differential and boundary laws. -/
theorem slab_solution (Tc q Q h k hc : ℝ) (hh : 0 ≤ h) (hk : 0 < k) (hhc : 0 < hc) :
    SteadySlab (slabTemperature Tc q Q h k hc)
      (fun x => (q + Q * h - Q * x) / k) Tc q Q h k hc := by
  refine ⟨hh, hk, hhc, ?_, ?_, ?_, ?_⟩
  · intro x _; exact slab_derivative Tc q Q h k hc x
  · intro x _; exact slab_second_derivative q Q h k x
  · exact slab_hot_flux q Q h k (ne_of_gt hk)
  · simpa using slab_cold_flux Tc q Q h k hc (ne_of_gt hk) (ne_of_gt hhc)

private theorem constant_on_slab {f : ℝ → ℝ} {h x : ℝ}
    (hd : ∀ s ∈ Set.Icc 0 h, HasDerivAt f 0 s) (hx : x ∈ Set.Icc 0 h) : f x = f 0 := by
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hd s hs).hasDerivWithinAt) (C := 0) (by intros; simp) x hx
  simp only [zero_mul] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-- Uniqueness of the classical slab boundary-value solution, proved by integrating
the derivative differences twice. Thus the bound is not limited to a chosen ansatz. -/
theorem slab_unique (T dT : ℝ → ℝ) (Tc q Q h k hc : ℝ)
    [laws : SteadySlab T dT Tc q Q h k hc] (x : ℝ) (hx : x ∈ Set.Icc 0 h) :
    T x = slabTemperature Tc q Q h k hc x := by
  have hh := laws.thickness_nonneg
  have hk := laws.conductivity_pos
  have hhc := laws.cooling_pos
  have h₀ : (0 : ℝ) ∈ Set.Icc 0 h := ⟨le_rfl, hh⟩
  have hhmem : h ∈ Set.Icc 0 h := ⟨hh, le_rfl⟩
  have dd : ∀ s ∈ Set.Icc 0 h, HasDerivAt
      (fun z => dT z - (q + Q * h - Q * z) / k) 0 s := by
    intro s hs
    convert (laws.flux_derivative s hs).sub (slab_second_derivative q Q h k s) using 1
    simp
  have dend : dT h - (q + Q * h - Q * h) / k = 0 := by
    have hb := laws.hot_flux
    field_simp
    nlinarith
  have dzero : dT 0 - (q + Q * h - Q * 0) / k = 0 := by
    rw [← constant_on_slab dd hhmem]
    exact dend
  have deq : ∀ s ∈ Set.Icc 0 h, dT s = (q + Q * h - Q * s) / k := by
    intro s hs
    have hd := constant_on_slab dd hs
    rw [dzero] at hd
    exact sub_eq_zero.mp hd
  have tzero : T 0 = slabTemperature Tc q Q h k hc 0 := by
    have hb := laws.cold_flux
    rw [deq 0 h₀] at hb
    have hs := slab_cold_flux Tc q Q h k hc (ne_of_gt hk) (ne_of_gt hhc)
    simp only [mul_zero, sub_zero] at hb
    nlinarith
  have td : ∀ s ∈ Set.Icc 0 h, HasDerivAt
      (fun z => T z - slabTemperature Tc q Q h k hc z) 0 s := by
    intro s hs
    have hd := (laws.temperature_derivative s hs).sub (slab_derivative Tc q Q h k hc s)
    convert hd using 1
    simp [deq s hs]
  have hcst := constant_on_slab td hx
  rw [tzero, sub_self] at hcst
  exact sub_eq_zero.mp hcst

/-- Every solution of the supplied slab laws obeys the hot-face maximum bound. -/
theorem slab_model_bound (T dT : ℝ → ℝ) (Tc q Q h k hc x : ℝ)
    [laws : SteadySlab T dT Tc q Q h k hc]
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hx : x ∈ Set.Icc 0 h) :
    T x ≤ slabMaximum Tc q Q h k hc := by
  rw [slab_unique T dT Tc q Q h k hc x hx]
  exact slab_le_maximum Tc q Q h k hc x hq hQ laws.conductivity_pos hx.2

end PlasmaLean.Engineering
