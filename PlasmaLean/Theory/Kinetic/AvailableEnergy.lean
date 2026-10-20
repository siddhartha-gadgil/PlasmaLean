/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Available-energy kernel and the min-B ⇒ max-J sign check

Track T8 (source: `notes/microturbulence-and-available-energy.md` §2.3, §3, §4).

## Available-energy kernel

The simplified kernel as stated in the project note (not yet checked against
Mackenbach–Proll–Helander, PRL 128, 175001; ramp vs. step `Θ` is unresolved) is
`availableEnergyKernel ω⋆ ωα = max 0 (ω⋆ (ω⋆ - ωα))`
with `ω⋆` the diamagnetic and `ωα` the bounce-averaged precession frequency. We prove
nonnegativity, the exact zero set, vanishing when the frequencies have matching signs and
precession dominates (`|ωα| ≥ |ω⋆|`), antitonicity in `ωα` for `ω⋆ ≥ 0`, the value `ω⋆²` at
`ωα = 0`, and for the energy-dependent `ω̂⋆(z) = ωₙ + (z - 3/2) ω_T` an explicit interval of
normalized energies `z` on which the kernel vanishes.

**Correction to the source note.** The note's "Key Verification Insight" claims that the
integrand vanishes when `ω⋆` and `ωα` have *opposite* signs. This is false: opposite signs
give `ω⋆(ω⋆ - ωα) = ω⋆² + |ω⋆||ωα| > 0` whenever `ω⋆ ≠ 0`
(`availableEnergyKernel_pos_of_opposite_signs`). The kernel vanishes exactly when `ω⋆` lies
between `0` and `ωα`, i.e. matching signs with `|ω⋆| ≤ |ωα|`.

## Bounce action and the radial-derivative expression

`NormalizedBounceAction` and `BounceActionRadialDeriv` follow the note's definitions with
fixed integration limits. The latter is the *expression*
`-(λ/2) ∫_{l_min}^{l_max} ∂_ψB / √(max 0 (1 - λB)) dl`; its identification with the true
`∂J/∂ψ` (endpoint differentiation) is not proved here. Because the integrand has an inverse
square-root endpoint singularity and the Bochner integral of a non-integrable function is
`0`, the sign theorem `bounceActionRadialDeriv_neg` assumes interval integrability
explicitly, together with `l_min < l_max`, `λ > 0`, and on the open interval
`∂_ψB > 0` and `1 - λB > 0`.
-/
public section

noncomputable section
namespace PlasmaLean.Kinetic.AvailableEnergy

/-- Simplified available-energy kernel `max 0 (ω⋆ (ω⋆ - ωα))` as stated in the project note;
not yet checked against the source (Mackenbach–Proll–Helander, PRL 128, 175001). -/
@[expose] def availableEnergyKernel (ωs ωa : ℝ) : ℝ :=
  max 0 (ωs * (ωs - ωa))

/-- The kernel is nonnegative. -/
theorem availableEnergyKernel_nonneg (ωs ωa : ℝ) : 0 ≤ availableEnergyKernel ωs ωa :=
  le_max_left _ _

/-- The kernel vanishes iff `ω⋆ (ω⋆ - ωα) ≤ 0`. -/
theorem availableEnergyKernel_eq_zero_iff (ωs ωa : ℝ) :
    availableEnergyKernel ωs ωa = 0 ↔ ωs * (ωs - ωa) ≤ 0 := by
  unfold availableEnergyKernel
  constructor
  · intro h
    have := le_max_right 0 (ωs * (ωs - ωa))
    linarith
  · intro h
    exact max_eq_left h

/-- Elementary zero-set characterization: `x (x - a) ≤ 0` iff `x` lies between `0` and `a`. -/
theorem mul_sub_nonpos_iff (x a : ℝ) :
    x * (x - a) ≤ 0 ↔ min 0 a ≤ x ∧ x ≤ max 0 a := by
  rcases le_total 0 a with ha | ha
  · rw [min_eq_left ha, max_eq_right ha]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      nlinarith
  · rw [min_eq_right ha, max_eq_left ha]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      nlinarith

/-- The kernel vanishes iff `ω⋆` lies between `0` and `ωα`. -/
theorem availableEnergyKernel_eq_zero_iff_between (ωs ωa : ℝ) :
    availableEnergyKernel ωs ωa = 0 ↔ min 0 ωa ≤ ωs ∧ ωs ≤ max 0 ωa := by
  rw [availableEnergyKernel_eq_zero_iff, mul_sub_nonpos_iff]

/-- Precession dominance with matching signs (`ω⋆ ωα ≥ 0`, `|ω⋆| ≤ |ωα|`) kills the kernel. -/
theorem availableEnergyKernel_eq_zero_of_dominant (ωs ωa : ℝ) (hsign : 0 ≤ ωs * ωa)
    (hdom : |ωs| ≤ |ωa|) : availableEnergyKernel ωs ωa = 0 := by
  rw [availableEnergyKernel_eq_zero_iff]
  have h1 : ωs * ωa = |ωs| * |ωa| := by rw [← abs_mul, abs_of_nonneg hsign]
  have h2 : ωs * ωs = |ωs| * |ωs| := by rw [← abs_mul, abs_mul_self]
  have h3 := abs_nonneg ωs
  nlinarith

/-- Correction of the note: opposite signs (`ω⋆ ωα ≤ 0`) with `ω⋆ ≠ 0` give a *positive*
kernel, at least `ω⋆²`. -/
theorem availableEnergyKernel_pos_of_opposite_signs (ωs ωa : ℝ) (hsign : ωs * ωa ≤ 0)
    (hs : ωs ≠ 0) : ωs ^ 2 ≤ availableEnergyKernel ωs ωa ∧ 0 < availableEnergyKernel ωs ωa := by
  have hpos : 0 < ωs ^ 2 := by positivity
  have hle : ωs ^ 2 ≤ ωs * (ωs - ωa) := by nlinarith
  exact ⟨hle.trans (le_max_right _ _), hpos.trans_le (hle.trans (le_max_right _ _))⟩

/-- Concrete refutation of "zero under opposite signs": `ω⋆ = 1`, `ωα = -1` gives `2`. -/
theorem availableEnergyKernel_one_neg_one : availableEnergyKernel 1 (-1) = 2 := by
  norm_num [availableEnergyKernel]

/-- With no precession the kernel is `ω⋆²`. -/
theorem availableEnergyKernel_zero_precession (ωs : ℝ) :
    availableEnergyKernel ωs 0 = ωs ^ 2 := by
  rw [availableEnergyKernel, sub_zero, ← sq]
  exact max_eq_right (sq_nonneg ωs)

/-- With no drive (`ω⋆ = 0`) the kernel vanishes. -/
theorem availableEnergyKernel_zero_drive (ωa : ℝ) : availableEnergyKernel 0 ωa = 0 := by
  simp [availableEnergyKernel]

/-- For `ω⋆ ≥ 0` the kernel is antitone in the precession frequency `ωα`. -/
theorem availableEnergyKernel_antitone {ωs : ℝ} (hs : 0 ≤ ωs) :
    Antitone (availableEnergyKernel ωs) := by
  intro a b hab
  unfold availableEnergyKernel
  exact max_le_max le_rfl (by nlinarith)

/-- For `ω⋆ > 0`, the kernel is strictly decreasing in `ωα` on `ωα < ω⋆` (where it is
positive). -/
theorem availableEnergyKernel_strictAntiOn {ωs : ℝ} (hs : 0 < ωs) :
    StrictAntiOn (availableEnergyKernel ωs) (Set.Iio ωs) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  unfold availableEnergyKernel
  rw [max_eq_right (by nlinarith), max_eq_right (by nlinarith)]
  nlinarith

/-! ### Energy-dependent diamagnetic frequency -/

/-- The energy-dependent diamagnetic frequency `ω̂⋆(z) = ωₙ + (z - 3/2) ω_T`. -/
@[expose] def omegaStarHat (ωn ωT z : ℝ) : ℝ :=
  ωn + (z - 3 / 2) * ωT

/-- Affine inversion, lower endpoint, `ω_T > 0`. -/
theorem zLower_iff_of_pos {ωn ωT m z : ℝ} (hT : 0 < ωT) :
    3 / 2 + (m - ωn) / ωT ≤ z ↔ m ≤ ωn + (z - 3 / 2) * ωT := by
  have hq : (m - ωn) / ωT * ωT = m - ωn := div_mul_cancel₀ _ hT.ne'
  constructor
  · intro h; nlinarith [mul_le_mul_of_nonneg_right h hT.le]
  · intro h; by_contra! hc; nlinarith [mul_lt_mul_of_pos_right hc hT]

/-- Affine inversion, upper endpoint, `ω_T > 0`. -/
theorem zUpper_iff_of_pos {ωn ωT m z : ℝ} (hT : 0 < ωT) :
    z ≤ 3 / 2 + (m - ωn) / ωT ↔ ωn + (z - 3 / 2) * ωT ≤ m := by
  have hq : (m - ωn) / ωT * ωT = m - ωn := div_mul_cancel₀ _ hT.ne'
  constructor
  · intro h; nlinarith [mul_le_mul_of_nonneg_right h hT.le]
  · intro h; by_contra! hc; nlinarith [mul_lt_mul_of_pos_right hc hT]

/-- Affine inversion, lower endpoint, `ω_T < 0`. -/
theorem zLower_iff_of_neg {ωn ωT m z : ℝ} (hT : ωT < 0) :
    3 / 2 + (m - ωn) / ωT ≤ z ↔ ωn + (z - 3 / 2) * ωT ≤ m := by
  have hq : (m - ωn) / ωT * ωT = m - ωn := div_mul_cancel₀ _ hT.ne
  constructor
  · intro h; nlinarith [mul_le_mul_of_nonpos_right h hT.le]
  · intro h; by_contra! hc; nlinarith [mul_lt_mul_of_neg_right hc hT]

/-- Affine inversion, upper endpoint, `ω_T < 0`. -/
theorem zUpper_iff_of_neg {ωn ωT m z : ℝ} (hT : ωT < 0) :
    z ≤ 3 / 2 + (m - ωn) / ωT ↔ m ≤ ωn + (z - 3 / 2) * ωT := by
  have hq : (m - ωn) / ωT * ωT = m - ωn := div_mul_cancel₀ _ hT.ne
  constructor
  · intro h; nlinarith [mul_le_mul_of_nonpos_right h hT.le]
  · intro h; by_contra! hc; nlinarith [mul_lt_mul_of_neg_right hc hT]

/-- For `ω_T > 0`, the kernel at energy `z` vanishes exactly on the interval
`z ∈ [3/2 + (min 0 ωα - ωₙ)/ω_T, 3/2 + (max 0 ωα - ωₙ)/ω_T]`. -/
theorem kernel_zero_set_pos_gradient {ωn ωT ωa : ℝ} (hT : 0 < ωT) (z : ℝ) :
    availableEnergyKernel (omegaStarHat ωn ωT z) ωa = 0 ↔
      z ∈ Set.Icc (3 / 2 + (min 0 ωa - ωn) / ωT) (3 / 2 + (max 0 ωa - ωn) / ωT) := by
  rw [availableEnergyKernel_eq_zero_iff_between, Set.mem_Icc, omegaStarHat]
  rw [zLower_iff_of_pos hT, zUpper_iff_of_pos hT]

/-- For `ω_T < 0`, the zero set is the interval with the roles of `min` and `max` swapped:
`z ∈ [3/2 + (max 0 ωα - ωₙ)/ω_T, 3/2 + (min 0 ωα - ωₙ)/ω_T]`. -/
theorem kernel_zero_set_neg_gradient {ωn ωT ωa : ℝ} (hT : ωT < 0) (z : ℝ) :
    availableEnergyKernel (omegaStarHat ωn ωT z) ωa = 0 ↔
      z ∈ Set.Icc (3 / 2 + (max 0 ωa - ωn) / ωT) (3 / 2 + (min 0 ωa - ωn) / ωT) := by
  rw [availableEnergyKernel_eq_zero_iff_between, Set.mem_Icc, omegaStarHat]
  rw [zLower_iff_of_neg hT, zUpper_iff_of_neg hT, and_comm]

/-- For `ω_T = 0` the zero set is all energies or none, according to `ωₙ(ωₙ - ωα) ≤ 0`. -/
theorem kernel_zero_set_flat (ωn ωa z : ℝ) :
    availableEnergyKernel (omegaStarHat ωn 0 z) ωa = 0 ↔ ωn * (ωn - ωa) ≤ 0 := by
  rw [availableEnergyKernel_eq_zero_iff, omegaStarHat, mul_zero, add_zero]

/-- Sanity: with `ωₙ = 0`, `ω_T = 1`, `ωα = 1` the kernel vanishes exactly for
`z ∈ [3/2, 5/2]`. -/
theorem kernel_zero_set_example (z : ℝ) :
    availableEnergyKernel (omegaStarHat 0 1 z) 1 = 0 ↔ z ∈ Set.Icc (3 / 2) (5 / 2) := by
  rw [kernel_zero_set_pos_gradient one_pos]
  norm_num

/-! ### Bounce action and the min-B ⇒ max-J sign check -/

/-- Normalized bounce action `∫_{l_min}^{l_max} √(max 0 (1 - λ B(ψ, α, l))) dl` with fixed
limits (the `max 0` guard only matters outside the bounce interval). -/
@[expose] def NormalizedBounceAction (B : ℝ → ℝ → ℝ → ℝ) (lmin lmax ψ α lam : ℝ) : ℝ :=
  ∫ l in lmin..lmax, Real.sqrt (max 0 (1 - lam * B ψ α l))

/-- The note's radial-derivative expression
`-(λ/2) ∫_{l_min}^{l_max} ∂_ψB(ψ, α, l) / √(max 0 (1 - λB(ψ, α, l))) dl`. -/
@[expose] def BounceActionRadialDeriv (B dB : ℝ → ℝ → ℝ → ℝ) (lmin lmax ψ α lam : ℝ) : ℝ :=
  -(lam / 2) * ∫ l in lmin..lmax, dB ψ α l / Real.sqrt (max 0 (1 - lam * B ψ α l))

/-- Sanity: the bounce action is nonnegative for correctly ordered limits. -/
theorem normalizedBounceAction_nonneg (B : ℝ → ℝ → ℝ → ℝ) {lmin lmax : ℝ} (h : lmin ≤ lmax)
    (ψ α lam : ℝ) : 0 ≤ NormalizedBounceAction B lmin lmax ψ α lam :=
  intervalIntegral.integral_nonneg h fun _ _ => Real.sqrt_nonneg _

/-- Min-B ⇒ max-J (sign of the expression): if `l_min < l_max`, `λ > 0`, the integrand is
interval integrable, and on the open bounce interval `∂_ψB > 0` and `1 - λB > 0`, then
the radial-derivative expression is negative. -/
theorem bounceActionRadialDeriv_neg (B dB : ℝ → ℝ → ℝ → ℝ) {lmin lmax ψ α lam : ℝ}
    (hl : lmin < lmax) (hlam : 0 < lam)
    (hint : IntervalIntegrable (fun l => dB ψ α l / Real.sqrt (max 0 (1 - lam * B ψ α l)))
      MeasureTheory.volume lmin lmax)
    (hdB : ∀ l ∈ Set.Ioo lmin lmax, 0 < dB ψ α l)
    (htrap : ∀ l ∈ Set.Ioo lmin lmax, 0 < 1 - lam * B ψ α l) :
    BounceActionRadialDeriv B dB lmin lmax ψ α lam < 0 := by
  have hpos : 0 < ∫ l in lmin..lmax, dB ψ α l / Real.sqrt (max 0 (1 - lam * B ψ α l)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun l hl' => ?_) hl
    have ht := htrap l hl'
    exact div_pos (hdB l hl') (Real.sqrt_pos.mpr (lt_max_of_lt_right ht))
  unfold BounceActionRadialDeriv
  have : 0 < lam / 2 := by positivity
  nlinarith

/-- Sanity: reversing the limits flips the sign, so `l_min < l_max` cannot be dropped. -/
theorem bounceActionRadialDeriv_symm (B dB : ℝ → ℝ → ℝ → ℝ) (lmin lmax ψ α lam : ℝ) :
    BounceActionRadialDeriv B dB lmax lmin ψ α lam =
      -BounceActionRadialDeriv B dB lmin lmax ψ α lam := by
  unfold BounceActionRadialDeriv
  rw [intervalIntegral.integral_symm]
  ring

/-- Non-vacuity fixture: `B(ψ, α, l) = 1 + ψ` (so `∂_ψB = 1`) at `ψ = 0`, `λ = 1/2` on
`[0, 1]` satisfies all hypotheses, and the expression is negative. -/
theorem bounceActionRadialDeriv_fixture :
    BounceActionRadialDeriv (fun ψ _ _ => 1 + ψ) (fun _ _ _ => 1) 0 1 0 0 (1 / 2) < 0 := by
  refine bounceActionRadialDeriv_neg _ _ one_pos (by norm_num) ?_ (fun _ _ => one_pos)
    (fun _ _ => by norm_num)
  exact intervalIntegrable_const

end PlasmaLean.Kinetic.AvailableEnergy
