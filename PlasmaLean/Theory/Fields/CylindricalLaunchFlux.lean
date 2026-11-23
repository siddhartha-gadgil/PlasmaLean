/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract
public import PlasmaLean.Kernel.Forms
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Magnetic flux on a cylindrical launch surface

The orientation is the launch-coordinate tangent followed by the geometric toroidal-angle
tangent. Each component on the right is a physical cylindrical component.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Forms

open Real PlasmaLean.Fields PlasmaLean.Contract WithLp

/-- The flux two-form on the two partial derivatives of a cylindrical chart. Here `duR`,
`duZ` are the derivatives in its first coordinate and `dpR`, `dpZ` in its toroidal angle. -/
theorem cylindrical_launch_flux {R z : ℝ → ℝ → ℝ} (B : Space → Space)
    {u φ duR duZ dpR dpZ : ℝ}
    (hRu : HasDerivAt (fun v => R v φ) duR u) (hZu : HasDerivAt (fun v => z v φ) duZ u)
    (hRp : HasDerivAt (R u) dpR φ) (hZp : HasDerivAt (z u) dpZ φ) :
    let X := fun v p => cylPoint (R v p) p (z v p)
    let V := B (X u φ)
    flux V ![deriv (fun v => X v φ) u, deriv (X u) φ] =
      -(cos φ * V 0 + sin φ * V 1) * R u φ * duZ +
      (-sin φ * V 0 + cos φ * V 1) * (duZ * dpR - duR * dpZ) + V 2 * R u φ * duR := by
  dsimp only
  have hu := (hasDerivAt_poloidalLoop hRu hZu).deriv
  have hp := (hasDerivAt_space3 (hRp.mul (hasDerivAt_cos φ)) (hRp.mul (hasDerivAt_sin φ)) hZp).deriv
  change deriv (fun v => cylPoint (R v φ) φ (z v φ)) u = _ at hu
  change deriv (fun p => cylPoint (R u p) p (z u p)) φ = _ at hp
  rw [hu, hp, flux_apply, volForm_vec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (B (cylPoint (R u φ) φ (z u φ)) 2 * R u φ * duR) *
    (sin_sq_add_cos_sq φ)

/-- Specialization to straight interpolation of two cylindrical section curves in a
meridian plane. It computes the pullback density used in the deep bounce launch screen. -/
theorem interpolated_launch_flux (B : Space → Space) {RC RA zC zA : ℝ → ℝ} (u φ : ℝ)
    (hRC : DifferentiableAt ℝ RC φ) (hRA : DifferentiableAt ℝ RA φ)
    (hzC : DifferentiableAt ℝ zC φ) (hzA : DifferentiableAt ℝ zA φ) :
    let cut := fun (c a : ℝ → ℝ) (v p : ℝ) => c p + v * (a p - c p)
    let X := fun v p => cylPoint (cut RC RA v p) p (cut zC zA v p)
    let V := B (X u φ)
    let dR := RA φ - RC φ
    let dz := zA φ - zC φ
    flux V ![deriv (fun v => X v φ) u, deriv (X u) φ] =
      -(cos φ * V 0 + sin φ * V 1) * cut RC RA u φ * dz +
      (-sin φ * V 0 + cos φ * V 1) *
        (dz * cut (deriv RC) (deriv RA) u φ - dR * cut (deriv zC) (deriv zA) u φ) +
      V 2 * cut RC RA u φ * dR := by
  dsimp only
  apply cylindrical_launch_flux (R := fun v p => RC p + v * (RA p - RC p))
    (z := fun v p => zC p + v * (zA p - zC p)) B
  · simpa using ((hasDerivAt_id u).mul_const (RA φ - RC φ)).const_add (RC φ)
  · simpa using ((hasDerivAt_id u).mul_const (zA φ - zC φ)).const_add (zC φ)
  · exact hRC.hasDerivAt.add ((hRA.hasDerivAt.sub hRC.hasDerivAt).const_mul u)
  · exact hzC.hasDerivAt.add ((hzA.hasDerivAt.sub hzC.hasDerivAt).const_mul u)

/-- A uniform lower bound for the oriented density gives a geometric flux budget on a
parametrized launch rectangle. The observable integrates over the parameter space, so no
global return-map injectivity or probabilistic birth-law normalization is implicit. -/
theorem launch_flux_lower_bound {F : ℝ → ℝ → ℝ} (hc : Continuous F.uncurry)
    {u₀ u₁ p₀ p₁ m : ℝ} (hu : u₀ ≤ u₁) (hp : p₀ ≤ p₁)
    (hF : ∀ u ∈ Set.Icc u₀ u₁, ∀ p ∈ Set.Icc p₀ p₁, m ≤ F u p) :
    (u₁ - u₀) * (p₁ - p₀) * m ≤ ∫ u in u₀..u₁, ∫ p in p₀..p₁, F u p := by
  have hphi (u) (hu' : u ∈ Set.Icc u₀ u₁) :
      (p₁ - p₀) * m ≤ ∫ p in p₀..p₁, F u p := by
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hp
      intervalIntegrable_const
      ((hc.uncurry_left u).intervalIntegrable _ _) (hF u hu')
    simpa using h
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := p₀) (μ := MeasureTheory.volume) hc (continuous_const (y := p₁))
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hu
    intervalIntegrable_const
    (hi.intervalIntegrable _ _) hphi
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  exact (le_of_eq (by ring)).trans h

end PlasmaLean.Forms
