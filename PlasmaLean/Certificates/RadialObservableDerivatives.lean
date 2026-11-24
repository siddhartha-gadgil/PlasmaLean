/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Differentiating radial tube observables

The compensated numerator in the strength gradient cancels the reference
term proportional to R⁷ before interval evaluation. All gradients are at
fixed azimuth. The trajectory tangent supplies the two radial velocities.
-/

@[expose] public section

namespace PlasmaLean.Certificates.RadialSlabs

/-- Squared field strength from the integer-polynomial field components. -/
noncomputable def strengthSq (r d nr nz : ℝ) := d^2/r^14 + (nr^2+nz^2)/r^16

/-- Squared arclength density of a field line parametrized by azimuth. -/
noncomputable def densitySq (r d nr nz : ℝ) := r^2 + (nr^2+nz^2)/d^2

/-- Numerator of the compensated radial derivative, with R¹⁷ as denominator. -/
noncomputable def strengthNumerator (r d q dr dz qr qz reference vr vz : ℝ) :=
  let diff := d - reference*r^7
  let diffR := dr - 7*reference*r^6
  (2*r^2*d*(r*diffR-7*diff)+r*qr-16*q)*vr + (2*r^3*d*dz+r*qz)*vz

/-- Numerator of the radial derivative of arclength squared, with D³ as denominator. -/
noncomputable def densityNumerator (r d q dr dz qr qz vr vz : ℝ) :=
  (2*r*d^3+d*qr-2*q*dr)*vr + (d*qz-2*q*dz)*vz

/-- Differentiation of the actual squared observables along a radial tangent.
The six gradient entries are the spatial derivatives of the three field
polynomials. The reference field can be chosen independently of their values. -/
theorem observable_derivatives {R D Nr Nz : ℝ → ℝ}
    {u vr vz dr dz nrr nrz nzr nzz : ℝ} (reference : ℝ)
    (hr : HasDerivAt R vr u) (hd : HasDerivAt D (dr * vr + dz * vz) u)
    (hnr : HasDerivAt Nr (nrr * vr + nrz * vz) u) (hnz : HasDerivAt Nz (nzr * vr + nzz * vz) u)
    (rpos : 0 < R u) (dpos : 0 < D u) :
    let q := (Nr u)^2+(Nz u)^2
    let qr := 2*(Nr u*nrr+Nz u*nzr)
    let qz := 2*(Nr u*nrz+Nz u*nzz)
    HasDerivAt (fun x => strengthSq (R x) (D x) (Nr x) (Nz x))
      (strengthNumerator (R u) (D u) q dr dz qr qz reference vr vz / (R u)^17) u ∧
    HasDerivAt (fun x => densitySq (R x) (D x) (Nr x) (Nz x))
      (densityNumerator (R u) (D u) q dr dz qr qz vr vz / (D u)^3) u := by
  dsimp only
  have hq := (hnr.pow 2).add (hnz.pow 2)
  constructor
  · convert ((hd.pow 2).div (hr.pow 14) (pow_ne_zero _ rpos.ne')).add
      (hq.div (hr.pow 16) (pow_ne_zero _ rpos.ne')) using 1
    · rfl
    · unfold strengthNumerator
      simp only [Pi.pow_apply, Pi.add_apply]
      field_simp [rpos.ne']
      ring
  · convert (hr.pow 2).add (hq.div (hd.pow 2) (pow_ne_zero _ dpos.ne')) using 1
    · rfl
    · unfold densityNumerator
      simp only [Pi.pow_apply, Pi.add_apply]
      field_simp [dpos.ne']
      ring

/-- The variational ODE matrix of a quotient-polynomial field at fixed azimuth. -/
theorem quotient_velocity_derivative {d n : ℝ → ℝ} {u vr vz dr dz nr nz : ℝ}
    (hd : HasDerivAt d (dr * vr + dz * vz) u) (hn : HasDerivAt n (nr * vr + nz * vz) u)
    (pos : 0 < d u) :
    HasDerivAt (fun x => n x / d x)
      (((nr*d u-n u*dr)*vr+(nz*d u-n u*dz)*vz)/(d u)^2) u := by
  convert hn.div hd pos.ne' using 1
  ring

end PlasmaLean.Certificates.RadialSlabs
