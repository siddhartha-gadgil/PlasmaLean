/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceField
public import PlasmaLean.Design.DommaschkKamCQSIdent
public import PlasmaLean.Certificates.RadialObservableDerivatives
public import PlasmaLean.Theory.Kinetic.MirrorArclength

/-!
# Physical observables in the Dommaschk mirror certificates

The same three polynomial values give the physical field strength and the
arclength density per radian. These identities hold at every cylindrical
point of positive radius with positive toroidal field, including between tori.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBounceField

open PlasmaLean.Contract DommaschkKam Certificates.RadialSlabs
open Kinetic.GCLittlejohn

local notation "Bdk" => DommaschkQA2R.field DommaschkQA2R.candidate

/-- Squared field strength at an arbitrary physical point from the three checked polynomials. -/
theorem norm_sq_eq_strengthSq {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    ‖Bdk (cylPoint R φ z)‖ ^ 2 =
      strengthSq R (atPoint dD R φ z) (atPoint dnR R φ z) (atPoint dnZ R φ z) := by
  obtain ⟨d, nr, nz⟩ := field_id hR φ z
  rw [DommaschkKamC.norm_field_sq, strengthSq, d, nr, nz]
  field_simp [hR.ne']
  ring

/-- Positivity of the denominator certificate orients the azimuthal clock. -/
theorem toroidal_pos_of_den {R φ z : ℝ} (hR : 0 < R) (hD : 0 < atPoint dD R φ z) :
    0 < cylBphi R φ z := by
  rw [(field_id hR φ z).1] at hD
  exact pos_of_mul_pos_right hD (by positivity)

/-- Squared physical arclength density from the same point and angular clock. -/
theorem arclength_sq_eq_densitySq {R φ z : ℝ} (hR : 0 < R) (hD : 0 < atPoint dD R φ z) :
    (R * ‖Bdk (cylPoint R φ z)‖ / cylBphi R φ z) ^ 2 =
      densitySq R (atPoint dD R φ z) (atPoint dnR R φ z) (atPoint dnZ R φ z) := by
  have hφ := toroidal_pos_of_den hR hD
  obtain ⟨d, nr, nz⟩ := field_id hR φ z
  rw [div_pow, mul_pow, DommaschkKamC.norm_field_sq, densitySq, d, nr, nz]
  field_simp [hR.ne', hφ.ne']
  ring

set_option maxRecDepth 8000 in
/-- A true trace of the physical ODE has the arclength density used by the action quadrature. -/
theorem physical_trace_tangent (R z : ℝ → ℝ) (α t : ℝ) (hR : 0 < R t)
    (hD : 0 < atPoint dD (R t) (α + t) (z t))
    (dr : HasDerivAt R (R t * cylBR (R t) (α + t) (z t) / cylBphi (R t) (α + t) (z t)) t)
    (dz : HasDerivAt z (R t * cylBz (R t) (α + t) (z t) / cylBphi (R t) (α + t) (z t)) t) :
    let X := fun s => cylPoint (R s) (α + s) (z s)
    let p := fun a => atPoint a (R t) (α + t) (z t)
    HasDerivAt X (Real.sqrt (densitySq (R t) (p dD) (p dnR) (p dnZ)) • bhat Bdk (X t)) t := by
  have hp := toroidal_pos_of_den hR hD
  have θ : -Real.sin (α + t) * (Bdk (cylPoint (R t) (α + t) (z t))) 0 +
      Real.cos (α + t) * (Bdk (cylPoint (R t) (α + t) (z t))) 1 =
      cylBphi (R t) (α + t) (z t) := by simp [cylBphi]
  have geom := Kinetic.MirrorWell.cylindrical_trace_speed Bdk R z α t hR
  dsimp only at geom ⊢
  rw [θ] at geom
  unfold cylBR at dr
  unfold cylBz at dz
  have result := @geom hp dr dz
  have hs := result.1
  have tangent := result.2.2
  rw [← arclength_sq_eq_densitySq hR hD, Real.sqrt_sq hs.le]
  exact tangent

end PlasmaLean.Design.DommaschkBounceField
