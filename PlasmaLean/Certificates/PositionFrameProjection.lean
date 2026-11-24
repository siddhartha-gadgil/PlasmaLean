/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameODE

/-! # Coordinate projections of an affine moving ellipsoid

A two-dimensional Euclidean trial ball maps inside a coordinate box whenever
both row lengths at both frame endpoints fit the requested radius. Convexity of
each coordinate bound gives the result throughout the slab.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameProjection
open PositionFrameSlabs

/-- Squared integer check for one row of an endpoint frame. -/
def rowFits (a b : ℤ) (trial radius : ℕ) : Prop :=
  (a ^ 2 + b ^ 2) * (trial : ℤ) ^ 2 ≤ ((radius : ℤ) * 2^40) ^ 2

/-- Four integer inequalities for two coordinates at two time endpoints. -/
structure Fits (left right : Frame) (trial radius : ℕ) : Prop where
  leftR : rowFits left.a left.b trial radius
  leftZ : rowFits left.c left.d trial radius
  rightR : rowFits right.a right.b trial radius
  rightZ : rowFits right.c right.d trial radius

private theorem endpoint_bound {a b : ℤ} {w r : ℕ} (h : rowFits a b w r) {v : Plane}
    (hv : ‖v‖ ≤ (w : ℝ) / 2 ^ 80) :
    |(a:ℝ)/2^40*v 0 + (b:ℝ)/2^40*v 1| ≤ (r:ℝ)/2^80 := by
  change (a^2+b^2) * (w:ℤ)^2 ≤ ((r:ℤ)*2^40)^2 at h
  have hr : ((a:ℝ)^2+(b:ℝ)^2)*(w:ℝ)^2 ≤ ((r:ℝ)*2^40)^2 := by exact_mod_cast h
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  calc
    _ ≤ (((a:ℝ)/2^40)^2+((b:ℝ)/2^40)^2) * ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      nlinarith only [sq_nonneg ((a:ℝ)/2^40*v 1 - (b:ℝ)/2^40*v 0)]
    _ ≤ (((a:ℝ)/2^40)^2+((b:ℝ)/2^40)^2) * ((w:ℝ)/2^80)^2 := by
      gcongr
    _ ≤ _ := by nlinarith only [hr]

private theorem interpolate {a b c d : ℤ} {t : ℝ} {x y R : ℝ} (ht : |t| ≤ 1)
    (h₀ : |(a : ℝ) / 2 ^ 40 * x + (b : ℝ) / 2 ^ 40 * y| ≤ R)
    (h₁ : |(c : ℝ) / 2 ^ 40 * x + (d : ℝ) / 2 ^ 40 * y| ≤ R) :
    |entry a c t*x + entry b d t*y| ≤ R := by
  obtain ⟨l,r⟩ := abs_le.mp ht
  have al : 0 ≤ (1-t)/2 := by linarith
  have ar : 0 ≤ (1+t)/2 := by linarith
  rw [show entry a c t*x + entry b d t*y =
      (1-t)/2*((a:ℝ)/2^40*x + (b:ℝ)/2^40*y) +
      (1+t)/2*((c:ℝ)/2^40*x + (d:ℝ)/2^40*y) by unfold entry; push_cast; ring]
  apply (abs_add_le ..).trans
  rw [abs_mul, abs_mul, abs_of_nonneg al, abs_of_nonneg ar]
  linarith only [mul_le_mul_of_nonneg_left h₀ al, mul_le_mul_of_nonneg_left h₁ ar]

/-- The actual affine frame sends the entire Euclidean ball into a uniform
coordinate box, with no enlargement of the target radius at intermediate times. -/
theorem coordinates_le {l r : Frame} {w p : ℕ} (ok : Fits l r w p)
    {t : ℝ} (ht : |t| ≤ 1) (det : affineDet l r t ≠ 0) {v : Plane}
    (hv : ‖v‖ ≤ (w : ℝ) / 2 ^ 80) (i : Fin 2) :
    |frameEquiv l r t v i| ≤ (p:ℝ)/2^80 := by
  change |(frameEquiv l r t).toContinuousLinearMap v i| ≤ _
  rw [frameEquiv_forward det]
  fin_cases i
  · change |forward l r t v (0 : Fin 2)| ≤ _
    rw [forward, matrix_zero]
    exact interpolate ht (endpoint_bound ok.leftR hv) (endpoint_bound ok.rightR hv)
  · change |forward l r t v (1 : Fin 2)| ≤ _
    rw [forward, matrix_one]
    exact interpolate ht (endpoint_bound ok.leftZ hv) (endpoint_bound ok.rightZ hv)

end PlasmaLean.Certificates.PositionFrameProjection
