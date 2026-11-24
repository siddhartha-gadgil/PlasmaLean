/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorStrengthSlope
public import Mathlib.Analysis.Calculus.MeanValue

/-! # A spatial mean-value enclosure for physical squared strength at one azimuth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCenteredStrength
open DommaschkKam DkPoly DommaschkBounceField Certificates.RadialSlabs Contract Set

/-- The coordinate segment between the reference point and a tube point. -/
def segment (a b t : ℝ) := a + t * (b - a)

theorem segment_derivative (a b t : ℝ) :
    HasDerivAt (segment a b) (b - a) t := by
  unfold segment
  convert (hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const (b - a)) using 1
  · rfl
  · ring

theorem segment_distance {a b e t : ℝ} (h : |b - a| ≤ e) (ht : t ∈ Icc 0 1) :
    |segment a b t - a| ≤ e := by
  simpa only [segment,add_sub_cancel_left,abs_mul,abs_of_nonneg ht.1] using
    (mul_le_of_le_one_left (abs_nonneg (b - a)) ht.2).trans h

/-- For a two-dimensional scalar observable, a sup bound for each partial derivative
controls the displacement to any point in the rectangle around the reference. -/
theorem mean_value {F : ℝ → ℝ → ℝ} {gx gz : ℝ → ℝ → ℝ} {a b x y e k l : ℝ}
    (hr : |x - a| ≤ e) (hz : |y - b| ≤ e)
    (along : ∀ t ∈ Icc (0 : ℝ) 1, let r := segment a x t; let z := segment b y t
      HasDerivAt (fun s => F (segment a x s) (segment b y s))
        (gx r z * (x - a) + gz r z * (y - b)) t)
    (bounds : ∀ r z, |r - a| ≤ e → |z - b| ≤ e → |gx r z| ≤ k ∧ |gz r z| ≤ l) :
    |F x y - F a b| ≤ e*(k+l) := by
  have T := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (along t ht).hasDerivWithinAt)
    (C := e*(k+l)) (fun t ht => by
      obtain ⟨p,q⟩ := bounds _ _ (segment_distance hr ⟨ht.1,ht.2.le⟩)
        (segment_distance hz ⟨ht.1,ht.2.le⟩)
      rw [Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul,abs_mul,mul_add]
        exact add_le_add
          (by simpa [mul_comm] using mul_le_mul p hr (abs_nonneg _) ((abs_nonneg _).trans p))
          (by simpa [mul_comm] using mul_le_mul q hz (abs_nonneg _) ((abs_nonneg _).trans q))))
  simpa [segment, Real.norm_eq_abs] using T

def physicalSq (φ r z : ℝ) := ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint r φ z)‖ ^ 2

/-- The compensated numerator of the radial partial derivative, divided by its denominator. -/
def radial (h φ r z : ℝ) : ℝ :=
  let p := fun a => atPoint a r φ z
  let q := (p dnR)^2+(p dnZ)^2
  let dq := 2*(p dnR*p (dU dnR)+p dnZ*p (dU dnZ))
  (2*r^2*p dD*(r*(p (dU dD)-7*h*r^6)-7*(p dD-h*r^7))+r*dq-16*q)/r^17

/-- The vertical partial derivative at fixed radius and angle. -/
def vertical (φ r z : ℝ) : ℝ :=
  let p := fun a => atPoint a r φ z
  let dq := 2*(p dnR*p (dZ dnR)+p dnZ*p (dZ dnZ))
  (2*r^2*p dD*p (dZ dD)+dq)/r^16

private theorem fixed_angle (p : SP) {R Z : ℝ → ℝ} {φ t vr vz : ℝ}
    (hr : HasDerivAt R vr t) (hz : HasDerivAt Z vz t) :
    HasDerivAt (fun s => atPoint p (R s) φ (Z s))
      (atPoint (dU p) (R t) φ (Z t)*vr + atPoint (dZ p) (R t) φ (Z t)*vz) t := by
  simpa only [atPoint, mul_zero, add_zero] using DommaschkMirrorStrengthSlope.sparse_path p
    (hr.sub_const dkR0) hz (hasDerivAt_const t (Real.cos (2*φ)))
    (hasDerivAt_const t (Real.sin (2*φ)))

theorem physical_derivative {R Z : ℝ → ℝ} {φ t vr vz : ℝ} (h : ℝ)
    (hr : HasDerivAt R vr t) (hz : HasDerivAt Z vz t) (rp : 0 < R t)
    (dp : 0 < atPoint dD (R t) φ (Z t)) :
    HasDerivAt (fun s => physicalSq φ (R s) (Z s))
      (radial h φ (R t) (Z t)*vr + vertical φ (R t) (Z t)*vz) t := by
  have hd := (observable_derivatives h hr (fixed_angle (φ := φ) dD hr hz)
    (fixed_angle (φ := φ) dnR hr hz) (fixed_angle (φ := φ) dnZ hr hz) rp dp).1
  apply HasDerivAt.congr_of_eventuallyEq (f := fun s => strengthSq (R s)
    (atPoint dD (R s) φ (Z s)) (atPoint dnR (R s) φ (Z s)) (atPoint dnZ (R s) φ (Z s)))
  · convert hd using 1
    unfold radial vertical strengthNumerator
    field_simp [rp.ne']
  · filter_upwards [hr.continuousAt.eventually (lt_mem_nhds rp)] with s hs
    exact norm_sq_eq_strengthSq hs _ _

/-- The QA2R quantity enclosed about the spatial centre is the squared magnitude
of the actual field. All section angles and both positions use the same clock. -/
theorem centered {h φ a b x y e k l : ℝ} (hr : |x - a| ≤ e) (hz : |y - b| ≤ e)
    (jet : ∀ r z, |r - a| ≤ e → |z - b| ≤ e →
      0 < r ∧ 0 < atPoint dD r φ z ∧ |radial h φ r z| ≤ k ∧ |vertical φ r z| ≤ l) :
    |physicalSq φ x y - physicalSq φ a b| ≤ e*(k+l) := by
  apply mean_value hr hz
  · intro t ht
    obtain ⟨rp,dp,_⟩ := jet _ _ (segment_distance hr ht) (segment_distance hz ht)
    exact physical_derivative h (segment_derivative _ _ _) (segment_derivative _ _ _) rp dp
  · exact fun r z u v => (jet r z u v).2.2

/-- The numerator used to compare the two reference strengths on their common clock. -/
theorem scaled_sq {r : ℝ} (hp : 0 < r) (φ z : ℝ) :
    r^16 * physicalSq φ r z = (r * atPoint dD r φ z)^2 +
      (atPoint dnR r φ z)^2 + (atPoint dnZ r φ z)^2 := by
  unfold physicalSq
  rw [norm_sq_eq_strengthSq hp]
  unfold strengthSq
  field_simp [hp.ne']
  ring

/-- Two centered estimates and one common-time cross product compare the actual
strengths while retaining their correlation in the toroidal angle. -/
theorem compare {f g a b e E p P margin : ℝ} (hp : 0 < p) (hP : 0 < P)
    (x : |f - a| ≤ e) (y : |g - b| ≤ E)
    (gap : 0 ≤ (p * a) * P - (P * b) * p - (margin + e + E) * (p * P)) :
    margin ≤ f - g := by
  have d : 0 ≤ ((a-b)-(margin+e+E))*(p*P) := by
    convert gap using 1
    ring
  have z := nonneg_of_mul_nonneg_left d (mul_pos hp hP)
  linarith only [z,(abs_le.mp x).1,(abs_le.mp y).2]

end PlasmaLean.Design.DommaschkCenteredStrength
