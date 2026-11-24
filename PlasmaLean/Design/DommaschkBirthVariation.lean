/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorStrengthSlope
public import PlasmaLean.Design.DommaschkFrameLaunch
public import PlasmaLean.Design.DommaschkPhysicalActionPanel

/-! # Radial differentiation of the physical interpolated birth at fixed azimuth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBirthVariation

open DommaschkMirrorLaunch DommaschkKam DommaschkKamC KamNewton DkPoly
open Theory.KAM WEll1Z2 DommaschkBounceField Certificates.RadialSlabs
open DommaschkPhysicalActionPanel Contract

/-- Initial condition for the radial variational equation at any birth azimuth. -/
def tangent (uC zC uA zA : FA) (φ : ℝ) : State :=
  ![RofC uA 0 φ - RofC uC 0 φ, Zof zA 0 φ - Zof zC 0 φ]

private theorem blend_derivative (c a u : ℝ) :
    HasDerivAt (fun x => blend x c a) (a-c) u := by
  convert (hasDerivAt_const u c).add ((hasDerivAt_id u).mul_const (a-c)) using 1
  · ext x
    simp [blend]
    ring
  · simp

theorem birth_derivative (uC zC uA zA : FA) (φ u : ℝ) :
    HasDerivAt (fun s => birth uC zC uA zA s φ) (tangent uC zC uA zA φ) u := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i <;> exact blend_derivative _ _ _

/-- Pilot birth coordinates and the two components of its actual tangent. -/
theorem geometry {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A
      DommaschkKamA.z₀A (1 / 10 ^ 12)) :
    let b := birth uC zC uA zA (47/100) 0
    let v := tangent uC zC uA zA 0
    b 0 ∈ Set.Icc (99548672/10^8) (99548675/10^8) ∧ |b 1| ≤ 1/10^12 ∧
      v 0 ∈ Set.Icc (1045982/10^8) (1045983/10^8) ∧ |v 1| ≤ 2/10^12 := by
  obtain ⟨c,zc⟩ := launch_error hc ha false (u := 0) ⟨by norm_num, by norm_num⟩
  obtain ⟨a,za⟩ := launch_error hc ha false (u := 1) ⟨by norm_num, by norm_num⟩
  obtain ⟨b,zb⟩ := launch_error hc ha false (u := 47/100) ⟨by norm_num, by norm_num⟩
  simp only [seedRadius, moment, signAt, Bool.false_eq_true, ↓reduceIte, momentCRZero,
    momentARZero, azimuth, blend, abs_le] at c zc a za b zb
  simp only [birth, tangent, blend, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, abs_le, Set.mem_Icc]
  exact ⟨⟨by linarith only [b.1], by linarith only [b.2]⟩, zb,
    ⟨by linarith only [a.1,c.2], by linarith only [a.2,c.1]⟩,
    ⟨by linarith only [za.1,zc.2], by linarith only [za.2,zc.1]⟩⟩

def fieldStrength (R φ z : ℝ) : ℝ :=
  ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖

private theorem spatial_path (p : SP) {R Z : ℝ → ℝ} {φ t vr vz : ℝ}
    (hr : HasDerivAt R vr t) (hz : HasDerivAt Z vz t) :
    HasDerivAt (fun a => atPoint p (R a) φ (Z a))
      (atPoint (dU p) (R t) φ (Z t) * vr + atPoint (dZ p) (R t) φ (Z t) * vz) t := by
  simpa only [atPoint, mul_zero, add_zero] using DommaschkMirrorStrengthSlope.sparse_path p
    (hr.sub_const dkR0) hz (hasDerivAt_const t (Real.cos (2*φ)))
    (hasDerivAt_const t (Real.sin (2*φ)))

/-- Algebraic tests on the field jet along any fixed-angle spatial variation. -/
def NumeratorBounds (R φ z vr vz : ℝ) : Prop :=
  let p := fun a => atPoint a R φ z
  let q := (p dnR)^2 + (p dnZ)^2
  let qr := 2*(p dnR * p (dU dnR) + p dnZ * p (dU dnZ))
  let qz := 2*(p dnR * p (dZ dnR) + p dnZ * p (dZ dnZ))
  0 < p dD ∧ DommaschkMirrorEndpointSign.gap R (3/2) (p dD) (p dnR) (p dnZ) < 0 ∧
    strengthNumerator R (p dD) q (p (dU dD)) (p (dZ dD)) qr qz 0 vr vz ≤ -(1/48) ∧
    0 < densityNumerator R (p dD) q (p (dU dD)) (p (dZ dD)) qr qz vr vz

private theorem root_deriv {g G : ℝ → ℝ} {t a : ℝ} (h : HasDerivAt G a t)
    (hpos : 0 < g t) (same : ∀ᶠ s in nhds t, 0 ≤ g s ∧ (g s) ^ 2 = G s) :
    HasDerivAt g (a / (2 * g t)) t := by
  have point := same.self_of_nhds
  have pos : 0 < G t := point.2 ▸ sq_pos_of_pos hpos
  have root := h.sqrt pos.ne'
  rw [← point.2,Real.sqrt_sq point.1] at root
  apply root.congr_of_eventuallyEq
  filter_upwards [same] with s hs
  rw [← hs.2,Real.sqrt_sq hs.1]

/-- Bounds on the actual derivatives at a birth, with no flow-time variation assumed. -/
theorem observable_slopes {R Z : ℝ → ℝ} {t φ vr vz : ℝ}
    (hr : HasDerivAt R vr t) (hz : HasDerivAt Z vz t) (rpos : 0 < R t) (rle : R t ≤ 1)
    (bound : NumeratorBounds (R t) φ (Z t) vr vz) :
    deriv (fun a => fieldStrength (R a) φ (Z a)) t ≤ -(1/144) ∧
      0 < deriv (fun a => arcDensity (R a) φ (Z a)) t ∧
      -(arcDensity (R t) φ (Z t)/32) ≤ deriv (fun a => arcDensity (R a) φ (Z a)) t := by
  obtain ⟨den,gap,small,big⟩ := bound
  have hd := spatial_path (φ := φ) dD hr hz
  obtain ⟨f,w⟩ := observable_derivatives 0 hr hd (spatial_path dnR hr hz)
    (spatial_path dnZ hr hz) rpos den
  have nearR := hr.continuousAt.eventually (lt_mem_nhds rpos)
  have nearD := hd.continuousAt.eventually (lt_mem_nhds den)
  have pos {r θ z : ℝ} (hp : 0 < r) (dp : 0 < atPoint dD r θ z) : 0 < fieldStrength r θ z := by
    have sqv := norm_sq_eq_strengthSq hp θ z
    unfold Certificates.RadialSlabs.strengthSq at sqv
    have A := div_pos (sq_pos_of_pos dp) (pow_pos hp 14)
    have B := div_nonneg (add_nonneg (sq_nonneg (atPoint dnR r θ z))
      (sq_nonneg (atPoint dnZ r θ z))) (pow_nonneg hp.le 16)
    unfold fieldStrength
    exact lt_of_le_of_ne (norm_nonneg _) (by intro eq; rw [← eq] at sqv; nlinarith only [sqv,A,B])
  have pw {r θ z : ℝ} (hp : 0 < r) (dp : 0 < atPoint dD r θ z) : 0 < arcDensity r θ z :=
    div_pos (mul_pos hp (pos hp dp)) (toroidal_pos_of_den hp dp)
  have df := root_deriv (g := fun a => fieldStrength (R a) φ (Z a)) f (pos rpos den) (by
    filter_upwards [nearR] with a ha
    exact ⟨norm_nonneg _,norm_sq_eq_strengthSq ha _ _⟩)
  have dw := root_deriv (g := fun a => arcDensity (R a) φ (Z a)) w (pw rpos den) (by
    filter_upwards [nearR,nearD] with a ha da
    exact ⟨(pw ha da).le,arclength_sq_eq_densitySq ha da⟩)
  rw [df.deriv,dw.deriv]
  have mag : fieldStrength (R t) φ (Z t) < 3/2 := by
    rw [DommaschkMirrorEndpointSign.gap_eq rpos] at gap
    have h := Right.neg_of_mul_neg_right gap (pow_nonneg rpos.le 16)
    change (fieldStrength (R t) φ (Z t))^2 - (3/2)^2 < 0 at h
    nlinarith only [h]
  have W := div_pos (div_pos big (pow_pos den 3))
    (mul_pos (by norm_num : (0 : ℝ) < 2) (pw rpos den))
  refine ⟨?_, W, le_trans (by linarith only [pw rpos den]) W.le⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) (pos rpos den))).mpr
  apply (div_le_iff₀ (pow_pos rpos 17)).mpr
  have one := pow_le_one₀ rpos.le rle (n := 17)
  have cap := mul_le_of_le_one_right (pos rpos den).le one
  linarith only [small,mag,cap]

end PlasmaLean.Design.DommaschkBirthVariation
