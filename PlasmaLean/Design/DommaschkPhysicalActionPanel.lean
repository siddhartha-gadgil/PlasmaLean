/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPreMirrorSigns
public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Physical inputs to a mirror-action time panel -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalActionPanel
open Certificates Certificates.TrajectoryTaylorModel DommaschkBounceField DommaschkKam
open DommaschkMirrorTubeCrossing DommaschkMirrorEndpointSign Contract

/-- Arclength density per radian of the oriented physical field line. -/
def arcDensity (R φ z : ℝ) : ℝ :=
  R * ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖ / cylBphi R φ z

theorem arcDensity_reflected {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    arcDensity R (-φ) (-z) = arcDensity R φ z := by
  rw [arcDensity, arcDensity, strength_reflected hR,
    (DommaschkSectionReflection.field_reflect hR φ z).1]

set_option maxRecDepth 8000 in
/-- The norm of the derivative of the actual cylindrical field line equals this density. -/
theorem norm_deriv_eq_density {R z : ℝ → ℝ} {t : ℝ} (hR : 0 < R t)
    (hD : 0 < atPoint dD (R t) t (z t))
    (dr : HasDerivAt R (R t * cylBR (R t) t (z t) / cylBphi (R t) t (z t)) t)
    (dz : HasDerivAt z (R t * cylBz (R t) t (z t) / cylBphi (R t) t (z t)) t) :
    ‖deriv (fun s => cylPoint (R s) s (z s)) t‖ = arcDensity (R t) t (z t) := by
  have hp := toroidal_pos_of_den hR hD
  have geom := Kinetic.MirrorWell.cylindrical_trace_speed
    (DommaschkQA2R.field DommaschkQA2R.candidate) R z 0 t hR
  simp only [zero_add] at geom
  have az : -Real.sin t * (DommaschkQA2R.field DommaschkQA2R.candidate
      (cylPoint (R t) t (z t))) 0 + Real.cos t * (DommaschkQA2R.field DommaschkQA2R.candidate
      (cylPoint (R t) t (z t))) 1 = cylBphi (R t) t (z t) := by simp [cylBphi]
  rw [az] at geom
  unfold cylBR at dr
  obtain ⟨pos, ne, tangent⟩ := geom hp dr dz
  rw [tangent.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos pos]
  rw [Kinetic.GCLittlejohn.bhat, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr ne), mul_one]
  rfl

/-- Lower bound on a Taylor model on a rational closed time panel. -/
theorem lower_on {m : Model} {l r a : ℚ} {t y : ℝ}
    (h : QPoly.checkOn m.poly (m.radius + a) l r [r] = true)
    (ht : t ∈ Set.Icc (l : ℝ) r) (hy : m.Mem t y) : (a : ℝ) ≤ y := by
  have bound := QPoly.checkOn_sound h t ht
  push_cast at bound
  linarith only [bound, (abs_le.mp hy).1]

/-- Enclose all physical times on the panel in an independent, constant dyadic model. -/
theorem box_on {m : Model} {l r : ℚ} {c e : ℤ} {t y : ℝ}
    (lo : QPoly.checkOn m.poly (m.radius + ((c : ℚ) - e) / 2 ^ 80) l r [r] = true)
    (hi : QPoly.checkOn (QPoly.scale (-1) m.poly) (m.radius - ((c : ℚ) + e) / 2 ^ 80)
      l r [r] = true) (ht : t ∈ Set.Icc (l : ℝ) r) (hy : m.Mem t y) (s : ℝ) :
    (ofDyadic 80 [c] e).Mem s y := by
  have bot := lower_on lo ht hy
  have top := QPoly.checkOn_sound hi t ht
  simp only [QPoly.eval_scale, Rat.cast_sub, Rat.cast_add, Rat.cast_neg, Rat.cast_one,
    Rat.cast_intCast, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, neg_one_mul] at top bot
  rw [mem_ofDyadic_iff, abs_le]
  simp only [List.map_cons, List.map_nil, QPoly.eval_cons, QPoly.eval_nil,
    Rat.cast_intCast, mul_zero, add_zero]
  constructor <;> linarith only [bot, top, (abs_le.mp hy).2]

theorem constant_coord {c e : ℤ} {t R : ℝ} (h : (ofDyadic 80 [c] e).Mem t R) :
    |R - (c : ℝ) / 2 ^ 80| ≤ (e : ℝ) / 2 ^ 80 := by
  rw [mem_ofDyadic_iff] at h
  simp only [List.map_cons, List.map_nil, QPoly.eval_cons, QPoly.eval_nil,
    Rat.cast_intCast, mul_zero, add_zero, abs_le] at h
  rw [abs_le]
  constructor <;> linarith only [h.1, h.2]

/-- A rectangular enclosure can discharge the arclength margin using exact rational bounds. -/
theorem density_margin_of_ranges {R D nr nz a r d b c : ℝ}
    (hr : 0 ≤ R) (hr' : R ≤ r) (hd : 0 ≤ d) (hd' : d ≤ D)
    (hb : |nr| ≤ b) (hc : |nz| ≤ c) (hs : r ^ 2 ≤ a ^ 2)
    (checked : b ^ 2 + c ^ 2 ≤ (a ^ 2 - r ^ 2) * d ^ 2) :
    0 ≤ ((a - R) * (a + R)) * D ^ 2 - (nr ^ 2 + nz ^ 2) := by
  apply sub_nonneg.mpr
  rw [show (a - R) * (a + R) = a ^ 2 - R ^ 2 by ring]
  have cx : nr ^ 2 ≤ b ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have cy : nz ^ 2 ≤ c ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hc 2
  have rr := pow_le_pow_left₀ hr hr' 2
  exact ((add_le_add cx cy).trans checked).trans (mul_le_mul (sub_le_sub_left rr _)
    (pow_le_pow_left₀ hd hd' 2) (sq_nonneg _) (sub_nonneg.mpr (rr.trans hs)))

/-- Two polynomial inequalities imply the encoded upper density and squared-speed
columns at the physical point, including the case of a vanishing speed bound. -/
theorem upper_columns {R φ z h a g : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hh : 0 ≤ h - g / 2) (hD : 0 < atPoint dD R φ z)
    (hd : 0 ≤ ((a - R) * (a + R)) * (atPoint dD R φ z) ^ 2 -
      ((atPoint dnR R φ z) ^ 2 + (atPoint dnZ R φ z) ^ 2))
    (hs : 0 ≤ gap R (h - g / 2) (atPoint dD R φ z) (atPoint dnR R φ z)
      (atPoint dnZ R φ z)) :
    arcDensity R φ z ≤ a ∧
    max (2 * (h - ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖)) 0 ≤ g := by
  have hp : 0 < (atPoint dD R φ z) ^ 2 := sq_pos_of_pos hD
  constructor
  · apply (sq_le_sq₀ (div_nonneg (mul_nonneg hR.le (norm_nonneg _))
      (toroidal_pos_of_den hR hD).le) ha).mp
    rw [arclength_sq_eq_densitySq hR hD, RadialSlabs.densitySq]
    apply (le_sub_iff_add_le').mp
    exact (div_le_iff₀ hp).mpr (by nlinarith only [hd])
  · rw [gap_eq hR] at hs
    have diff := (mul_nonneg_iff_of_pos_left (pow_pos hR 16)).mp hs
    have ge := (sq_le_sq₀ hh (norm_nonneg _)).mp (sub_nonneg.mp diff)
    exact max_le (by linarith) hg

end PlasmaLean.Design.DommaschkPhysicalActionPanel
