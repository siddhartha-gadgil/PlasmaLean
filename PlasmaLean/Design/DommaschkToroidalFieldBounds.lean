/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkToroidalEnvelope
public import PlasmaLean.Design.DommaschkSignedTraceDensity
public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign

/-! # Magnitude, arclength density and parallel speed on the entire pilot envelope -/

public section
noncomputable section
namespace PlasmaLean.Design.DommaschkToroidalFieldBounds

open DommaschkKam DommaschkSignedTraceDomain DommaschkMirrorTubeCrossing
open DommaschkPhysicalActionPanel DommaschkFirstMirrorLaunchSign Certificates.PositionFrameSlabs
set_option maxRecDepth 8192

/-- The magnitude dominates the strictly positive toroidal component throughout the box. -/
theorem strength_lower {x : Plane} (φ : ℝ) (region : Region x) : 7 / 8 < strength φ x := by
  have component := DommaschkToroidalEnvelope.cylBphi_lower φ region.1 region.2
  have magnitude := DommaschkKamC.norm_field_sq (x 0) φ (x 1)
  change (strength φ x) ^ 2 = _ at magnitude
  have hp : 0 ≤ strength φ x := norm_nonneg _
  have sq : cylBphi (x 0) φ (x 1) ^ 2 ≤ strength φ x ^ 2 := by
    linarith only [magnitude, sq_nonneg (cylBR (x 0) φ (x 1)), sq_nonneg (cylBz (x 0) φ (x 1))]
  exact component.trans_le (le_of_sq_le_sq sq hp)

/-- At any accessible height, the actual Cartesian arclength density is bounded by
eight sevenths times the height. -/
theorem density_upper {x : Plane} {φ h : ℝ} (region : Region x) (accessible : strength φ x ≤ h) :
    arcDensity (x 0) φ (x 1) ≤ h * (8 / 7) := by
  have component := DommaschkToroidalEnvelope.cylBphi_lower φ region.1 region.2
  have hp := lt_trans (by norm_num : (0 : ℝ) < 7 / 8) component
  have norm : 0 ≤ strength φ x := norm_nonneg _
  have hc := mul_le_of_le_one_left norm region.1.2
  change x 0 * strength φ x / cylBphi (x 0) φ (x 1) ≤ h * (8 / 7)
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ h := hc.trans accessible
    _ = (h * (8 / 7)) * (7 / 8) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left component.le (mul_nonneg (norm.trans accessible)
      (by norm_num))

/-- The normalized clipped parallel speed stays below 61/100 for every admitted height. -/
theorem speed_upper {x : Plane} {φ h : ℝ} (region : Region x) (cap : h ≤ height true) :
    Real.sqrt (2 * (h - strength φ x)) < 61 / 100 := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 61 / 100)).mpr
  have floor := strength_lower φ region
  norm_num [height] at cap
  linarith

end PlasmaLean.Design.DommaschkToroidalFieldBounds
