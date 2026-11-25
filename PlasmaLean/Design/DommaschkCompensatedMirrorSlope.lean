/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkHarmonicHorner
public import PlasmaLean.Design.DommaschkMirrorStrengthSlope

/-! # Cancelling the leading radial field in the physical mirror-slope numerator -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkCompensatedMirrorSlope

open DommaschkKam DommaschkKam.DkPoly DommaschkHarmonicHorner DommaschkMirrorStrengthSlope

/-- Angular derivative for the physical azimuth, with doubled fundamental angle. -/
def angular (p : SP) : SP :=
  scale 2 (merge (mul [⟨1,0,0,1,0⟩] (dS p)) (scale (-1) (mul [⟨1,0,0,0,1⟩] (dC p))))

/-- Numerator of the radial derivative of the toroidal component D/R⁷. -/
def radial : SP := merge (mul Rl (dU dD)) (scale (-7) dD)

private theorem scale_real (l : ℚ) (p : SP) (u z c s : ℝ) :
    evR u z c s (scale l p) = (l : ℝ) * evR u z c s p := by
  apply Complex.ofReal_inj.mp
  simp only [Complex.ofReal_mul, Complex.ofReal_ratCast, ← ev_ofReal, ev_scale]
  rfl

theorem angular_eval (p : SP) (u z c s : ℝ) :
    evR u z c s (angular p) = 2 * (c * evR u z c s (dS p) - s * evR u z c s (dC p)) := by
  simp only [angular, scale_real, real_merge, real_mul]
  norm_num [evR]
  ring

theorem radial_eval (R z c s : ℝ) :
    evR (R-dkR0) z c s radial =
      R * evR (R-dkR0) z c s (dU dD) - 7 * evR (R-dkR0) z c s dD := by
  rw [radial,real_merge,real_mul,scale_real]
  have radius : evR (R-dkR0) z c s Rl = R := by norm_num [evR,Rl,dkR0,R0q]
  rw [radius]
  norm_num
  ring

/-- Factoring the radial quotient before bounding avoids subtracting independent large
intervals for the derivative of the leading radial power. -/
theorem numerator_eq (R z c s : ℝ) :
    let v := evR (R-dkR0) z c s
    let d := v dD
    let n := v dnR
    let h := v dnZ
    let m (p : SP) := n * v (dU p) + h * v (dZ p) + d * v (angular p)
    let t := n * v radial + R * (h * v (dZ dD) + d * v (angular dD))
    numerator R z c s =
      2 * (R*R*d*t + R * (n * m dnR + h * m dnZ)) - 16 * (n * (n*n + h*h)) := by
  dsimp only
  simp only [numerator, material, radial_eval, angular_eval]
  ring

end PlasmaLean.Design.DommaschkCompensatedMirrorSlope
