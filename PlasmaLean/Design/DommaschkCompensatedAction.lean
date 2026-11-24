/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalActionPanel

/-! # Cancellation in the radial coefficients of the physical action gap -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkCompensatedAction
open DommaschkKam DommaschkKam.DkPoly DommaschkFirstMirrorLaunchSign

/-- Subtract the dominant radial term in the coefficients before any spatial
enclosure. Equal powers of the cylindrical displacement are combined exactly. -/
def shiftedD (height : ℚ) : SP := merge dD (scale (-height) (RpowL 7))

theorem eval_shiftedD (k : ℚ) (u z c s : ℝ) :
    evR u z c s (shiftedD k) = evR u z c s dD - (k : ℝ) * (dkR0 + u) ^ 7 := by
  let x : Fin 6 → ℂ := ![(u : ℂ), z, c, s, 0, 0]
  have a := ev_ofReal u z c s (shiftedD k)
  have b := ev_ofReal u z c s dD
  change ev x (shiftedD k) = _ at a
  change ev x dD = _ at b
  rw [shiftedD, ev_merge, ev_scale, ev_RpowL, b] at a
  apply Complex.ofReal_inj.mp
  unfold shiftedD
  rw [← a]
  simp [x, dkR0, R0q, sub_eq_add_neg]

/-- A single compensated gap suffices at every parallel-speed threshold. -/
theorem gap_from_shift (k : ℚ) {R u z c s h : ℝ} (hr : u = R - dkR0) :
    DommaschkMirrorEndpointSign.gap R h (evR u z c s dD)
      (evR u z c s dnR) (evR u z c s dnZ) =
    R ^ 2 * evR u z c s (shiftedD k) * (2 * evR u z c s dD - evR u z c s (shiftedD k)) +
      (evR u z c s dnR) ^ 2 + (evR u z c s dnZ) ^ 2 +
      R ^ 16 * ((k : ℝ) ^ 2 - h ^ 2) := by
  rw [eval_shiftedD, show dkR0 + u = R by rw [hr]; ring]
  unfold DommaschkMirrorEndpointSign.gap
  ring

end PlasmaLean.Design.DommaschkCompensatedAction
