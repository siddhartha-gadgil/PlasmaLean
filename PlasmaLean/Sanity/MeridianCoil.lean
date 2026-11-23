/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.FilamentVacuum
public import PlasmaLean.Theory.Fields.FormConvexRegion
public import PlasmaLean.Theory.Geometry.PlacedCircle

/-!
# A coil whose field is vacuum throughout a meridian half-space

If the full circular filament lies on the other side of the meridian plane, its
Biot–Savart field is vacuum on the open half-space. The centre and radius supply
a sufficient clearance test for every orientation of the coil.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.MeridianCoil

open PlasmaLean.Fields PlasmaLean.Forms PlasmaLean.Geometry PlasmaLean.Vacuum

/-- A radius bound separates every point of the placed filament from the half-space
at toroidal angle zero. Equality of centre clearance and radius is enough because
the half-space is open. -/
theorem placedCircle_outside_meridian_zero (Q : Space ≃ₗᵢ[ℝ] Space) {center : Space} {R : ℝ}
    (h : center 0 + |R| ≤ 0) (t : ℝ) : placedCircle Q center R t ∉ meridianHalfSpace 0 := by
  have hc := PiLp.norm_apply_le (placedCircle Q center R t - center) (0 : Fin 3)
  rw [placedCircle_radius] at hc
  have hdiff : |placedCircle Q center R t 0 - center 0| ≤ |R| := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hc
  have hle := (abs_le.mp hdiff).2
  intro hx
  have hpos : 0 < placedCircle Q center R t 0 := by simpa [mem_meridianHalfSpace] using hx
  linarith

/-- A closed circular filament with the stated clearance generates a vacuum field
on the entire open half-space, for any current. -/
theorem placedCircle_vacuum_meridian_zero (Q : Space ≃ₗᵢ[ℝ] Space) {center : Space} {R : ℝ}
    (h : center 0 + |R| ≤ 0) (μ₀ I : ℝ) :
    VacuumField (meridianHalfSpace 0)
      (filamentField μ₀ I (placedCircle Q center R) 0 (2 * Real.pi)) := by
  obtain ⟨hd, hc⟩ := placedCircle_C1 Q center R
  apply PlasmaLean.Sanity.filamentField_vacuumField' _ _ _ _ _ (meridianHalfSpace 0).isOpen
    (fun t _ => hd t) hc.continuousOn
  · intro x hx t _ he
    exact placedCircle_outside_meridian_zero Q h t (sub_eq_zero.mp he ▸ hx)
  · simpa using ((placedCircle_periodic Q center R) 0).symm

/-- Explicit positive-radius example with unit permeability and unit filament current.
The centre is at (−2,0,0) and the whole unit circle lies at x ≤ −1. -/
theorem unitCoil_vacuum_meridian_zero :
    VacuumField (meridianHalfSpace 0) (filamentField 1 1
      (placedCircle (LinearIsometryEquiv.refl ℝ Space) (WithLp.toLp 2 ![-2, 0, 0]) 1)
      0 (2 * Real.pi)) := by
  apply placedCircle_vacuum_meridian_zero
  change (-2 : ℝ) + |1| ≤ 0
  norm_num

end PlasmaLean.Sanity.MeridianCoil
