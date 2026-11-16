/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Forms
public import PlasmaLean.Sanity.Vacuum
public import PlasmaLean.Sanity.AuditVacuum
public import PlasmaLean.Sanity.Equilibrium
public import PlasmaLean.Sanity.AuditEquilibrium

/-!
# Sanity checks for the differential-form kernel `Kernel/Forms`

The statements are made afresh in form language. Each proof is transported from the
sanity check of the same fact in vector language (`Sanity/Vacuum`, `Sanity/AuditVacuum`,
`Sanity/Equilibrium`, `Sanity/AuditEquilibrium`) through the equivalences `flux`,
`flat`, `density`, `hodge` and the theorems `vacuumForm_flux_iff`,
`formForceBalance_iff`.

1. **Equivalences.** Values on the Cartesian basis (`dx`, `dy ∧ dz`, the volume form),
   and the round trips.
2. **Vacuum forms.** Accepted: the zero form, constant forms, the flux form of the
   hyperbolic field (which is also `⋆dp` for the harmonic polynomial `p`). Rejected:
   the flux form of the rotation field (not co-closed) and of the identity field (not
   closed). Audit V-1 carries over: every 2-form is a vacuum form on the empty region.
3. **Force balance.** Accepted: uniform, parallel (`ι_B ω_B = 0`), the pinch
   orientation. Rejected: perpendicular data with `dp = 0`, the reversed sign
   convention. Audit E-1 carries over: `dp := ι_B ω_J` always balances.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.Forms

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Sanity PlasmaLean.Sanity.Audit
  PlasmaLean.Fields Matrix

/-! ### The equivalences on the Cartesian basis -/

/-- `(e₀)♭ = dx`: it evaluates to the first component. -/
theorem flat_coordVec_apply (w : Euclid3) : flat (coordVec 0) ![w] = w 0 := by
  simp [coordVec, EuclideanSpace.inner_single_left]

/-- `ι_{e₀} vol = dy ∧ dz`: on `(e₁, e₂)` it is `1`. -/
theorem flux_coordVec : flux (coordVec 0) ![coordVec 1, coordVec 2] = 1 := by
  simp [flux_apply, volForm_vec]

/-- The volume form is `1` on the standard frame. -/
theorem volForm_frame : volForm ![coordVec 0, coordVec 1, coordVec 2] = 1 := by
  simp [volForm_vec]

/-- The volume form is `-1` on the frame with the opposite orientation. -/
theorem volForm_frame_swap : volForm ![coordVec 1, coordVec 0, coordVec 2] = -1 := by
  simp [volForm_vec]

/-- Round trip: a 2-form is the flux form of its vector. -/
theorem flux_roundtrip (ω : Form 2) : flux (flux.symm ω) = ω := flux.apply_symm_apply ω

/-- Round trip: a vector is the vector of its flux form. -/
theorem flux_symm_roundtrip (v : Euclid3) : flux.symm (flux v) = v := flux.symm_apply_apply v

/-- Round trip for fields of forms. -/
theorem fluxField_roundtrip (ω : Euclid3 → Form 2) : fluxField (fluxField.symm ω) = ω :=
  fluxField.apply_symm_apply ω

/-- The Hodge star sends `dy ∧ dz` to `dx`. -/
theorem hodge_dydz : hodge (flux (coordVec 0)) = flat (coordVec 0) := hodge_flux _

/-! ### Vacuum forms: accepted fixtures -/

/-- Degenerate case: the zero 2-form is a vacuum form on every open region.
Transported from `zero_vacuum`. -/
theorem zero_vacuumForm {Ω : Set Euclid3} (hΩ : IsOpen Ω) :
    VacuumForm Ω (fun _ => (0 : Form 2)) := by
  have h := vacuumForm_flux_iff.2 (zero_vacuum hΩ)
  have e : fluxField (fun _ => (0 : Euclid3)) = fun _ => (0 : Form 2) := by
    funext x; simp
  rwa [e] at h

/-- A constant 2-form is a vacuum form on every open region. Transported from
`const_vacuum`. -/
theorem const_vacuumForm {Ω : Set Euclid3} (hΩ : IsOpen Ω) (ω₀ : Form 2) :
    VacuumForm Ω (fun _ => ω₀) := by
  have h := vacuumForm_flux_iff.2 (const_vacuum hΩ (flux.symm ω₀))
  have e : fluxField (fun _ => flux.symm ω₀) = fun _ => ω₀ := by
    funext x; simp
  rwa [e] at h

/-- The flux form `x dy∧dz + y dz∧dx - 2z dx∧dy` of the hyperbolic field is a vacuum
form on all of space. Transported from `hyperbolic_gradient_vacuum`. -/
theorem hyperbolic_vacuumForm :
    VacuumForm Set.univ (fluxField fun y => hyperbolicField y) :=
  vacuumForm_flux_iff.2 hyperbolic_gradient_vacuum

/-- The same form is `⋆dp` for the harmonic polynomial `p = (x² + y²)/2 - z²`: the
Hodge star of the flux form is the differential of the potential. Transported from
`fderiv_hyperbolicPotential`. -/
theorem hodge_hyperbolic (y : Euclid3) :
    hodge (fluxField (fun y => hyperbolicField y) y) = formGrad hyperbolicPotential y := by
  rw [fluxField_apply, hodge_flux]
  ext w
  rw [flat_apply, formGrad_apply, fderiv_hyperbolicPotential]

/-! ### Vacuum forms: rejected fixtures -/

/-- The flux form of the rotation field `(-y, x, 0)` is not a vacuum form on any
nonempty region (it is not co-closed). Transported from `rotationField_not_vacuum`. -/
theorem rotation_not_vacuumForm {Ω : Set Euclid3} (hne : Ω.Nonempty) :
    ¬ VacuumForm Ω (fluxField fun y => rotationField y) := fun h =>
  rotationField_not_vacuum hne (vacuumForm_flux_iff.1 h)

/-- It is, however, closed: `d(ι_B vol) = 0`. Transported from `fieldDiv_rotationField`. -/
theorem rotation_closed (x : Euclid3) :
    extDeriv (fluxField fun y => rotationField y) x = 0 := by
  rw [show fluxField (fun y => rotationField y) = fun y => flux (rotationField y) from rfl,
    extDeriv_flux, fieldDiv_rotationField, map_zero]

/-- The flux form `x dy∧dz + y dz∧dx + z dx∧dy` of the identity field has
`dω = 3 vol`. Transported from `fieldDiv_id`. -/
theorem extDeriv_flux_id (x : Euclid3) :
    extDeriv (fun y : Euclid3 => flux y) x = density 3 := by
  rw [extDeriv_flux, fieldDiv_id]

/-- So it is not a vacuum form on any nonempty region (it is not closed), although
`⋆ω = d(|x|²/2)` is closed. Transported from `id_not_vacuum`. -/
theorem id_not_vacuumForm {Ω : Set Euclid3} (hne : Ω.Nonempty) :
    ¬ VacuumForm Ω (fluxField fun y => y) := fun h =>
  id_not_vacuum hne (vacuumForm_flux_iff.1 h)

/-- **Regression (finding V-1, vacuity hazard) in form language.** Every 2-form is a
vacuum form on the empty region. Transported from `vacuumField_empty`. -/
theorem vacuumForm_empty (ω : Euclid3 → Form 2) : VacuumForm ∅ ω :=
  vacuumField_fluxSymm_iff.1 (vacuumField_empty _)

/-- Scaling a vacuum form by a constant gives a vacuum form. Transported from
`VacuumField.const_smul`. -/
theorem vacuumForm_const_smul {Ω : Set Euclid3} {ω : Euclid3 → Form 2}
    (h : VacuumForm Ω ω) (a : ℝ) : VacuumForm Ω (fun x => a • ω x) := by
  have h1 := Audit.VacuumField.const_smul (vacuumField_fluxSymm_iff.2 h) a
  have h2 := vacuumForm_flux_iff.2 h1
  have e : fluxField (fun x => a • fluxField.symm ω x) = fun x => a • ω x := by
    funext x; simp
  rwa [e] at h2

/-! ### Force balance -/

/-- A uniform field with zero current form and zero pressure differential is in
balance. Transported from `uniformBalance`. -/
theorem uniformFormBalance (ωB : Form 2) : FormForceBalance ωB 0 0 := by
  have h := formForceBalance_iff.2 (uniformBalance (vec.symm (flux.symm ωB)))
  simpa using h

/-- Parallel field and current: `ι_B ω_B = 0`, a force-free witness. Transported from
`parallelBalance`. -/
theorem parallelFormBalance (ωB : Form 2) : FormForceBalance ωB ωB 0 := by
  have h := formForceBalance_iff.2 (parallelBalance (vec.symm (flux.symm ωB)))
  simpa using h

/-- **Counterexample.** `ω_J = dy∧dz` (current along `x`) and `ω_B = dx∧dy` (field
along `z`) do not balance `dp = 0`. Transported from `forceBalance_rejects_perp`. -/
theorem formForceBalance_rejects_perp :
    ¬ FormForceBalance (flux (vec ![0, 0, 1])) (flux (vec ![1, 0, 0])) 0 := fun h =>
  forceBalance_rejects_perp (formForceBalance_iff.1 (by simpa using h))

/-- **Orientation check (pinch force).** Axial current `ω_J = dx∧dy`, azimuthal field
`ω_B = dz∧dx` at `e_x`: `ι_B ω_J = -dx`, the pressure decreases outward. Transported
from `pinch_force_inward`. -/
theorem formPinch_force_inward :
    FormForceBalance (flux (vec ![0, 1, 0])) (flux (vec ![0, 0, 1])) (flat (vec ![-1, 0, 0])) :=
  formForceBalance_iff.2 pinch_force_inward

/-- **Orientation check.** The reversed convention `ι_J ω_B = dp` is rejected.
Transported from `forceBalance_rejects_reversed`. -/
theorem formForceBalance_rejects_reversed :
    ¬ FormForceBalance (flux (vec ![0, 1, 0])) (flux (vec ![0, 0, 1]))
      (flat (vec ![1, 0, 0])) := fun h =>
  forceBalance_rejects_reversed (formForceBalance_iff.1 h)

/-- **Regression (finding E-1, vacuity hazard) in form language.** Every pair of flux
forms balances the datum `dp := ι_B ω_J`: the law carries no physics unless `dp` is
proved to be the differential of a pressure field. Transported from
`forceBalance_of_cross`. -/
theorem formForceBalance_of_interior (ωB ωJ : Form 2) :
    FormForceBalance ωB ωJ (ωJ.curryLeft (flux.symm ωB)) := by
  have h := formForceBalance_iff.2
    (forceBalance_of_cross (vec.symm (flux.symm ωB)) (vec.symm (flux.symm ωJ)))
  have e := curryLeft_flux (vec.symm (flux.symm ωB)) (vec.symm (flux.symm ωJ))
  simp only [LinearEquiv.apply_symm_apply] at h e
  rwa [← e] at h

/-- The field is tangent to the pressure surfaces in the pinch fixture: `dp(B) = 0`
(here `-dx(e_y) = 0`). -/
theorem formPinch_tangency : flat (vec ![-1, 0, 0]) ![vec ![0, 1, 0]] = 0 := by
  have := formPinch_force_inward
  simpa using form_field_tangency (flux (vec ![0, 1, 0])) (flux (vec ![0, 0, 1]))
    (flat (vec ![-1, 0, 0]))

end PlasmaLean.Sanity.Forms
