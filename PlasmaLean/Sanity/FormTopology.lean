/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormTopology
public import PlasmaLean.Sanity.CurvatureObstruction
public import PlasmaLean.Sanity.Forms

/-!
# Sanity checks for the bridge to manifold forms (`Theory/Fields/FormTopology`)

* Rejected fixture for potentials: the field of a straight wire, `B = e_z × x / (x² + y²)`, is a
  vacuum field on the complement of the axis (`wireField_vacuum`) and is **not** a gradient
  there (`wireField_no_potential`): a potential would increase strictly around the unit circle,
  which is a closed field line.
* Topological consequence through the bridge: the complement of a line in `ℝ³` is not simply
  connected (`wireRegion_not_simplyConnected`).
* Accepted fixture: on all of `ℝ³`, which is simply connected, the hyperbolic vacuum field has a
  potential by the same theorem (`hyperbolic_scalarPotential_top`).
* Bridge checks: the bridge preserves closedness for the wire form (`wire_closed_onOpens`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormTopology

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-- The complement of the wire axis, as an open subset of `ℝ³`. -/
def wireOpens : Opens Space := ⟨wireRegion, isOpen_wireRegion⟩

/-- The unit circle lies in the wire region. -/
theorem unitCircle_mem (s : ℝ) : unitCircle s ∈ wireRegion := by
  change 0 < wireR2 (unitCircle s)
  rw [wireR2_unitCircle]
  exact one_pos

/-- The unit circle closes up. -/
theorem unitCircle_two_pi : unitCircle (2 * Real.pi) = unitCircle 0 := by
  simp [unitCircle]

/-- **The wire field has no potential on the complement of its axis.** -/
theorem wireField_no_potential :
    ¬ ∃ φ : Space → ℝ, DifferentiableOn ℝ φ wireRegion ∧
      ∀ x ∈ wireRegion, wireField x = gradient φ x := by
  rintro ⟨φ, hφ, hgrad⟩
  have hd (s : ℝ) : HasDerivAt (fun t => φ (unitCircle t))
      (⟪wireField (unitCircle s), wireField (unitCircle s)⟫) s := by
    have hφs : DifferentiableAt ℝ φ (unitCircle s) :=
      (hφ _ (unitCircle_mem s)).differentiableAt (isOpen_wireRegion.mem_nhds (unitCircle_mem s))
    have h := hφs.hasFDerivAt.comp_hasDerivAt s (unitCircle_fieldLine s)
    have e : fderiv ℝ φ (unitCircle s) (wireField (unitCircle s)) =
        ⟪wireField (unitCircle s), wireField (unitCircle s)⟫ := by
      rw [hgrad _ (unitCircle_mem s), inner_gradient_left]
    rw [← e]
    exact h
  have hmono : StrictMono (fun t => φ (unitCircle t)) :=
    strictMono_of_hasDerivAt_pos hd fun s =>
      real_inner_self_pos.2 (wireField_unitCircle_ne_zero s)
  have hlt := hmono (show (0 : ℝ) < 2 * Real.pi by positivity)
  simp only [unitCircle_two_pi] at hlt
  exact lt_irrefl _ hlt

/-- **The complement of a line in `ℝ³` is not simply connected**, proved from a magnetic field:
the wire field is a vacuum field there with no potential. -/
theorem wireRegion_not_simplyConnected : ¬ SimplyConnectedSpace wireOpens :=
  not_simplyConnected_of_no_potential (U := wireOpens) wireField_vacuum wireField_no_potential

/-- Bridge check: the 1-form `B♭` of the wire field is closed as a form on the manifold
`wireOpens`. -/
theorem wire_closed_onOpens :
    mextDeriv (onOpens wireOpens fun y => flat (wireField y)) = 0 := by
  rw [mextDeriv_onOpens_eq_zero_iff]
  intro x hx
  rw [extDeriv_flat, wireField_vacuum.curl_eq_zero x hx, map_zero]

/-- Bridge check: the same form is `C²` on the manifold. -/
theorem wire_isSmoothForm_onOpens :
    IsSmoothForm 𝓘(ℝ, Space) 2 (onOpens wireOpens fun y => flat (wireField y)) := by
  rw [isSmoothForm_onOpens_iff]
  exact flat.toContinuousLinearEquiv.contDiff.comp_contDiffOn wireField_vacuum.contDiffOn

end PlasmaLean.Sanity.FormTopology
