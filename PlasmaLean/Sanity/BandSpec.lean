/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.BandSpec
public import PlasmaLean.Sanity.TrappedBirthBand

/-!
# Sanity checks for the band form of C2 with fixed inputs

Regressions for the audit findings of 25 November 2026 (AW-H3, AW-M3):

* `dirac_not_admissible`: a point-mass birth law is never an admissible specification, so the
  single-orbit fixture `quadratic_guidingCentreBand` cannot be read as a band-form instance
  (`quadratic_fixture_not_admissible`).
* `mirror_not_meetsBand`: the quadratic-mirror field, which violates the magnetic Gauss law,
  meets no band specification, although it satisfies the unrestricted `GuidingCentreBand`.
* `not_meetsBand_const` (in the contract module): a uniform field has no trapped births.

A positive instance (an admissible specification and a field meeting it) is the open research
target of clause C2 and is not provided here.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Sanity.BandSpec

open PlasmaLean.Contract PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Sanity.TrappedBirthBand
open Set MeasureTheory

/-- A birth law concentrated at one point is not absolutely continuous with respect to volume,
so no specification with it is admissible. -/
theorem dirac_not_admissible (s : BandSpec) (b : GCBirth) (hν : s.ν = Measure.dirac b) :
    ¬ s.Admissible := by
  intro h
  have hvol : (volume : Measure GCBirth) {b} = 0 := by
    apply measure_mono_null (singleton_subset_iff.mpr
      (show b ∈ ({b.1} : Set Space) ×ˢ (univ : Set (ℝ × ℝ)) from ⟨rfl, trivial⟩))
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  have h0 : s.ν {b} = 0 := h.birth_ac hvol
  rw [hν, Measure.dirac_apply_of_mem (mem_singleton b)] at h0
  exact one_ne_zero h0

/-- The data of the single-orbit fixture `quadratic_guidingCentreBand` (Dirac birth law at
`mirrorBirth`), with any axis, horizon, excursion and fraction, is not an admissible
specification. -/
theorem quadratic_fixture_not_admissible (q T d f : ℝ) (axis : ℝ → Space) :
    ¬ BandSpec.Admissible
      { m := 2, q := q, ν := Measure.dirac mirrorBirth, support := {mirrorBirth},
        energy := Icc 1 3, pitch := Icc (1 / 3) (2 / 3), axis := axis, horizon := T,
        excursion := d, minFraction := f } :=
  dirac_not_admissible _ mirrorBirth rfl

/-- The quadratic-mirror field has divergence `2x₀`, which vanishes on no open set, so it meets
no band specification: the Maxwell clause of `MeetsBand` rejects it. -/
theorem mirror_not_meetsBand (s : BandSpec) : ¬ MeetsBand s mirror := by
  intro h
  obtain ⟨b, -, Ω, hΩ, hb, hdiv⟩ := h.exists_birth
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.mp hΩ _ hb
  have h0 := hdiv _ hb
  rw [quadratic_fieldDiv] at h0
  set y : Space := b.1 + (ε / 2) • coordVec 0
  have hy : y ∈ Ω := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, show y - b.1 = (ε / 2) • coordVec 0 by simp [y],
      norm_smul]
    have hn : ‖(coordVec 0 : Space)‖ = 1 := by simp [coordVec]
    rw [hn, Real.norm_of_nonneg (by positivity)]
    linarith
  have h1 := hdiv _ hy
  rw [quadratic_fieldDiv] at h1
  have hy0 : y 0 = b.1 0 + ε / 2 := by simp [y, coordVec]
  rw [hy0] at h1
  linarith

end PlasmaLean.Sanity.BandSpec
