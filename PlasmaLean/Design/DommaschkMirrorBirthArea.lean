/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorBandPassage
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Area of certified phase-height pairs on the Dommaschk pilot launch -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorBirthArea

open Contract Certificates.PositionFrameSlabs DommaschkFirstMirrorLaunchSign
open DommaschkMirrorLaunch DommaschkKamC KamNewton Theory.KAM WEll1Z2
open Forms Fields.VacuumBoozer MeasureTheory Set

/-- Dimensionless Lebesgue measure here uses angle in radians and archive height. -/
def rectangle : Set (ℝ × ℝ) :=
  Icc (-(1 / 2 ^ 19 : ℝ)) (1 / 2 ^ 19) ×ˢ Icc (height false : ℝ) (height true)

/-- Exact area of the rectangle at fixed interpolation parameter 47/100. -/
theorem rectangle_area :
    volume rectangle = ENNReal.ofReal (1292367655761 / 655360000000000000000) := by
  rw [rectangle, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num [height]

/-- The regular-birth predicate at the Cartesian position interpolated between
the two selected tori, on the launch curve with interpolation parameter 47/100. -/
def regularPairs (uC zC uA zA : FA) : Set (ℝ × ℝ) :=
  {z | let b := birth uC zC uA zA (47 / 100) z.1
       RegularMirrorBirth (DommaschkQA2R.field DommaschkQA2R.candidate)
         (cylPoint (b 0) z.1 (b 1)) z.2}

/-- The same nested tori work for the whole rectangle. The explicit lower bound
uses the two-dimensional launch-parameter measure. -/
def AreaBound : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    rectangle ⊆ regularPairs uC zC uA zA ∧
    ENNReal.ofReal (1292367655761 / 655360000000000000000) ≤ volume (regularPairs uC zC uA zA)

theorem of_passage {C : ℝ → (ℝ → Plane) → Prop}
    (pilot : DommaschkSignedBirthApproach.ThroughBirth C)
    (pass : ∀ φ y, C φ y → DommaschkMirrorBandPassage.Passage φ y) : AreaBound := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, iC, iA, nested, every⟩ := pilot
  have sub : rectangle ⊆ regularPairs uC zC uA zA := by
    rintro ⟨φ, h⟩ ⟨phase, band⟩
    obtain ⟨y, start, prop⟩ := every φ (abs_le.mpr phase)
    have regular := ((pass φ y prop).2.2 h band).2.1
    change RegularMirrorBirth _ (cylPoint _ φ _) h
    simpa only [DommaschkFirstMirrorWell.point, start, coordinates,
      PiLp.continuousLinearEquiv_symm_apply] using regular
  exact ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, iC, iA, nested, sub,
    rectangle_area ▸ measure_mono sub⟩

end PlasmaLean.Design.DommaschkMirrorBirthArea
