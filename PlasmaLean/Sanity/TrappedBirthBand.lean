/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.TrappedBirthBand
public import PlasmaLean.Theory.Kinetic.LorentzOrbitOpen

/-!
# A trapped Littlejohn orbit in a quadratic mirror

In the synthetic field `B = (1 + x₀²)e₀`, mass two and magnetic moment one
give a unit-frequency oscillator. The divergence is 2x₀, so this field tests the kinetic
equations independently of the Maxwell laws.
The reference birth population used here is an explicitly atomic measure.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Sanity.TrappedBirthBand

open PlasmaLean.Contract PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Kinetic
open GCLittlejohn Real Set MeasureTheory
open scoped RealInnerProductSpace

/-- A positive quadratic mirror strength along lines parallel to the first coordinate. -/
def mirror (x : Space) : Space := (1 + (x 0) ^ 2) • coordVec 0

/-- The divergence is `2x₀`. The fixture violates the magnetic Gauss law away from x₀=0. -/
theorem quadratic_fieldDiv (x : Space) : fieldDiv mirror x = 2 * x 0 := by
  have hp := ((EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2
  have hd := (hp.const_add 1).smul_const (coordVec 0)
  rw [fieldDiv, show fderiv ℝ mirror x = _ from hd.fderiv, divOp_apply]
  simp [coordVec]

private theorem strength (x : Space) : ‖mirror x‖ = 1 + (x 0) ^ 2 := by
  simp [mirror, norm_smul, coordVec, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + (x 0)^2)]

private theorem direction : bhat mirror = fun _ => coordVec 0 := by
  funext x
  rw [bhat, strength, mirror, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

private theorem axis_coordinate (s : ℝ) : (s • coordVec 0 : Space) 0 = s := by simp [coordVec]

private theorem strength_on_axis (s : ℝ) : ‖mirror (s • coordVec 0)‖ = 1 + s^2 := by
  rw [strength, axis_coordinate]

/-- Birth at the origin at mirror height two has simple turning points at arclength ±1. -/
theorem quadratic_regularMirrorBirth : RegularMirrorBirth mirror 0 2 := by
  let line := fun s : ℝ => s • coordVec 0
  have hd (s : ℝ) : HasDerivAt line (coordVec 0) s := by
    simpa [line] using (hasDerivAt_id s).smul_const (coordVec 0)
  have hs : (fun s => ‖mirror (line s)‖) = fun s => 1 + s^2 := funext strength_on_axis
  have ds (s : ℝ) : deriv (fun k => ‖mirror (line k)‖) s = 2 * s := by
    rw [hs]
    simp
  refine ⟨line, -1, 1, by norm_num, by constructor <;> norm_num, by simp [line], ?_, ?_, ?_, ?_, ?_⟩
  · intro s _
    exact ⟨fun hz => by have hh := strength_on_axis s; rw [hz, norm_zero] at hh; nlinarith, by
      simpa [direction] using hd s⟩
  · change ‖mirror ((-1 : ℝ) • coordVec 0)‖ = 2
    rw [strength_on_axis]
    norm_num
  · change ‖mirror ((1 : ℝ) • coordVec 0)‖ = 2
    rw [strength_on_axis]
    norm_num
  · intro s hs
    rw [show ‖mirror (line s)‖ = 1 + s^2 from strength_on_axis s]
    nlinarith [mul_pos (sub_pos.mpr hs.2) (show 0 < s+1 by linarith [hs.1])]
  · rw [ds, ds]
    norm_num

private theorem strength_gradient (x : Space) : gradAbsB mirror x = (2 * x 0) • coordVec 0 := by
  rw [gradAbsB, show (fun y => ‖mirror y‖) = fun y : Space => 1 + (y 0)^2 from funext strength]
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hp := ((EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2
  have heq : (InnerProductSpace.toDual ℝ Space) ((2 * x 0) • coordVec 0) =
      (2 • (EuclideanSpace.proj 0) x ^ (2 - 1)) • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, coordVec,
      EuclideanSpace.inner_single_left]
  rw [heq]
  exact hp.const_add 1

private theorem star (m q v : ℝ) (x : Space) : Bstar m q mirror v x = mirror x := by
  simp [Bstar, curlb, direction, curl]

private theorem star_parallel (m q v : ℝ) (x : Space) :
    BstarPar m q mirror v x = 1 + (x 0)^2 := by
  simp [BstarPar, direction, star, mirror, coordVec, inner_smul_right]

/-- The complete phase-space right-hand side reduces to the linear oscillator. -/
theorem littlejohnVelocity_quadratic (q : ℝ) (w : Space × ℝ) :
    littlejohnVelocity mirror 2 q 1 w = (w.2 • coordVec 0, -(w.1 0)) := by
  have pos : 0 < 1 + (w.1 0)^2 := by positivity
  have hc : cross (coordVec 0) (coordVec 0) = 0 := by simp [cross]
  simp only [littlejohnVelocity, star_parallel, star, direction, strength_gradient, mirror,
    cross_smul_right, hc, smul_zero, add_zero, smul_smul, inner_smul_left, inner_smul_right]
  congr 1
  · rw [← mul_assoc, mul_comm _ w.2, mul_assoc, inv_mul_cancel₀ pos.ne', mul_one]
  · simp [coordVec]
    field_simp

/-- Start at the centre of the well with unit parallel speed and unit magnetic moment. -/
def mirrorBirth : GCBirth := (0, 1, 1)

/-- The resulting mirror orbit in position and parallel velocity. -/
def mirrorOrbit (s : ℝ) : Space × ℝ := (sin s • coordVec 0, cos s)

private theorem mirrorOrbit_solves (q t : ℝ) :
    GCBirthOrbitOn mirror 2 q mirrorBirth mirrorOrbit t := by
  refine ⟨by simp [mirrorOrbit, mirrorBirth], fun s _ => ?_⟩
  change HasDerivAt mirrorOrbit (littlejohnVelocity mirror 2 q 1 (mirrorOrbit s)) s
  rw [littlejohnVelocity_quadratic]
  change HasDerivAt (fun u => (sin u • coordVec 0, cos u))
    (cos s • coordVec 0, -((sin s • coordVec 0 : Space) 0)) s
  rw [axis_coordinate]
  exact ((Real.hasDerivAt_sin s).smul_const (coordVec 0)).prodMk (Real.hasDerivAt_cos s)

private theorem partial_eq_mirrorOrbit {q t : ℝ} (ht : 0 ≤ t) {z : ℝ → Space × ℝ}
    (h : GCBirthOrbitOn mirror 2 q mirrorBirth z t) : z t = mirrorOrbit t := by
  have ha := mirrorOrbit_solves q t
  let f : Space × ℝ → Space × ℝ := fun w => (w.2 • coordVec 0, -w.1 0)
  have smooth : ContDiff ℝ 1 f := by
    dsimp [f]
    fun_prop
  have he := integralCurve_eqOn_of_contDiffOn (f := f) isOpen_univ smooth.contDiffOn
    ordConnected_Icc (t₀ := (0 : ℝ)) (left_mem_Icc.mpr ht)
    (γ₁ := z) (γ₂ := mirrorOrbit)
    (fun s hs => by simpa only [mirrorBirth, littlejohnVelocity_quadratic, f] using h.2 s hs)
    (fun s hs => by simpa only [mirrorBirth, littlejohnVelocity_quadratic, f] using ha.2 s hs)
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) (h.1.trans ha.1.symm)
  exact he (right_mem_Icc.mpr ht)

private theorem reference_singleton :
    trappedReference mirror 2 {mirrorBirth} (Icc 1 3) (Icc (1 / 3) (2 / 3)) = {mirrorBirth} := by
  ext b
  constructor
  · exact fun h => h.1
  · rintro rfl
    have e : hamiltonian 2 1 mirror 0 1 = 2 := by norm_num [hamiltonian, strength]
    change mirrorBirth ∈ ({mirrorBirth} : Set GCBirth) ∧ 0 < (1 : ℝ) ∧
      0 < hamiltonian 2 1 mirror 0 1 ∧ hamiltonian 2 1 mirror 0 1 ∈ Icc 1 3 ∧
      1 / hamiltonian 2 1 mirror 0 1 ∈ Icc (1 / 3) (2 / 3) ∧
      RegularMirrorBirth mirror 0 (hamiltonian 2 1 mirror 0 1 / 1)
    rw [e, div_one]
    exact ⟨mem_singleton _, by norm_num, by norm_num, by constructor <;> norm_num,
      by constructor <;> norm_num, quadratic_regularMirrorBirth⟩

/-- For any positive horizon and either sign of charge, every partial orbit of the
unit-speed birth stays within one length unit of its starting distance to the origin.
The supplied Dirac measure assigns mass one to the tested birth. -/
theorem quadratic_guidingCentreBand {q T : ℝ} (hq : q ≠ 0) (hT : 0 < T) :
    GuidingCentreBand mirror 2 q {0} (Measure.dirac mirrorBirth) {mirrorBirth} {mirrorBirth}
      (Icc 1 3) (Icc (1 / 3) (2 / 3)) 1 1 T := by
  refine ⟨by norm_num, hq, singleton_nonempty _, isCompact_singleton, hT, by norm_num,
    ?_, ?_, ?_⟩
  · rw [reference_singleton]
    apply BirthCoverage.full (measurableSet_singleton _)
    · simp
    · simp [measureReal_def]
  · rintro _ rfl
    exact ⟨mirrorOrbit, mirrorOrbit_solves q T⟩
  · rintro _ rfl t ht z hz
    rw [partial_eq_mirrorOrbit ht.1 hz]
    refine ⟨fun he => ?_, ?_, ?_⟩
    · have hpos := strength (mirrorOrbit t).1
      rw [he, norm_zero] at hpos
      nlinarith
    · rw [star_parallel]
      positivity
    · simp [mirrorBirth, mirrorOrbit, Metric.infDist_singleton, norm_smul, coordVec,
        Real.abs_sin_le_one]

end PlasmaLean.Sanity.TrappedBirthBand
