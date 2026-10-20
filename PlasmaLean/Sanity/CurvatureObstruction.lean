/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Vacuum
public import PlasmaLean.Theory.Fields.CurvatureObstruction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Sanity checks for the curvature obstruction

Checks for `Theory/Fields/CurvatureObstruction`:
* degenerate case: a uniform field has zero field-line curvature;
* the hyperbolic vacuum field `(x, y, -2z)` has its minimum of `|B|` at the origin,
  where `B = 0`: the hypothesis `B ≠ 0` of Corollary B/C fails there, so the
  existence of this minimum is consistent with the obstruction;
* special case: along the `x`-axis (a straight field line of the hyperbolic field)
  the curvature computed by `fieldCurvature_eq` is `0`;
* rejected fixture: for the rigid-rotation field `(-y, x, 0)` (curl `2 e_z`, NOT a
  vacuum field) at `e_x`, the field lines are unit circles, `κ = -e_x`, while
  `∇(|B|²/2) = e_x` is already normal to `B`; so `∇⊥(|B|²/2) = e_x ≠ -e_x = |B|² κ`,
  showing that the curl-free hypothesis of the curvature identity is needed;
* non-vacuous instance of Corollary C (it is vacuous in simply connected regions): the
  straight-wire field `(-y, x, 0)/(x² + y²)` is a vacuum field off the wire
  (`wireField_vacuum`), the unit circle is a closed field line with `B ≠ 0`, hence
  `wireField_not_transverseMinB`; directly, `|B| = 1/r` decreases outward
  (`norm_wireField_radial`, `wireField_radial_not_isLocalMin`).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity
open PlasmaLean.Vacuum PlasmaLean.Fields

/-- Degenerate case: a uniform field has straight field lines, `κ = 0`. -/
theorem fieldCurvature_const (B₀ x : Euclid3) : fieldCurvature (fun _ => B₀) x = 0 := by
  change fderiv ℝ (fun _ : Euclid3 => ‖B₀‖⁻¹ • B₀) x _ = 0
  simp

/-- The hyperbolic vacuum field has a local minimum of `|B|` at the origin, but
`B = 0` there, so the curvature obstruction (which needs `B ≠ 0`) does not apply. -/
theorem hyperbolicField_min_at_zero :
    IsLocalMin (fun y => ‖hyperbolicField y‖) 0 ∧ hyperbolicField 0 = 0 := by
  refine ⟨Filter.Eventually.of_forall fun y => ?_, map_zero _⟩
  simp

/-- Along the `x`-axis the hyperbolic field is `B(e_x) = e_x`. -/
theorem hyperbolicField_coordVec0 : hyperbolicField (coordVec 0) = coordVec 0 := by
  ext i
  fin_cases i <;> simp [hyperbolicField]

/-- Special case: the hyperbolic field's field line through `e_x` (the `x`-axis) is
straight: `κ(e_x) = 0`. -/
theorem hyperbolicField_curvature_xAxis :
    fieldCurvature (fun y => hyperbolicField y) (coordVec 0) = 0 := by
  have h0 : hyperbolicField (coordVec 0) ≠ 0 := by
    rw [hyperbolicField_coordVec0]; simp
  have hu : unitField (fun y => hyperbolicField y) (coordVec 0) = coordVec 0 := by
    simp [unitField, hyperbolicField_coordVec0]
  rw [fieldCurvature_eq hyperbolicField.hasFDerivAt h0, hu, hyperbolicField_coordVec0]
  simp

/-- The rotation field at `e_x` is `e_y`. -/
theorem rotationField_coordVec0 : rotationField (coordVec 0) = coordVec 1 := by
  obtain ⟨h0, h1, h2⟩ := rotationField_coords (coordVec 0)
  ext i
  fin_cases i <;> simp [h0, h1, h2]

/-- The rotation field at `e_y` is `-e_x`. -/
theorem rotationField_coordVec1 : rotationField (coordVec 1) = -coordVec 0 := by
  obtain ⟨h0, h1, h2⟩ := rotationField_coords (coordVec 1)
  ext i
  fin_cases i <;> simp [h0, h1, h2]

/-- Rejected fixture, part 1: the field lines of the rotation field through `e_x` are
unit circles, `κ(e_x) = -e_x`. -/
theorem rotationField_curvature :
    fieldCurvature (fun y => rotationField y) (coordVec 0) = -coordVec 0 := by
  have h0 : rotationField (coordVec 0) ≠ 0 := by rw [rotationField_coordVec0]; simp
  have hu : unitField (fun y => rotationField y) (coordVec 0) = coordVec 1 := by
    simp [unitField, rotationField_coordVec0]
  rw [fieldCurvature_eq rotationField.hasFDerivAt h0, hu, rotationField_coordVec1]
  simp [rotationField_coordVec0, EuclideanSpace.inner_single_left]

/-- Rejected fixture, part 2: for the rotation field (curl `≠ 0`) at `e_x`,
`∇(|B|²/2) = e_x`. Since `⟪e_y, e_x⟫ = 0` and `|B|² κ = -e_x`, the vacuum curvature
identity `∇⊥(|B|²/2) = |B|² κ` FAILS without the curl-free hypothesis. -/
theorem rotationField_identity_fails :
    gradient (fun y => ‖rotationField y‖ ^ 2 / 2) (coordVec 0) = coordVec 0 ∧
      gradient (fun y => ‖rotationField y‖ ^ 2 / 2) (coordVec 0) -
          ⟪unitField (fun y => rotationField y) (coordVec 0),
            gradient (fun y => ‖rotationField y‖ ^ 2 / 2) (coordVec 0)⟫ •
            unitField (fun y => rotationField y) (coordVec 0) ≠
        ‖rotationField (coordVec 0)‖ ^ 2 •
          fieldCurvature (fun y => rotationField y) (coordVec 0) := by
  have hg : gradient (fun y => ‖rotationField y‖ ^ 2 / 2) (coordVec 0) = coordVec 0 := by
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    have hf : (fun y => ‖rotationField y‖ ^ 2 / 2) = fun y => ‖rotationField y‖ ^ 2 * (1 / 2) := by
      funext y; ring
    rw [hf]
    convert (rotationField.hasFDerivAt (x := coordVec 0)).norm_sq.mul_const (1 / 2 : ℝ) using 1
    ext v
    obtain ⟨h0, h1, h2⟩ := rotationField_coords v
    simp [rotationField_coordVec0, EuclideanSpace.inner_single_left, h1]
  have hu : unitField (fun y => rotationField y) (coordVec 0) = coordVec 1 := by
    simp [unitField, rotationField_coordVec0]
  refine ⟨hg, ?_⟩
  rw [hg, hu, rotationField_curvature, rotationField_coordVec0]
  intro h
  have := congrArg (fun v : Euclid3 => v 0) h
  simp at this
  norm_num at this

/-! ### A non-vacuous instance of Corollary C: the straight-wire field -/

/-- `r² = x² + y²`, the squared distance from the `z`-axis. -/
@[expose] def wireR2 (y : Euclid3) : ℝ := y 0 ^ 2 + y 1 ^ 2

/-- The field of a straight wire along the `z`-axis (up to the factor `μ₀ I / 2π`):
`B = (-y, x, 0) / (x² + y²)`, with `|B| = 1/r`. -/
@[expose] def wireField (y : Euclid3) : Euclid3 := (wireR2 y)⁻¹ • rotationField y

/-- The current-free region: space minus the wire (multiply connected). -/
@[expose] def wireRegion : Set Euclid3 := {y | 0 < wireR2 y}

/-- Derivative of `r²`. -/
theorem hasFDerivAt_wireR2 (y : Euclid3) :
    HasFDerivAt wireR2 ((2 * y 0) • (EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ) +
      (2 * y 1) • (EuclideanSpace.proj 1 : Euclid3 →L[ℝ] ℝ)) y := by
  have h0 := ((EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ).hasFDerivAt (x := y)).pow 2
  have h1 := ((EuclideanSpace.proj 1 : Euclid3 →L[ℝ] ℝ).hasFDerivAt (x := y)).pow 2
  exact (h0.add h1).congr_fderiv (by ext v; simp)

/-- Derivative of the wire field off the axis. -/
theorem hasFDerivAt_wireField {y : Euclid3} (hy : wireR2 y ≠ 0) :
    HasFDerivAt wireField ((wireR2 y)⁻¹ • rotationField +
      ((-(wireR2 y ^ 2)⁻¹) • ((2 * y 0) • (EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ) +
        (2 * y 1) • (EuclideanSpace.proj 1 : Euclid3 →L[ℝ] ℝ))).smulRight (rotationField y))
      y :=
  ((hasDerivAt_inv hy).comp_hasFDerivAt y (hasFDerivAt_wireR2 y)).smul rotationField.hasFDerivAt

/-- The wire region is open. -/
theorem isOpen_wireRegion : IsOpen wireRegion :=
  isOpen_lt continuous_const (by unfold wireR2; fun_prop)

/-- **The straight-wire field is a vacuum field** off the wire. -/
theorem wireField_vacuum : VacuumField wireRegion wireField := by
  refine ⟨isOpen_wireRegion, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · intro y hy
    have hy' : wireR2 y ≠ 0 := (show 0 < wireR2 y from hy).ne'
    have hr : ContDiff ℝ 2 wireR2 := by unfold wireR2; fun_prop
    exact ((hr.contDiffAt.inv hy').smul rotationField.contDiff.contDiffAt).contDiffWithinAt
  · have hy' : wireR2 y ≠ 0 := (show 0 < wireR2 y from hy).ne'
    rw [fieldDiv, (hasFDerivAt_wireField hy').fderiv, divOp_apply]
    obtain ⟨a0, a1, a2⟩ := rotationField_coords y
    obtain ⟨b0, b1, b2⟩ := rotationField_coords (coordVec 2)
    simp [rotationField_coordVec0, rotationField_coordVec1, a0, a1, b2]
    ring
  · have hy' : wireR2 y ≠ 0 := (show 0 < wireR2 y from hy).ne'
    rw [fieldCurl, (hasFDerivAt_wireField hy').fderiv]
    obtain ⟨a0, a1, a2⟩ := rotationField_coords y
    obtain ⟨b0, b1, b2⟩ := rotationField_coords (coordVec 2)
    ext k
    fin_cases k <;> simp [curlOp, rotationField_coordVec0, rotationField_coordVec1, a0, a1, a2,
      b0, b1]
    field_simp
    unfold wireR2 at hy' ⊢
    ring

/-- The unit circle in the plane `z = 0`, `γ(s) = (cos s, sin s, 0)`. -/
@[expose] def unitCircle (s : ℝ) : Euclid3 := Real.cos s • coordVec 0 + Real.sin s • coordVec 1

/-- `r² = 1` on the unit circle. -/
theorem wireR2_unitCircle (s : ℝ) : wireR2 (unitCircle s) = 1 := by
  simp [wireR2, unitCircle, Real.cos_sq_add_sin_sq]

/-- The unit circle is a field line of the wire field: `γ' = B ∘ γ`. -/
theorem unitCircle_fieldLine (s : ℝ) : HasDerivAt unitCircle (wireField (unitCircle s)) s := by
  have h := ((Real.hasDerivAt_cos s).smul_const (coordVec 0)).add
    ((Real.hasDerivAt_sin s).smul_const (coordVec 1))
  convert h using 1
  · rfl
  rw [wireField, wireR2_unitCircle, inv_one, one_smul, unitCircle, map_add, map_smul, map_smul,
    rotationField_coordVec0, rotationField_coordVec1]
  ext i
  fin_cases i <;> simp

/-- The field does not vanish on the unit circle (`|B| = 1` there). -/
theorem wireField_unitCircle_ne_zero (s : ℝ) : wireField (unitCircle s) ≠ 0 := by
  intro h
  have := congrArg (fun v : Euclid3 => ‖v‖ ^ 2) (unitCircle_fieldLine s).deriv
  rw [wireField, wireR2_unitCircle, inv_one, one_smul] at h
  have h2 := congrArg (fun v : Euclid3 => v 0 ^ 2 + v 1 ^ 2) h
  obtain ⟨a0, a1, _⟩ := rotationField_coords (unitCircle s)
  simp only [a0, a1, PiLp.zero_apply] at h2
  have h3 := wireR2_unitCircle s
  unfold wireR2 at h3
  nlinarith

/-- **Corollary C is not vacuous.** The straight-wire field on the (multiply connected)
region off the wire has the unit circle as a closed field line with `B ≠ 0`, so every
hypothesis of `VacuumField.not_closed_fieldLine_transverse_minB` holds and
`TransverseMinB` must fail. -/
theorem wireField_not_transverseMinB :
    ¬ TransverseMinB wireField unitCircle (2 * Real.pi) :=
  wireField_vacuum.not_closed_fieldLine_transverse_minB (by positivity)
    (fun s _ => show 0 < wireR2 (unitCircle s) by rw [wireR2_unitCircle]; norm_num)
    (fun s _ => unitCircle_fieldLine s) (fun s _ => wireField_unitCircle_ne_zero s)
    (by simp [unitCircle])

/-- `|B| = 1/(1 + σ)` along the outward radial line through `e_x = γ(0)`. -/
theorem norm_wireField_radial (σ : ℝ) (hσ : 0 < 1 + σ) :
    ‖wireField (unitCircle 0 + σ • coordVec 0)‖ = (1 + σ)⁻¹ := by
  have hp : unitCircle 0 + σ • coordVec 0 = (1 + σ) • coordVec 0 := by
    simp [unitCircle, add_smul]
  have hr : wireR2 ((1 + σ) • coordVec 0) = (1 + σ) ^ 2 := by simp [wireR2]
  rw [hp, wireField, hr, map_smul, rotationField_coordVec0, smul_smul, norm_smul]
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity)]
  field_simp

/-- **Why `TransverseMinB` fails directly:** `|B| = 1/r` decreases outward, so along the
radial direction `e_x ⊥ B(e_x) = e_y` the function `σ ↦ |B(e_x + σ e_x)|` has no local
minimum at `σ = 0`. -/
theorem wireField_radial_not_isLocalMin :
    ¬ IsLocalMin (fun σ : ℝ => ‖wireField (unitCircle 0 + σ • coordVec 0)‖) 0 := by
  intro h
  have hev := (h.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num) : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0))
  obtain ⟨σ, hle, hσ0, _⟩ := hev.exists
  simp only at hle
  rw [norm_wireField_radial 0 (by norm_num), norm_wireField_radial σ (by linarith)] at hle
  have : (1 + σ)⁻¹ < (1 + 0)⁻¹ := by
    rw [add_zero, inv_one]; exact inv_lt_one_of_one_lt₀ (by linarith)
  linarith

/-- The radial direction `e_x` is normal to `B(γ 0) = e_y`. -/
theorem wireField_unitCircle_zero_perp : ⟪wireField (unitCircle 0), coordVec 0⟫ = 0 := by
  rw [wireField, wireR2_unitCircle, inv_one, one_smul]
  simp [unitCircle, rotationField_coordVec0, EuclideanSpace.inner_single_left]

end PlasmaLean.Sanity
