/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormPiecewisePeriod
public import PlasmaLean.Sanity.FormPeriods
public import PlasmaLean.Sanity.FormLoopCurrent
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sanity checks for `Theory/Fields/FormPiecewisePeriod`

* Accepted, nonzero period: the square with vertices `(1, -1, 0)`, `(1, 1, 0)`, `(-1, 1, 0)`,
  `(-1, -1, 0)` encircles the wire axis once. Each edge contributes `π/2` to the circulation of
  the wire field (`wire_edge_integral`, an arctangent integral), so the circulation is `2π`
  (`square_circulation`, `square_lineIntegral`) and so is the de Rham period on the class of
  the polygonal loop (`square_period`). This is the value on the unit circle (`wire_period`).
* Hypothesis check: the square has a genuine corner, so it is not `C¹` on `[0, 4]`
  (`square_not_differentiableAt`, `square_not_contDiffOn`); the theorems for curves that are
  `C¹` on the whole interval do not apply to it.
* Accepted, two pieces: the unit circle cut into its upper and lower halves
  (`halfCircles_period`); the two-piece theorem gives the period `2π`.
* Accepted, zero: a triangle in the simply connected bent region has zero circulation for the
  hyperbolic vacuum field (`hyperbolic_triangle_circulation`), by the corollary for simply
  connected regions.
* Rejected: the corollary fails without simple connectedness. The square in the wire region has
  circulation `2π ≠ 0` (`square_circulation_ne_zero`), which proves again that the complement
  of a line is not simply connected (`wireOpens_not_simplyConnected_of_square`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormPiecewisePeriod

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open PlasmaLean.Sanity.FormTopology PlasmaLean.Sanity.FormPeriods
open PlasmaLean.Sanity.FormLoopCurrent PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-! ## The wire field along a straight segment -/

/-- The tangential component of the wire field along a segment from `P` to `Q`: the constant
`P₀ Q₁ - P₁ Q₀` divided by the squared distance to the axis. -/
theorem wire_segment_integrand (P Q : Space) (s : ℝ) :
    ⟪wireField (segCurve P Q s), Q - P⟫
      = (wireR2 (segCurve P Q s))⁻¹ * (P 0 * Q 1 - P 1 * Q 0) := by
  obtain ⟨a0, a1, a2⟩ := rotationField_coords (segCurve P Q s)
  have hx0 : (segCurve P Q s) 0 = P 0 + s * (Q 0 - P 0) := by simp [segCurve]
  have hx1 : (segCurve P Q s) 1 = P 1 + s * (Q 1 - P 1) := by simp [segCurve]
  rw [inner_coords3]
  simp only [wireField, PiLp.smul_apply, smul_eq_mul, a0, a1, a2, PiLp.sub_apply]
  rw [hx0, hx1]
  ring

/-- `∫₀¹ 2 / (1 + (2s - 1)²) ds = π/2`. -/
theorem integral_arctan_edge :
    ∫ s in (0 : ℝ)..1, (1 + (2 * s - 1) ^ 2)⁻¹ * 2 = Real.pi / 2 := by
  have h := intervalIntegral.mul_integral_comp_mul_sub (f := fun x : ℝ => (1 + x ^ 2)⁻¹)
    (a := 0) (b := 1) (c := 2) (d := 1)
  rw [intervalIntegral.integral_mul_const, mul_comm, h, integral_inv_one_add_sq]
  have e1 : (2 : ℝ) * 1 - 1 = 1 := by norm_num
  have e2 : (2 : ℝ) * 0 - 1 = -1 := by norm_num
  rw [e1, e2, Real.arctan_neg, Real.arctan_one]
  ring

/-- **One edge of the square carries a quarter of the current.** A segment along which the
squared distance to the axis is `1 + (2s - 1)²` and for which `P₀ Q₁ - P₁ Q₀ = 2` has wire
circulation `π/2`. -/
theorem wire_edge_integral (P Q : Space)
    (hR : ∀ s, wireR2 (segCurve P Q s) = 1 + (2 * s - 1) ^ 2)
    (hN : P 0 * Q 1 - P 1 * Q 0 = 2) :
    lineIntegral wireField (segCurve P Q) 0 1 = Real.pi / 2 := by
  rw [lineIntegral_segCurve]
  simp only [wire_segment_integrand, hR, hN]
  exact integral_arctan_edge

/-! ## A square around the wire -/

/-- The vertices of the square `(1, -1, 0)`, `(1, 1, 0)`, `(-1, 1, 0)`, `(-1, -1, 0)`, traversed
anticlockwise about the wire axis; the list closes up at index `4`. -/
noncomputable def squareVertex : ℕ → Space
  | 0 => !₂[1, -1, 0]
  | 1 => !₂[1, 1, 0]
  | 2 => !₂[-1, 1, 0]
  | 3 => !₂[-1, -1, 0]
  | _ => !₂[1, -1, 0]

/-- The square closes up. -/
theorem squareVertex_closed : squareVertex 0 = squareVertex 4 :=
  rfl

/-- Along every edge of the square the squared distance to the axis is `1 + (2s - 1)²`. -/
theorem wireR2_square_edge {i : ℕ} (hi : i < 4) (s : ℝ) :
    wireR2 (segCurve (squareVertex i) (squareVertex (i + 1)) s) = 1 + (2 * s - 1) ^ 2 := by
  interval_cases i <;> simp [squareVertex, wireR2, segCurve] <;> ring

/-- Every edge of the square lies in the wire region. -/
theorem square_edge_mem : ∀ i < 4, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    segCurve (squareVertex i) (squareVertex (i + 1)) s ∈ wireOpens := by
  intro i hi s _
  change 0 < wireR2 _
  rw [wireR2_square_edge hi]
  positivity

/-- Each edge of the square has wire circulation `π/2`. -/
theorem square_edge_integral {i : ℕ} (hi : i < 4) :
    lineIntegral wireField (segCurve (squareVertex i) (squareVertex (i + 1))) 0 1
      = Real.pi / 2 := by
  refine wire_edge_integral _ _ (wireR2_square_edge hi) ?_
  interval_cases i <;> simp [squareVertex] <;> norm_num

/-- **Ampère's law on a square**: the circulation of the wire field around the square, as the
sum over the four edges, is `2π`. -/
theorem square_circulation :
    ∑ i ∈ Finset.range 4,
      lineIntegral wireField (segCurve (squareVertex i) (squareVertex (i + 1))) 0 1
      = 2 * Real.pi := by
  rw [Finset.sum_congr rfl fun i hi => square_edge_integral (Finset.mem_range.1 hi)]
  simp
  ring

/-- The square is a piecewise `C¹` curve in the wire region. -/
theorem square_piecewise :
    PiecewiseC1In wireOpens (polyCurve squareVertex) (fun i => (i : ℝ)) 4 :=
  piecewiseC1In_polyCurve (by norm_num) square_edge_mem

/-- The square closes up as a curve. -/
theorem square_closed :
    polyCurve squareVertex ((0 : ℕ) : ℝ) = polyCurve squareVertex ((4 : ℕ) : ℝ) := by
  rw [polyCurve_natCast, polyCurve_natCast]
  exact squareVertex_closed

/-- The circulation of the wire field along the polygonal curve over `[0, 4]` is `2π`. -/
theorem square_lineIntegral :
    lineIntegral wireField (polyCurve squareVertex) ((0 : ℕ) : ℝ) ((4 : ℕ) : ℝ)
      = 2 * Real.pi := by
  rw [← sum_lineIntegral_pieces (U := wireOpens) wireField_vacuum.contDiffOn.continuousOn
    square_piecewise, ← square_circulation]
  exact Finset.sum_congr rfl fun i _ => lineIntegral_polyCurve_piece wireField squareVertex i

/-- **The de Rham period of the wire form on the square is `2π`**, the same as on the unit
circle (`wire_period`). The loop is the concatenation of four straight pieces. -/
theorem square_period :
    periodHom (onOpens wireOpens fun y => flat (wireField y))
      ⟨polyCurve squareVertex ((0 : ℕ) : ℝ), square_piecewise.mem_zero⟩
      (Additive.ofMul (chainLoop square_piecewise square_closed)) = 2 * Real.pi := by
  rw [← lineIntegral_eq_periodHom_piecewise (U := wireOpens)
    (wireField_vacuum.contDiffOn.of_le (by norm_num)) wireField_vacuum.curl_eq_zero
    square_piecewise square_closed]
  exact square_lineIntegral

/-- The same period, from the polygon theorem. -/
theorem square_period_polygon :
    periodHom (onOpens wireOpens fun y => flat (wireField y))
      ⟨polyCurve squareVertex ((0 : ℕ) : ℝ), square_piecewise.mem_zero⟩
      (Additive.ofMul (chainLoop square_piecewise square_closed)) = 2 * Real.pi := by
  rw [← square_circulation]
  exact (sum_lineIntegral_segCurve_eq_periodHom (U := wireOpens)
    (wireField_vacuum.contDiffOn.of_le (by norm_num)) wireField_vacuum.curl_eq_zero
    (by norm_num) square_edge_mem squareVertex_closed).symm

/-! ## The square is not `C¹`: the new theorem is needed -/

/-- The edge vectors at the vertex `(1, 1, 0)` differ. -/
theorem square_corner :
    squareVertex (0 + 1) - squareVertex 0 ≠ squareVertex (0 + 1 + 1) - squareVertex (0 + 1) := by
  intro h
  have h0 := congrArg (fun v : Space => v 0) h
  norm_num [squareVertex] at h0

/-- **Hypothesis check**: the square is not differentiable at the vertex `(1, 1, 0)`. -/
theorem square_not_differentiableAt :
    ¬ DifferentiableAt ℝ (polyCurve squareVertex) ((0 + 1 : ℕ) : ℝ) :=
  not_differentiableAt_polyCurve squareVertex 0 square_corner

/-- **Hypothesis check**: the square is not `C¹` on `[0, 4]`, so `lineIntegral_eq_periodHom`
(for curves that are `C¹` on the whole interval) does not apply to it. -/
theorem square_not_contDiffOn :
    ¬ ContDiffOn ℝ 1 (polyCurve squareVertex) (Set.Icc (0 : ℝ) (4 : ℕ)) :=
  not_contDiffOn_polyCurve squareVertex (by norm_num) square_corner

/-! ## Rejected: the corollary for simply connected regions needs its hypothesis -/

/-- The circulation around the square is not zero. -/
theorem square_circulation_ne_zero :
    ∑ i ∈ Finset.range 4,
      lineIntegral wireField (segCurve (squareVertex i) (squareVertex (i + 1))) 0 1 ≠ 0 := by
  rw [square_circulation]
  positivity

/-- **Rejected case**: if the wire region were simply connected, the circulation around the
square would vanish. So the complement of a line is not simply connected. -/
theorem wireOpens_not_simplyConnected_of_square : ¬ SimplyConnectedSpace wireOpens := fun _ =>
  square_circulation_ne_zero
    (VacuumField.sum_lineIntegral_segCurve_eq_zero (U := wireOpens) wireField_vacuum
      (by norm_num) square_edge_mem squareVertex_closed)

/-! ## Two pieces: the upper and lower halves of the unit circle -/

/-- The unit circle is `C¹` on every set. -/
theorem unitCircle_contDiffOn (s : Set ℝ) : ContDiffOn ℝ 1 unitCircle s := by
  have h : ContDiff ℝ 1 unitCircle := by
    unfold unitCircle
    fun_prop
  exact h.contDiffOn

/-- The circulation of the wire field around the unit circle over `[0, 2π]` is `2π`. -/
theorem unitCircle_lineIntegral :
    lineIntegral wireField unitCircle 0 (2 * Real.pi) = 2 * Real.pi := by
  have hI : ∀ t : ℝ, ⟪wireField (unitCircle t), deriv unitCircle t⟫ = 1 := fun t => by
    rw [(unitCircle_fieldLine t).deriv, wireField_unitCircle_inner]
  simp [lineIntegral, hI]

/-- **Two pieces**: the period of the wire form on the loop made of the upper half circle
followed by the lower half circle is `2π`. -/
theorem halfCircles_period :
    periodHom (onOpens wireOpens fun y => flat (wireField y))
      ⟨unitCircle 0, unitCircle_mem 0⟩
      (Additive.ofMul (.of (.mk (((arcPath (U := wireOpens) Real.pi_pos.le
        (fun t _ => unitCircle_mem t) (unitCircle_contDiffOn _).continuousOn).trans
        (arcPath (U := wireOpens) (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi)
          (fun t _ => unitCircle_mem t) (unitCircle_contDiffOn _).continuousOn)).cast rfl
        (Subtype.ext unitCircle_two_pi.symm))))) = 2 * Real.pi := by
  rw [← lineIntegral_eq_periodHom_two_pieces (U := wireOpens)
    (wireField_vacuum.contDiffOn.of_le (by norm_num)) wireField_vacuum.curl_eq_zero
    Real.pi_pos (by linarith [Real.pi_pos]) (fun t _ => unitCircle_mem t)
    (fun t _ => unitCircle_mem t) (unitCircle_contDiffOn _) (unitCircle_contDiffOn _)
    unitCircle_two_pi.symm]
  exact unitCircle_lineIntegral

/-! ## Accepted: a triangle in a simply connected region -/

/-- The vertices of a triangle in the plane `z = -1`; the list closes up at index `3`. -/
noncomputable def triangleVertex : ℕ → Space
  | 0 => !₂[0, 0, -1]
  | 1 => !₂[1, 0, -1]
  | 2 => !₂[0, 1, -1]
  | _ => !₂[0, 0, -1]

/-- A segment in the plane `z = -1` lies in the bent region `z < x²`. -/
theorem segCurve_mem_bent {P Q : Space} (hP : P 2 = -1) (hQ : Q 2 = -1) (s : ℝ) :
    segCurve P Q s ∈ bentOpens := by
  change (segCurve P Q s) 2 < (segCurve P Q s) 0 ^ 2
  have h2 : (segCurve P Q s) 2 = -1 := by
    simp [segCurve, hP, hQ]
  rw [h2]
  nlinarith [sq_nonneg ((segCurve P Q s) 0)]

/-- Every edge of the triangle lies in the bent region. -/
theorem triangle_edge_mem : ∀ i < 3, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    segCurve (triangleVertex i) (triangleVertex (i + 1)) s ∈ bentOpens := by
  intro i hi s _
  refine segCurve_mem_bent ?_ ?_ s <;> interval_cases i <;> simp [triangleVertex]

/-- **Accepted case**: the hyperbolic vacuum field has zero circulation around the triangle,
which lies in the simply connected bent region. -/
theorem hyperbolic_triangle_circulation :
    ∑ i ∈ Finset.range 3, lineIntegral (fun y => hyperbolicField y)
      (segCurve (triangleVertex i) (triangleVertex (i + 1))) 0 1 = 0 :=
  VacuumField.sum_lineIntegral_segCurve_eq_zero (U := bentOpens) hyperbolic_vacuum_bent
    (by norm_num) triangle_edge_mem rfl

/-- The triangle has a genuine corner at its second vertex, so it is not `C¹` on `[0, 3]`. -/
theorem triangle_not_contDiffOn :
    ¬ ContDiffOn ℝ 1 (polyCurve triangleVertex) (Set.Icc (0 : ℝ) (3 : ℕ)) := by
  refine not_contDiffOn_polyCurve triangleVertex (i := 0) (by norm_num) fun h => ?_
  have h0 := congrArg (fun v : Space => v 0) h
  norm_num [triangleVertex] at h0

/-- **Accepted case, as a curve**: the circulation of the hyperbolic field along the triangle
over `[0, 3]` is zero, by the corollary for piecewise `C¹` loops. -/
theorem hyperbolic_triangle_lineIntegral :
    lineIntegral (fun y => hyperbolicField y) (polyCurve triangleVertex) ((0 : ℕ) : ℝ)
      ((3 : ℕ) : ℝ) = 0 :=
  VacuumField.lineIntegral_eq_zero_of_piecewise (U := bentOpens) hyperbolic_vacuum_bent
    (piecewiseC1In_polyCurve (by norm_num) triangle_edge_mem)
    (by rw [polyCurve_natCast, polyCurve_natCast]; rfl)

end PlasmaLean.Sanity.FormPiecewisePeriod
