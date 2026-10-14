/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.ClebschTorus
public import PlasmaLean.Theory.Fields.ClebschDivergence

/-!
# The Clebsch-torus field is divergence free but not a vacuum field

For the synthetic field `PlasmaLean.Design.ClebschTorus.field`
B = B_T + (1/8) ∇ψ × ∇x₂ we compute the actual Fréchet derivative from an explicit
polynomial Jacobian, and prove, at every point x:

* `field_divergence_free`: ∇ · B = 0, so B is an admissible magnetic field (no monopoles);
* `field_curl`: ∇ × B = (−3x₁/2, −3x₀/2, 3 − 9(x₀² + x₁²)/4), which is nonzero
  (`field_curl_origin`: curl = (0,0,3) at the origin; `field_not_vacuum`: nonzero
  at every point of the barrier region).

So by Ampère's law the field carries the current density curl B / μ₀ in the plasma
region: it is NOT a vacuum field, and producing it requires distributed current, not
only external coils. The Clebsch part is independently divergence free by the general
theorem `PlasmaLean.Fields.clebsch_divergence_free` (`clebschPart_divergence_free`).
No MHD force balance J × B = ∇p is claimed for this field.
-/

public section
noncomputable section
namespace PlasmaLean.Design.ClebschTorus
open Fields WithLp

/-- Explicit Jacobian `jac x k i = ∂ᵢ Bₖ (x)` of the example field. -/
@[expose] def jac (x : Space) : Fin 3 → Fin 3 → ℝ :=
  ![![(10 * x 0 * x 1 - 4 * (x 2 - x 0 * x 1 / 2)) / 8,
      -1 + (4 * (x 0 ^ 2 + x 1 ^ 2 - 1) + 8 * x 1 ^ 2 + 2 * x 0 ^ 2) / 8, -x 0 / 2],
    ![1 - (4 * (x 0 ^ 2 + x 1 ^ 2 - 1) + 8 * x 0 ^ 2 + 2 * x 1 ^ 2) / 8,
      -(10 * x 0 * x 1 - 4 * (x 2 - x 0 * x 1 / 2)) / 8, x 1 / 2],
    ![x 0, -x 1, 0]]

/-- Row `k` of the Jacobian as a continuous linear functional. -/
@[expose] def row (x : Space) (k : Fin 3) : Space →L[ℝ] ℝ :=
  ∑ i, jac x k i • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i

/-- The derivative operator assembled from the Jacobian rows. -/
@[expose] def fieldDeriv (x : Space) : Space →L[ℝ] Space :=
  ∑ k, (row x k).smulRight (basis k)

/-- Entries of the assembled derivative are the Jacobian entries. -/
theorem fieldDeriv_apply (x : Space) (i k : Fin 3) : fieldDeriv x (basis i) k = jac x k i := by
  rw [fieldDeriv, coords_apply]
  fin_cases i <;> simp [row, Fin.sum_univ_three, basis]

/-- Coordinate 0 of the field as an explicit polynomial. -/
theorem field_coord0 : (fun y => field y 0) = fun y =>
    -y 1 + 1 / 8 * (4 * y 1 * (y 0 ^ 2 + y 1 ^ 2 - 1) - 4 * y 0 * (y 2 - 1 / 2 * (y 0 * y 1)))
    := by
  funext y; rw [field_apply]
  simp only [psiGrad, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- Coordinate 1 of the field as an explicit polynomial. -/
theorem field_coord1 : (fun y => field y 1) = fun y =>
    y 0 - 1 / 8 * (4 * y 0 * (y 0 ^ 2 + y 1 ^ 2 - 1) - 4 * y 1 * (y 2 - 1 / 2 * (y 0 * y 1)))
    := by
  funext y; rw [field_apply]
  simp only [psiGrad, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- Coordinate 2 of the field as an explicit polynomial. -/
theorem field_coord2 : (fun y => field y 2) = fun y => 1 / 2 * (y 0 ^ 2 - y 1 ^ 2) := by
  funext y; rw [field_apply]; simp; ring

/-- The example field has the explicit Jacobian as its actual Fréchet derivative. -/
theorem field_hasFDerivAt (x : Space) : HasFDerivAt field (fieldDeriv x) x := by
  have h0 := coord_hasFDerivAt 0 x
  have h1 := coord_hasFDerivAt 1 x
  have h2 := coord_hasFDerivAt 2 x
  have hs := ((h0.pow 2).add (h1.pow 2)).sub_const 1
  have hw := h2.sub ((h0.mul h1).const_mul (1 / 2))
  have k0 : HasFDerivAt (fun y => field y 0) (row x 0) x := by
    rw [field_coord0]
    refine (h1.neg.add ((((h1.const_mul 4).mul hs).sub ((h0.const_mul 4).mul hw)).const_mul
      (1 / 8))).congr_fderiv ?_
    ext v
    simp [row, jac, Fin.sum_univ_three]
    ring
  have k1 : HasFDerivAt (fun y => field y 1) (row x 1) x := by
    rw [field_coord1]
    refine (h0.sub ((((h0.const_mul 4).mul hs).sub ((h1.const_mul 4).mul hw)).const_mul
      (1 / 8))).congr_fderiv ?_
    ext v
    simp [row, jac, Fin.sum_univ_three]
    ring
  have k2 : HasFDerivAt (fun y => field y 2) (row x 2) x := by
    rw [field_coord2]
    refine (((h0.pow 2).sub (h1.pow 2)).const_mul (1 / 2)).congr_fderiv ?_
    ext v
    simp [row, jac, Fin.sum_univ_three]
    ring
  apply hasFDerivAt_of_coords
  intro k
  fin_cases k
  · exact k0
  · exact k1
  · exact k2

/-- The example field is divergence free everywhere. -/
theorem field_divergence_free (x : Space) : divergence (fderiv ℝ field x) = 0 := by
  rw [(field_hasFDerivAt x).fderiv, divergence_apply, fieldDeriv_apply, fieldDeriv_apply,
    fieldDeriv_apply]
  simp [jac]
  ring

/-- Explicit curl of the example field. -/
theorem field_curl (x : Space) :
    curl (fderiv ℝ field x) =
      toLp 2 ![-3 * x 1 / 2, -3 * x 0 / 2, 3 - 9 * (x 0 ^ 2 + x 1 ^ 2) / 4] := by
  rw [(field_hasFDerivAt x).fderiv]
  obtain ⟨c0, c1, c2⟩ := curl_coords (fieldDeriv x)
  apply space_ext
  · rw [c0, fieldDeriv_apply, fieldDeriv_apply]; simp [jac]; ring
  · rw [c1, fieldDeriv_apply, fieldDeriv_apply]; simp [jac]; ring
  · rw [c2, fieldDeriv_apply, fieldDeriv_apply]; simp [jac]; ring

/-- The field is not a vacuum field: its curl is (0,0,3) at the origin. -/
theorem field_curl_origin : curl (fderiv ℝ field 0) = toLp 2 ![0, 0, 3] := by
  rw [field_curl]
  simp

/-- On the barrier region {ψ ≤ 1/4} the horizontal curl satisfies
curl₀² + curl₁² = 9(x₀² + x₁²)/4 ≥ 9/8, so the field needs distributed current
throughout the confinement region. (The vertical curl changes sign on the region.) -/
theorem field_curl_horizontal_on_region {x : Space} (hx : psi x ≤ 1 / 4) :
    9 / 8 ≤ curl (fderiv ℝ field x) 0 ^ 2 + curl (fderiv ℝ field x) 1 ^ 2 := by
  obtain ⟨h1, -, -, -, -⟩ := torusRegion_bounds hx
  rw [field_curl]
  simp
  nlinarith

/-- The field is not a vacuum field anywhere on its barrier region. -/
theorem field_not_vacuum {x : Space} (hx : psi x ≤ 1 / 4) : curl (fderiv ℝ field x) ≠ 0 := by
  intro h
  have := field_curl_horizontal_on_region hx
  rw [h] at this
  simp at this
  linarith

/-- The potentials of the example are smooth. -/
theorem psi_contDiff : ContDiff ℝ 2 psi := by
  unfold psi
  fun_prop

/-- Cross-check by the general theorem: the Clebsch part alone is divergence free. -/
theorem clebschPart_divergence_free (x : Space) :
    divergence (fderiv ℝ (clebschField psi height) x) = 0 :=
  clebsch_divergence_free psi_contDiff.contDiffAt (by unfold height; fun_prop)

end PlasmaLean.Design.ClebschTorus
