/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CylindricalDrift
public import PlasmaLean.Design.RationalStellarator

/-!
# The lifted guiding-centre velocity in the toroidal field

Non-vacuity of `Kinetic.CylindricalDrift.cylVelocity_littlejohn`: for the toroidal vacuum field
`∇φ = (−y, x, 0)/R²` all hypotheses hold off the axis, with the planar field-line equation
`x' = 0` and angular speed `ω = R⁻²`.

* `toroidal_rel`: `cylVelocity θ R (∇φ) = R⁻² (1, 0)`.
* `toroidal_decomp`: the lifted guiding-centre velocity is `(v_∥/|B|) R⁻² (1, 0)` plus the
  lifted drift, and the drift is bounded by the energy.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Sanity.CylindricalDrift
open Fields Vacuum Contract Kinetic Kinetic.GCLittlejohn Kinetic.CylindricalDrift
open Fields.CylindricalLift Design.RationalStellarator

/-- The angular speed of the toroidal field line through a lifted point. -/
def omega (p : ℝ × Plane) : ℝ := (p.2 0 ^ 2)⁻¹

/-- A point with positive cylindrical radius is off the axis. -/
theorem cylPoint_mem_domain {R : ℝ} (hR : 0 < R) (θ z : ℝ) : cylPoint R θ z ∈ domain := by
  have h : r2 (cylPoint R θ z) = R ^ 2 := by
    simp only [r2, cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination R ^ 2 * Real.cos_sq_add_sin_sq θ
  change 0 < r2 _
  rw [h]
  positivity

/-- The toroidal field has cylindrical velocity `R⁻² (1, 0)`. -/
theorem toroidal_rel {p : ℝ × Plane} (hR : 0 < p.2 0) :
    cylVelocity p.1 (p.2 0) (toroidal (cylPoint (p.2 0) p.1 (p.2 1))) =
      omega p • FlowLabel.field (fun _ _ => (0 : Plane)) p := by
  obtain ⟨c0, c1, -⟩ := cylPoint_coords (p.2 0) p.1 (p.2 1)
  have hcs := Real.cos_sq_add_sin_sq p.1
  have h : r2 (cylPoint (p.2 0) p.1 (p.2 1)) = p.2 0 ^ 2 := by
    simp only [r2, c0, c1]
    linear_combination p.2 0 ^ 2 * hcs
  refine Prod.ext ?_ ?_
  · simp only [cylVelocity, toroidal, winv, h, omega, FlowLabel.field, c0, c1,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Prod.smul_fst, smul_eq_mul,
      mul_one]
    field_simp
    linear_combination hcs
  · ext i
    fin_cases i
    · simp [cylVelocity, toroidal, winv, h, FlowLabel.field, c0, c1]
      ring
    · simp [cylVelocity, toroidal, FlowLabel.field]

/-- The toroidal field does not vanish off the axis. -/
theorem toroidal_ne_zero {p : ℝ × Plane} (hR : 0 < p.2 0) :
    toroidal (cylPoint (p.2 0) p.1 (p.2 1)) ≠ 0 := by
  intro h0
  have h := toroidal_rel (p := p) hR
  rw [h0] at h
  have h1 : (0 : ℝ) = (p.2 0 ^ 2)⁻¹ := by
    simpa [cylVelocity, omega, FlowLabel.field] using congrArg Prod.fst h
  exact (inv_pos.mpr (pow_pos hR 2)).ne h1

/-- **Sanity**: all hypotheses of the decomposition hold for the toroidal field off the axis,
and the lifted drift is bounded by the energy. -/
theorem toroidal_decomp {m q μ : ℝ} {p : ℝ × Plane} (hR : 0 < p.2 0) (hm : 0 ≤ m) (hμ : 0 ≤ μ)
    (hq : q ≠ 0) (v : ℝ) :
    let x := cylPoint (p.2 0) p.1 (p.2 1)
    cylVelocity p.1 (p.2 0) (littlejohnVelocity toroidal m q μ (x, v)).1 =
        rate toroidal omega (x, v) p • FlowLabel.field (fun _ _ => (0 : Plane)) p +
          perturbation toroidal m q μ (x, v) p ∧
      ‖perturbation toroidal m q μ (x, v) p‖ ≤ max 1 (p.2 0)⁻¹ *
        (2 * hamiltonian m μ toroidal x v / (|q| * ‖toroidal x‖ ^ 2) * ‖gradAbsB toroidal x‖) := by
  intro x
  have hx : x ∈ domain := cylPoint_mem_domain hR _ _
  have vac := toroidal_vacuum
  have nz : toroidal x ≠ 0 := toroidal_ne_zero hR
  have diff : DifferentiableAt ℝ toroidal x :=
    (vac.contDiffOn.contDiffAt (vac.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  have nocurl : curl (fderiv ℝ toroidal x) = 0 := by
    simpa only [fieldCurl, Forms.curlOp_eq_curl] using vac.curl_eq_zero x hx
  exact ⟨cylVelocity_littlejohn (w := (x, v)) nz diff nocurl hq (toroidal_rel hR),
    norm_perturbation_le (w := (x, v)) hR nz hm hμ⟩

end PlasmaLean.Sanity.CylindricalDrift
