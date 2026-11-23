/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormLoopCurrent
public import PlasmaLean.Sanity.FormPeriods

/-!
# Sanity checks for `Theory/Fields/FormLoopCurrent`

* Reparametrisation, on the straight-wire fixture: the circulation of the wire field around the
  unit circle is `2π` over `θ ∈ [0, 2π]` (`wire_circulation_two_pi`) and over `θ ∈ [-π, π]`
  (`wire_circulation_symm`), as it is over `[0, 1]` in `Sanity/FormPeriods`.
* Accepted case for the topological corollary: the circular torus section
  `R = 3 + cos θ`, `z = sin θ` at `φ₀ = 0` lies in the simply connected bent region
  `z < x²`, where the hyperbolic field is a vacuum field. Its poloidal circulation and loop
  current vanish (`hyperbolic_poloidalCirculation`, `hyperbolic_loopCurrent`), and so does the
  de Rham period of its 1-form on that loop (`hyperbolic_period`).
* Rejected case: the wire field, on the complement of its axis, has circulation `2π ≠ 0`
  around a closed loop (`wire_circulation_two_pi_ne_zero`); that region is not simply connected,
  so the corollary does not apply. The unit circle is not a poloidal loop (it has constant
  height, not constant toroidal angle), so this rejection is stated for `lineIntegral`, not for
  `poloidalCirculation`.
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormLoopCurrent

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open PlasmaLean.Sanity.FormTopology PlasmaLean.Sanity.FormPeriods PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-- **Reparametrisation check**: the circulation of the wire field around the unit circle over
`θ ∈ [0, 2π]` is `2π`. -/
theorem wire_circulation_two_pi :
    lineIntegral wireField unitCircle 0 (2 * Real.pi) = 2 * Real.pi := by
  rw [← lineIntegral_comp_affine]
  refine Eq.trans ?_ wire_circulation
  congr 1
  funext t
  change unitCircle (0 + (2 * Real.pi - 0) * t) = unitCircle (2 * Real.pi * t)
  rw [zero_add, sub_zero]

/-- The unit circle has period `2π`. -/
theorem unitCircle_add_two_pi (s : ℝ) : unitCircle (s + 2 * Real.pi) = unitCircle s := by
  simp [unitCircle]

/-- **Reparametrisation check, symmetric interval**: the circulation of the wire field around
the unit circle over `θ ∈ [-π, π]` is `2π`. -/
theorem wire_circulation_symm :
    lineIntegral wireField unitCircle (-Real.pi) Real.pi = 2 * Real.pi := by
  have hI (t : ℝ) : ⟪wireField (unitCircle t), deriv unitCircle t⟫ = 1 := by
    rw [(unitCircle_fieldLine t).deriv, wireField_unitCircle_inner]
  simp only [lineIntegral, hI, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Rejected case: on the complement of the wire, which is not simply connected, a vacuum field
has non-zero circulation around a closed loop. -/
theorem wire_circulation_two_pi_ne_zero :
    lineIntegral wireField unitCircle 0 (2 * Real.pi) ≠ 0 := by
  rw [wire_circulation_two_pi]
  positivity

/-! ## A torus section in a simply connected region -/

/-- Major radius profile of the circular torus section: `R = 3 + cos θ`. -/
noncomputable def torusR (θ _φ : ℝ) : ℝ := 3 + Real.cos θ

/-- Height profile of the circular torus section: `z = sin θ`. -/
noncomputable def torusZ (θ _φ : ℝ) : ℝ := Real.sin θ

/-- The poloidal loop of the section at `φ₀ = 0` is the circle of radius `1` about `(3, 0, 0)`
in the plane `y = 0`. -/
theorem torus_poloidalLoop (θ : ℝ) :
    poloidalLoop torusR torusZ 0 θ = WithLp.toLp 2 ![3 + Real.cos θ, 0, Real.sin θ] := by
  simp [poloidalLoop, cylPoint, torusR, torusZ]

/-- The section lies in the bent region `z < x²`. -/
theorem torus_mem (θ : ℝ) : poloidalLoop torusR torusZ 0 θ ∈ bentOpens := by
  rw [torus_poloidalLoop]
  change Real.sin θ < (3 + Real.cos θ) ^ 2
  nlinarith [Real.sin_le_one θ, Real.neg_one_le_cos θ]

/-- The section is a `C¹` loop. -/
theorem torus_contDiff : ContDiff ℝ 1 (poloidalLoop torusR torusZ 0) :=
  contDiff_poloidalLoop (by unfold torusR; fun_prop) (by unfold torusZ; fun_prop)

/-- The section closes up. -/
theorem torus_closed :
    poloidalLoop torusR torusZ 0 Real.pi = poloidalLoop torusR torusZ 0 (-Real.pi) := by
  simp [torus_poloidalLoop]

/-- The hyperbolic field is a vacuum field on the bent region. -/
theorem hyperbolic_vacuum_bent :
    VacuumField (bentOpens : Set Space) (fun y => hyperbolicField y) :=
  ⟨isOpen_bentSet, hyperbolic_gradient_vacuum.contDiffOn.mono (Set.subset_univ _),
    fun x _ => hyperbolic_gradient_vacuum.div_eq_zero x (Set.mem_univ x),
    fun x _ => hyperbolic_gradient_vacuum.curl_eq_zero x (Set.mem_univ x)⟩

/-- **Accepted case**: in the simply connected bent region the hyperbolic vacuum field has zero
circulation around the torus section. -/
theorem hyperbolic_poloidalCirculation :
    poloidalCirculation (fun y => hyperbolicField y) torusR torusZ 0 = 0 :=
  hyperbolic_vacuum_bent.poloidalCirculation_eq_zero_of_simplyConnected torus_mem torus_contDiff
    torus_closed

/-- **Accepted case**: so it carries no net current through the section, for every `μ₀`. -/
theorem hyperbolic_loopCurrent (μ₀ : ℝ) :
    loopCurrent μ₀ (fun y => hyperbolicField y) torusR torusZ 0 = 0 :=
  hyperbolic_vacuum_bent.loopCurrent_eq_zero_of_simplyConnected μ₀ torus_mem torus_contDiff
    torus_closed

/-- **Period check**: the de Rham period of the hyperbolic 1-form on the class of the torus
section is `0`, by `poloidalCirculation_eq_periodHom`. -/
theorem hyperbolic_period :
    periodHom (onOpens bentOpens fun y => flat (hyperbolicField y)) (poloidalCurve torus_mem 0)
      (Additive.ofMul (.of (.mk (poloidalPath torus_mem torus_contDiff.continuous torus_closed))))
      = 0 := by
  rw [← poloidalCirculation_eq_periodHom
    (hyperbolic_vacuum_bent.contDiffOn.of_le (by norm_num)) hyperbolic_vacuum_bent.curl_eq_zero
    torus_mem torus_contDiff torus_closed]
  exact hyperbolic_poloidalCirculation

end PlasmaLean.Sanity.FormLoopCurrent
