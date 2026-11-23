/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormPeriods

/-!
# The Ampère loop current of the stellarator contract as a de Rham period

The contract layer defines the net toroidal current through the poloidal loop of a torus by
`loopCurrent μ₀ B R z φ₀ = poloidalCirculation B R z φ₀ / μ₀`, where the circulation is the line
integral over `θ ∈ [-π, π]`. `periodHom_onOpens_flat` identifies a de Rham period with a
circulation over `[0, 1]`. This file closes the gap between the two parametrisations.

* `lineIntegral_comp_affine`: the line integral does not change under an affine change of
  parameter. No hypothesis on the field or the curve.
* `poloidalCurve`, `poloidalPath`: the poloidal loop, traversed once for `t ∈ [0, 1]`, as a curve
  and as a loop in an open region `U` that contains it.
* `poloidalCirculation_eq_periodHom`: for a `C¹` curl-free field on `U`, the poloidal
  circulation is the period of `B♭` on the class of `poloidalPath`.
* `loopCurrent_eq_periodHom_div`: so the loop current is that period divided by `μ₀`.
* `VacuumField.poloidalCirculation_eq_zero_of_simplyConnected`,
  `VacuumField.loopCurrent_eq_zero_of_simplyConnected`: a vacuum field on a simply connected
  region carries no net current through a poloidal loop in the region. These are proved from
  the scalar potential (`VacuumField.exists_scalarPotential_of_simplyConnected` and the
  fundamental theorem for line integrals), not from the period.

Restrictions of this file: the poloidal loop is required to lie in `U` and to be `C¹` for
every value of the parameter, not only on `[-π, π]`, and the simply connected corollary is not
derived from the period. Both are removed in `Theory/Fields/FormLoopCurrentInterval`. Nothing
is said about loops that are only piecewise `C¹`.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped Manifold RealInnerProductSpace

/-- **Affine reparametrisation of a line integral.** Traversing `γ` over `[a, b]` at the constant
rate `b - a` for `t ∈ [0, 1]` gives the same line integral. No regularity is assumed. -/
theorem lineIntegral_comp_affine (B : Space → Space) (γ : ℝ → Space) (a b : ℝ) :
    lineIntegral B (fun t => γ (a + (b - a) * t)) 0 1 = lineIntegral B γ a b := by
  have hd (t : ℝ) : deriv (fun t => γ (a + (b - a) * t)) t
      = (b - a) • deriv γ (a + (b - a) * t) := by
    rw [← deriv_comp_const_add (f := γ) (a := a), ← deriv_comp_mul_left (f := fun x => γ (a + x))]
  have h := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (f := fun s => ⟪B (γ s), deriv γ s⟫) (b - a) a
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul] at h
  rw [lineIntegral, lineIntegral, ← h, ← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  rw [hd, inner_smul_right]

section Poloidal

variable {U : Opens Space} {B : Space → Space} {R z : ℝ → ℝ → ℝ} {φ₀ : ℝ}

/-- The poloidal loop of the torus `(R, z)` at toroidal angle `φ₀`, traversed once for
`t ∈ [0, 1]` (so `θ = -π + 2π t`), as a curve in an open region `U` that contains it. -/
noncomputable def poloidalCurve (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U) (t : ℝ) : U :=
  ⟨poloidalLoop R z φ₀ (-Real.pi + (Real.pi - -Real.pi) * t), hU _⟩

/-- The value of `poloidalCurve` as a point of space. -/
@[simp] theorem coe_poloidalCurve (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U) (t : ℝ) :
    (poloidalCurve hU t : Space) = poloidalLoop R z φ₀ (-Real.pi + (Real.pi - -Real.pi) * t) :=
  rfl

/-- The reparametrised poloidal loop is `C¹` when the poloidal loop is. -/
theorem contDiff_poloidalCurve (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀)) :
    ContDiff ℝ 1 fun t => (poloidalCurve hU t : Space) :=
  hγ.comp (by fun_prop)

/-- A closed poloidal loop gives a closed reparametrised curve. -/
theorem poloidalCurve_one (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    poloidalCurve hU 1 = poloidalCurve hU 0 := by
  apply Subtype.ext
  simp only [coe_poloidalCurve, mul_one, mul_zero, add_zero, add_sub_cancel]
  exact hclosed

/-- The poloidal loop as a loop in the open region `U`, based at its point `θ = -π`. It needs
the loop to be continuous, to lie in `U` and to close up. -/
noncomputable def poloidalPath (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hcont : Continuous (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    Path (poloidalCurve hU 0) (poloidalCurve hU 0) where
  toFun t := poloidalCurve hU t
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact hcont.comp (by fun_prop)
  source' := rfl
  target' := by simpa using poloidalCurve_one hU hclosed

/-- The circulation of `B` along the reparametrised poloidal loop over `[0, 1]` is the poloidal
circulation of the contract. No regularity is assumed. -/
theorem lineIntegral_poloidalCurve (B : Space → Space) (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U) :
    lineIntegral B (fun t => (poloidalCurve hU t : Space)) 0 1 = poloidalCirculation B R z φ₀ :=
  lineIntegral_comp_affine B (poloidalLoop R z φ₀) (-Real.pi) Real.pi

/-- **The poloidal circulation is a de Rham period.** For a field `B` that is `C¹` and curl-free
on the open region `U`, and a `C¹` closed poloidal loop in `U`, the circulation of `B` around
the loop is the period of the closed 1-form `B♭` on the homotopy class of the loop. -/
theorem poloidalCirculation_eq_periodHom (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    poloidalCirculation B R z φ₀
      = periodHom (onOpens U fun y => flat (B y)) (poloidalCurve hU 0)
          (Additive.ofMul (.of (.mk (poloidalPath hU hγ.continuous hclosed)))) := by
  rw [periodHom_onOpens_flat hB hcurl (contDiff_poloidalCurve hU hγ) (fun _ => rfl),
    lineIntegral_poloidalCurve]

/-- **The Ampère loop current is a de Rham period divided by `μ₀`.** -/
theorem loopCurrent_eq_periodHom_div (μ₀ : ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    loopCurrent μ₀ B R z φ₀
      = periodHom (onOpens U fun y => flat (B y)) (poloidalCurve hU 0)
          (Additive.ofMul (.of (.mk (poloidalPath hU hγ.continuous hclosed)))) / μ₀ := by
  rw [loopCurrent, poloidalCirculation_eq_periodHom hB hcurl hU hγ hclosed]

/-- **Topology forbids a net current.** A vacuum field on a simply connected open region has
zero circulation around every `C¹` closed poloidal loop in the region. The proof uses the scalar
potential of the field on the region. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.poloidalCirculation_eq_zero_of_simplyConnected
    [SimplyConnectedSpace U] (h : VacuumField U B) (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    poloidalCirculation B R z φ₀ = 0 := by
  obtain ⟨φ, hφ, hgrad⟩ := h.exists_scalarPotential_of_simplyConnected
  have hnhds (t : ℝ) : (U : Set Space) ∈ 𝓝 (poloidalLoop R z φ₀ t) := U.isOpen.mem_nhds (hU t)
  refine lineIntegral_eq_zero_of_potential (g := B) (Φ := φ) hγ
    (fun t => (h.contDiffOn.continuousOn.continuousAt (hnhds t))) (fun _ => rfl) (fun t => ?_)
    hclosed.symm
  have hd : DifferentiableAt ℝ φ (poloidalLoop R z φ₀ t) :=
    ((hφ.differentiableOn (by norm_num)) _ (hU t)).differentiableAt (hnhds t)
  have hg := hd.hasGradientAt
  rw [← hgrad _ (hU t)] at hg
  exact hg.hasFDerivAt

/-- **No net toroidal current in a simply connected vacuum region.** -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.loopCurrent_eq_zero_of_simplyConnected
    [SimplyConnectedSpace U] (μ₀ : ℝ) (h : VacuumField U B)
    (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U) (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    loopCurrent μ₀ B R z φ₀ = 0 := by
  rw [loopCurrent, h.poloidalCirculation_eq_zero_of_simplyConnected hU hγ hclosed, zero_div]

end Poloidal

end PlasmaLean.Forms
