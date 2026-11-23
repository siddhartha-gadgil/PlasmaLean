/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormBridges
public import TauCeti.Analysis.Calculus.DifferentialForm.LieDeriv
public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare

/-!
# Lie derivatives and potentials for the form kernel (TauCeti v4.36.0)

`Kernel/Forms` and `Theory/Fields/FormBridges` write the magnetic field as a 2-form `ω` on
`ℝ³` and use Mathlib's exterior derivative. TauCeti v4.36.0 adds, on the same carrier (forms
on a normed space), the Lie derivative with Cartan's formula and the Poincaré lemma on
star-convex sets. This file uses them for two statements that the earlier files could not make.

## Lie derivative (note N-43, step 1 of the weak-quasisymmetry construction)

* `lieDerivForm_eq_zero_of_interior`: if `ω` is closed at `x` and `ι_ξ ω = -dψ` near `x` with
  `ψ` of class `C²`, then `L_ξ ω = 0` at `x` (Cartan's formula and `d ∘ d = 0`).
* `FormWeakQS.lieDerivForm_eq_zero`, `WeakQS.lieDerivForm_flux_eq_zero`: the flux form of a
  weakly quasisymmetric, divergence-free field is invariant under the generator.
* `lieDerivForm_flux`: `L_ξ(ι_B vol) = ι_{[ξ, B] + (div ξ) B} vol`.
* `WeakQS.lieBracket_eq_zero`: hence `[ξ, B] = 0` in vector language, under extra hypotheses
  that are not part of `WeakQS`: the set `T` is open, `B` is differentiable and divergence-free
  on `T`, and the potential `ψ` is of class `C²` on `T`. (The same hypotheses are needed for
  `WeakQS.lieDerivForm_flux_eq_zero`.)

## Potentials (topology of the region)

* `VacuumForm.exists_scalarPotential`: on an open star-convex region a vacuum field is a
  gradient, `⋆ω = dφ`.
* `VacuumForm.exists_vectorPotential`: there is a 1-form `A` with `dA = ω`.
* `VacuumField.exists_scalarPotential`, `VacuumField.exists_vectorPotential`: the same in
  vector language, `B = ∇φ` and `B = ∇ × A`. `VacuumField.exists_vectorPotential` does not
  record the regularity of `A`; `VacuumField.exists_vectorPotential_contDiffOn` does (`A` is
  of class `C²` on the region).

Star-convexity is a hypothesis on the topology of the region. On a region that is not simply
connected (a solid torus, the complement of a wire) a vacuum field need not be a gradient: that
is the term `G dϑ` in the class `G dϑ + dF` of note N-42 (S-2). No such counterexample is
proved in this file; the wire field is one (`wireField_no_potential` in
`Sanity/FormTopology`).
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields
open TauCeti Topology

/-! ## `d(dψ) = 0` and the Lie derivative -/

/-- `d(-ψ) = -dψ`, with no differentiability hypothesis. -/
theorem formGrad_neg (ψ : Space → ℝ) (x : Space) :
    formGrad (fun y => -ψ y) x = -formGrad ψ x := by
  ext w
  simp [formGrad_apply, fderiv_fun_neg]

/-- **`d(dψ) = 0`** at a point where `ψ` is of class `C²`. -/
theorem extDeriv_formGrad_eq_zero {ψ : Space → ℝ} {x : Space} (hψ : ContDiffAt ℝ 2 ψ x) :
    extDeriv (formGrad ψ) x = 0 := by
  have h0 : formGrad ψ =
      extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ Space (Fin 0) (ψ y)) :=
    funext fun y => (extDeriv_formGrad ψ y).symm
  rw [h0]
  refine extDeriv_extDeriv_apply (r := 2) ?_ (by simp)
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Space ℝ (Fin 0)).contDiff.contDiffAt.comp x hψ

/-- **Invariance of a closed 2-form under a Hamiltonian-type generator.** If `ω` is closed at
`x` and `ι_ξ ω = -dψ` near `x` with `ψ` of class `C²`, then `L_ξ ω = 0` at `x`. This is Cartan's
formula `L_ξ ω = ι_ξ dω + d(ι_ξ ω)` together with `d ∘ d = 0`. -/
theorem lieDerivForm_eq_zero_of_interior {ω : Space → Form 2} {ξ : Space → Space}
    {ψ : Space → ℝ} {x : Space} (hω : DifferentiableAt ℝ ω x) (hξ : DifferentiableAt ℝ ξ x)
    (hclosed : extDeriv ω x = 0)
    (hint : ∀ᶠ y in 𝓝 x, (ω y).curryLeft (ξ y) = -formGrad ψ y)
    (hψ : ContDiffAt ℝ 2 ψ x) : lieDerivForm ξ ω x = 0 := by
  rw [lieDerivForm_eq_curryLeft_extDeriv_add hω hξ, hclosed]
  have h1 : (fun y => (ω y).curryLeft (ξ y)) =ᶠ[𝓝 x] formGrad (fun y => -ψ y) := by
    filter_upwards [hint] with y hy
    rw [hy, formGrad_neg]
  rw [h1.extDeriv_eq, extDeriv_formGrad_eq_zero hψ.neg]
  simp

/-- **The flux form of a weakly quasisymmetric field is invariant under the generator**:
`L_ξ ω = 0` on an open set `T`, when `ω` is differentiable and closed (`∇ · B = 0`) on `T`
and the potential is of class `C²` there. -/
theorem FormWeakQS.lieDerivForm_eq_zero
    {ω : Space → Form 2} {ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (h : FormWeakQS ω ξ ψ T) (hT : IsOpen T) (hω : ∀ x ∈ T, DifferentiableAt ℝ ω x)
    (hclosed : ∀ x ∈ T, extDeriv ω x = 0) (hψ : ∀ x ∈ T, ContDiffAt ℝ 2 ψ x)
    {x : Space} (hx : x ∈ T) : lieDerivForm ξ ω x = 0 :=
  lieDerivForm_eq_zero_of_interior (hω x hx) (h.xi_diff x hx) (hclosed x hx)
    (Filter.eventually_of_mem (hT.mem_nhds hx) fun y hy => h.interior y hy) (hψ x hx)

/-- Vector-language form of `FormWeakQS.lieDerivForm_eq_zero`: for a weakly quasisymmetric
field `B` that is differentiable and divergence-free on the open set `T`, with potential of
class `C²`, the flux form `ι_B vol` is invariant under the generator `ξ`. -/
theorem _root_.PlasmaLean.Fields.WeakQS.lieDerivForm_flux_eq_zero
    {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space} (h : WeakQS B ξ ψ T)
    (hT : IsOpen T) (hB : ∀ x ∈ T, DifferentiableAt ℝ B x)
    (hdiv : ∀ x ∈ T, fieldDiv B x = 0) (hψ : ∀ x ∈ T, ContDiffAt ℝ 2 ψ x)
    {x : Space} (hx : x ∈ T) : lieDerivForm ξ (fluxField B) x = 0 := by
  refine (formWeakQS_flux_iff.2 h).lieDerivForm_eq_zero hT (fun y hy => ?_) (fun y hy => ?_) hψ hx
  · exact (flux.toContinuousLinearEquiv.differentiable.differentiableAt).comp y (hB y hy)
  · change extDeriv (fun z => flux (B z)) y = 0
    rw [extDeriv_flux, hdiv y hy, map_zero]

/-! ## The Lie derivative of a flux form and the Lie bracket -/

/-- Components of a linear map applied to a vector, in the Cartesian basis. -/
theorem clm_coords (L : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    L v i = v 0 * L (coordVec 0) i + v 1 * L (coordVec 1) i + v 2 * L (coordVec 2) i := by
  have hv : v = v 0 • coordVec 0 + v 1 • coordVec 1 + v 2 • coordVec 2 := by
    ext j; fin_cases j <;> simp
  conv_lhs => rw [hv]
  simp

/-- **Lie derivative of a flux form**: `L_ξ(ι_B vol) = ι_{[ξ, B] + (div ξ) B} vol`, at every
point and with no differentiability hypothesis (both sides use the Fréchet derivative). Here
`[ξ, B] = DB ξ − Dξ B` is Mathlib's Lie bracket. -/
theorem lieDerivForm_flux (ξ B : Space → Space) (x : Space) :
    lieDerivForm ξ (fluxField B) x =
      flux (VectorField.lieBracket ℝ ξ B x + fieldDiv ξ x • B x) := by
  have hd : fderiv ℝ (fluxField B) x
      = (flux.toContinuousLinearEquiv : Space →L[ℝ] Form 2) ∘L fderiv ℝ B x :=
    flux.toContinuousLinearEquiv.comp_fderiv
  rw [← LinearEquiv.symm_apply_eq, flux_symm_eq]
  set L := fderiv ℝ ξ x with hL
  set M := fderiv ℝ B x with hM
  have c0 := clm_coords L (B x) 0
  have c1 := clm_coords L (B x) 1
  have c2 := clm_coords L (B x) 2
  have u0 (a b c : Space) : Function.update ![a, b] 0 c = ![c, b] := by
    ext i j; fin_cases i <;> simp
  have u1 (a b c : Space) : Function.update ![a, b] 1 c = ![a, c] := by
    ext i j; fin_cases i <;> simp
  ext i
  fin_cases i <;>
    simp [lieDerivForm_apply, hd, Fin.sum_univ_two, u0, u1, flux_apply, volForm_vec,
      fluxField_apply, VectorField.lieBracket, fieldDiv, divOp_apply, ← hL, ← hM, c0, c1, c2] <;>
    ring

/-- **Weak quasisymmetry gives commuting fields**: for a weakly quasisymmetric field `B` that
is differentiable and divergence-free on the open set `T`, with potential of class `C²`, the
generator commutes with the field, `[ξ, B] = 0` on `T`. This is step 1 of note N-43 in vector
language. -/
theorem _root_.PlasmaLean.Fields.WeakQS.lieBracket_eq_zero
    {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space} (h : WeakQS B ξ ψ T)
    (hT : IsOpen T) (hB : ∀ x ∈ T, DifferentiableAt ℝ B x)
    (hdiv : ∀ x ∈ T, fieldDiv B x = 0) (hψ : ∀ x ∈ T, ContDiffAt ℝ 2 ψ x)
    {x : Space} (hx : x ∈ T) : VectorField.lieBracket ℝ ξ B x = 0 := by
  have h0 := h.lieDerivForm_flux_eq_zero hT hB hdiv hψ hx
  rw [lieDerivForm_flux ξ B x] at h0
  have hξ : fieldDiv ξ x = 0 := by
    have := h.div_free x hx
    rwa [← divOp_eq_divergence] at this
  rw [hξ, zero_smul, add_zero] at h0
  exact flux.injective (h0.trans (map_zero flux).symm)

/-! ## Potentials on star-convex regions -/

/-- **Vector potential.** On an open star-convex region a vacuum 2-form is exact:
`ω = dA` for a 1-form `A` of class `C²` that vanishes at the centre. Only Gauss's law
`dω = 0` is used. -/
theorem VacuumForm.exists_vectorPotential {Ω : Set Space}
    {ω : Space → Form 2} (h : VacuumForm Ω ω) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ A : Space → Form 1, ContDiffOn ℝ 2 A Ω ∧ A x₀ = 0 ∧ ∀ x ∈ Ω, extDeriv A x = ω x :=
  hs.exists_contDiffOn_forall_extDeriv_eq h.isOpen (r := 2) (by norm_num)
    (by exact_mod_cast h.contDiffOn) h.closed

/-- **Scalar potential.** On an open star-convex region a vacuum field is a gradient:
`⋆ω = dφ` for a function `φ` of class `C²` that vanishes at the centre. Only Ampère's law
`d(⋆ω) = 0` is used. -/
theorem VacuumForm.exists_scalarPotential {Ω : Set Space}
    {ω : Space → Form 2} (h : VacuumForm Ω ω) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ φ : Space → ℝ, ContDiffOn ℝ 2 φ Ω ∧ φ x₀ = 0 ∧ ∀ x ∈ Ω, formGrad φ x = hodge (ω x) := by
  have hreg : ContDiffOn ℝ ((2 : ℕ∞) : WithTop ℕ∞) (fun y => hodge (ω y)) Ω := by
    have h1 := flux.toContinuousLinearEquiv.symm.contDiff (n := 2) |>.comp_contDiffOn h.contDiffOn
    have h2 := flat.toContinuousLinearEquiv.contDiff (n := 2) |>.comp_contDiffOn h1
    exact_mod_cast h2
  obtain ⟨α, hα, hα0, hd⟩ :=
    hs.exists_contDiffOn_forall_extDeriv_eq h.isOpen (r := 2) (by norm_num) hreg h.coclosed
  let e := ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Space ℝ (Fin 0)
  refine ⟨fun y => e.symm (α y), ?_, ?_, fun x hx => ?_⟩
  · have := e.symm.contDiff (n := 2) |>.comp_contDiffOn hα
    exact_mod_cast this
  · simp [hα0]
  · rw [← hd x hx, ← extDeriv_formGrad]
    congr 1
    funext y
    exact (e.apply_symm_apply (α y))

/-- **Scalar potential, vector language**: a vacuum field on an open star-convex region is
the gradient of a `C²` function, `B = ∇φ`. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.exists_scalarPotential {Ω : Set Space}
    {B : Space → Space} (h : VacuumField Ω B) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ φ : Space → ℝ, ContDiffOn ℝ 2 φ Ω ∧ φ x₀ = 0 ∧ ∀ x ∈ Ω, B x = gradient φ x := by
  obtain ⟨φ, hφ, hφ0, hd⟩ := (vacuumForm_flux_iff.2 h).exists_scalarPotential hs
  refine ⟨φ, hφ, hφ0, fun x hx => ?_⟩
  have := hd x hx
  rw [← flat_gradient, fluxField_apply, hodge, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] at this
  exact (flat.injective this).symm

/-- **Vector potential, vector language**: a vacuum field on an open star-convex region is a
curl, `B = ∇ × A`. The regularity of `A` is not recorded here; see
`VacuumField.exists_vectorPotential_contDiffOn`. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.exists_vectorPotential {Ω : Set Space}
    {B : Space → Space} (h : VacuumField Ω B) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ A : Space → Space, A x₀ = 0 ∧ ∀ x ∈ Ω, B x = fieldCurl A x := by
  obtain ⟨A, -, hA0, hd⟩ := (vacuumForm_flux_iff.2 h).exists_vectorPotential hs
  refine ⟨fun y => flat.symm (A y), by simp [hA0], fun x hx => ?_⟩
  have h1 : extDeriv (fun y => flat (flat.symm (A y))) x = flux (B x) := by
    simpa using hd x hx
  rw [extDeriv_flat] at h1
  exact (flux.injective h1).symm

/-- **Vector potential of class `C²`, vector language**: a vacuum field on an open star-convex
region is the curl of a vector field `A` that is of class `C²` on the region and vanishes at
the centre. This is `VacuumField.exists_vectorPotential` with the regularity of `A` kept. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.exists_vectorPotential_contDiffOn {Ω : Set Space}
    {B : Space → Space} (h : VacuumField Ω B) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ A : Space → Space, ContDiffOn ℝ 2 A Ω ∧ A x₀ = 0 ∧ ∀ x ∈ Ω, B x = fieldCurl A x := by
  obtain ⟨A, hA, hA0, hd⟩ := (vacuumForm_flux_iff.2 h).exists_vectorPotential hs
  refine ⟨fun y => flat.symm (A y), ?_, by simp [hA0], fun x hx => ?_⟩
  · exact flat.toContinuousLinearEquiv.symm.contDiff.comp_contDiffOn hA
  · have h1 : extDeriv (fun y => flat (flat.symm (A y))) x = flux (B x) := by
      simpa using hd x hx
    rw [extDeriv_flat] at h1
    exact (flux.injective h1).symm

end PlasmaLean.Forms
