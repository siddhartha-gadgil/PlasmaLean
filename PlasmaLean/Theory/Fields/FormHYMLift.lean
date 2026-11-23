/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormContact

/-!
# The Abelian Hermitian–Yang–Mills lift of a vacuum field (anti-self-dual lift)

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, section "A
complex-surface lift that retains the Euclidean metric" (§4 of the note; assessment claim S-13
in `notes/theory/fusion-complex-geometry-assessment.md`, orientation note N-37 in
`notes/theory/holomorphic-lift-orientation-patch.md`).

## Convention (taken from the source)

For a field `B` on a region of `ℝ³` put `α = B♭` and `β = ⋆₃α = ι_B vol` (the flux 2-form). On
`ℝ³ × ℝ` with coordinates `(x₀, x₁, x₂, τ)`, the Euclidean product metric and the orientation
`dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`, the source defines

`ℱ = β - α ∧ dτ`.

Here the form is written for a field of 2-forms `ω` (so `β = ω`, `α = ⋆ω = hodge ω`):
`hymLift ω = π^*ω - π^*(⋆ω) ∧ dτ`, with `π : ℝ³ × ℝ → ℝ³` the projection, the pullback Mathlib's
`compContinuousLinearMap` and the wedge TauCeti's `ContinuousAlternatingMap.wedge`
(`(a ∧ b)(v, w) = a(v) b(w) - a(w) b(v)` on 1-forms). In components (`hymLift_apply`)

`ℱ((u, s), (v, t)) = ω(u, v) - ((⋆ω)(u) t - (⋆ω)(v) s)`.

With the opposite orientation `dτ ∧ dx₀ ∧ dx₁ ∧ dx₂` the same form is self-dual (N-37).

## What is proved

* `extDeriv_hymLift_apply`: `dℱ = π^*(dω) - π^*(d⋆ω) ∧ dτ`, evaluated on three vectors.
* `extDeriv_hymLift_eq_zero_iff`: at every point, `dℱ = 0 ↔ dω = 0 ∧ d(⋆ω) = 0`. No
  differentiability hypothesis is needed (all three exterior derivatives use the Fréchet
  derivative, and the lift is differentiable at `(x, τ)` exactly when `ω` is at `x`).
* `VacuumForm.hymLift_closed`, `hymLift_closed_iff_vacuumForm`: for `ω` of class `C²` on an
  open `Ω`, the lift is closed on `Ω × ℝ` exactly when `ω` is a vacuum form; and the same in
  vector language (`hymLift_closed_of_vacuumField`, `hymLift_closed_iff_vacuumField`).
* `hymLift_isAntiSelfDual`: the lift of every `ω` is anti-self-dual, in the component form
  `ℱ(eᵢ, e_τ) = -ℱ(eⱼ, eₖ)` for `(i, j, k)` cyclic (`IsAntiSelfDual`).

## What is not formalized

* The quotient by `τ ↦ τ + ℓ`: the source works on `Ω × (ℝ/ℓℤ)`. The lift does not depend on
  `τ` (`hymLift_tau_indep`), so it descends to the circle; the quotient manifold is not built.
* A Hodge star operator on 2-forms of `ℝ⁴`: `IsAntiSelfDual` is the component form of
  `⋆₄ℱ = -ℱ` for the stated metric and orientation, written by hand; it is not derived from a
  general star.
* The complex structure, the type `(1,1)` and primitivity statements, the line bundle and its
  Chern class, the energy identity `∫|ℱ|² = 2ℓ ∫|B|²` and Yang–Mills minimality.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix
open scoped RealInnerProductSpace

/-- The lift space `ℝ³ × ℝ`: physical space with one auxiliary coordinate `τ`. -/
abbrev LiftSpace := Space × ℝ

/-- Constant-coefficient real `k`-forms on the lift space. -/
abbrev LiftForm (k : ℕ) := LiftSpace [⋀^Fin k]→L[ℝ] ℝ

/-- The 1-form `dτ` on the lift space. -/
def dTau : LiftForm 1 :=
  ContinuousAlternatingMap.ofSubsingleton ℝ LiftSpace ℝ (0 : Fin 1)
    (ContinuousLinearMap.snd ℝ Space ℝ)

/-- `dτ` reads off the auxiliary component. -/
@[simp] theorem dTau_apply (v : Fin 1 → LiftSpace) : dTau v = (v 0).2 := rfl

/-- Two 2-forms on the lift space are equal if they agree on all pairs of vectors written in
components. -/
theorem liftForm2_ext {f g : LiftForm 2}
    (h : ∀ (u v : Space) (s t : ℝ), f ![(u, s), (v, t)] = g ![(u, s), (v, t)]) : f = g := by
  ext w
  have e : w = ![((w 0).1, (w 0).2), ((w 1).1, (w 1).2)] := by
    funext i; fin_cases i <;> rfl
  rw [e]
  exact h _ _ _ _

/-- **The lift at one point**: `π^*b - π^*(⋆b) ∧ dτ` for a 2-form `b` on `ℝ³`, where `π` is the
projection `ℝ³ × ℝ → ℝ³` and the wedge is TauCeti's. -/
noncomputable def hymLiftAt (b : Form 2) : LiftForm 2 :=
  b.compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ) -
    (ContinuousAlternatingMap.wedge
      ((hodge b).compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ)) dTau : LiftForm 2)

/-- **Evaluation of the lift** on two vectors `(u, s)`, `(v, t)`:
`b(u, v) - ((⋆b)(u) t - (⋆b)(v) s)`. -/
theorem hymLiftAt_apply (b : Form 2) (u v : Space) (s t : ℝ) :
    hymLiftAt b ![(u, s), (v, t)] = b ![u, v] - (hodge b ![u] * t - hodge b ![v] * s) := by
  have e : ((Prod.fst : LiftSpace → Space) ∘ ![(u, s), (v, t)]) = ![u, v] := by
    funext i; fin_cases i <;> rfl
  have e1 (a : Space) (r : ℝ) :
      ((Prod.fst : LiftSpace → Space) ∘ ![(a, r)]) = ![a] := by
    funext i; fin_cases i; rfl
  simp [hymLiftAt, ContinuousAlternatingMap.compContinuousLinearMap_apply, e, e1]

/-- The lift at one point is additive. -/
theorem hymLiftAt_add (a b : Form 2) : hymLiftAt (a + b) = hymLiftAt a + hymLiftAt b := by
  apply liftForm2_ext
  intro u v s t
  simp only [ContinuousAlternatingMap.add_apply, hymLiftAt_apply, map_add]
  ring

/-- The lift at one point commutes with scalar multiplication. -/
theorem hymLiftAt_smul (c : ℝ) (b : Form 2) : hymLiftAt (c • b) = c • hymLiftAt b := by
  apply liftForm2_ext
  intro u v s t
  simp only [ContinuousAlternatingMap.smul_apply, hymLiftAt_apply, map_smul, smul_eq_mul]
  ring

/-- The lift at one point as a continuous linear map `Form 2 →L[ℝ] LiftForm 2`. -/
noncomputable def hymLiftCLM : Form 2 →L[ℝ] LiftForm 2 :=
  (LinearMap.toContinuousLinearMap
      ({ toFun := fun v => hymLiftAt (flux v)
         map_add' := fun a b => by rw [map_add, hymLiftAt_add]
         map_smul' := fun c a => by rw [map_smul, hymLiftAt_smul]; rfl } :
        Space →ₗ[ℝ] LiftForm 2)) ∘L
    (flux.toContinuousLinearEquiv.symm : Form 2 →L[ℝ] Space)

/-- `hymLiftCLM` is `hymLiftAt`. -/
@[simp] theorem hymLiftCLM_apply (b : Form 2) : hymLiftCLM b = hymLiftAt b := by
  simp [hymLiftCLM]

/-- Restriction of a form on the lift space to the slice `τ = const`, as a continuous linear
map. It is a left inverse of the lift. -/
noncomputable def sliceCLM : LiftForm 2 →L[ℝ] Form 2 :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ Space ℝ)

/-- The slice of the lift of `b` is `b`. -/
theorem sliceCLM_hymLiftAt (b : Form 2) : sliceCLM (hymLiftAt b) = b := by
  ext w
  have e : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
  have e' : (⇑(ContinuousLinearMap.inl ℝ Space ℝ) ∘ w) = ![(w 0, 0), (w 1, 0)] := by
    funext i; fin_cases i <;> rfl
  rw [sliceCLM, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, e', hymLiftAt_apply]
  conv_rhs => rw [e]
  simp

/-- **The lifted 2-form** `F = π^*ω - π^*(⋆ω) ∧ dτ` of a field of 2-forms `ω` on `ℝ³`. It does
not depend on `τ`. -/
noncomputable def hymLift (w : Space → Form 2) (p : LiftSpace) : LiftForm 2 := hymLiftAt (w p.1)

/-- **Evaluation of the lifted form** on two vectors `(u, s)`, `(v, t)`. -/
theorem hymLift_apply (w : Space → Form 2) (x u v : Space) (τ s t : ℝ) :
    hymLift w (x, τ) ![(u, s), (v, t)] =
      w x ![u, v] - (hodge (w x) ![u] * t - hodge (w x) ![v] * s) :=
  hymLiftAt_apply _ _ _ _ _

/-- The lift of a flux form in vector language: `F((u,s),(v,t)) = det(B,u,v) - (⟪B,u⟫ t -
⟪B,v⟫ s)`. -/
theorem hymLift_fluxField_apply (B : Space → Space) (x u v : Space) (τ s t : ℝ) :
    hymLift (fluxField B) (x, τ) ![(u, s), (v, t)] =
      volForm ![B x, u, v] - (⟪B x, u⟫ * t - ⟪B x, v⟫ * s) := by
  rw [hymLift_apply, fluxField_apply, hodge_flux, flux_apply]
  rfl

/-- The lifted form does not depend on the auxiliary coordinate. -/
theorem hymLift_tau_indep (w : Space → Form 2) (x : Space) (τ τ' : ℝ) :
    hymLift w (x, τ) = hymLift w (x, τ') := rfl

/-- The derivative of the lifted form, with no differentiability hypothesis: both sides vanish
where `w` is not differentiable, because the lift has the left inverse `sliceCLM`. -/
theorem fderiv_hymLift (w : Space → Form 2) (x : Space) (τ : ℝ) :
    fderiv ℝ (hymLift w) (x, τ) =
      hymLiftCLM ∘L fderiv ℝ w x ∘L ContinuousLinearMap.fst ℝ Space ℝ := by
  by_cases h : DifferentiableAt ℝ w x
  · have h1 : HasFDerivAt (fun p : LiftSpace => w p.1)
        (fderiv ℝ w x ∘L ContinuousLinearMap.fst ℝ Space ℝ) (x, τ) :=
      HasFDerivAt.comp (x, τ) (f := Prod.fst) (g := w) h.hasFDerivAt hasFDerivAt_fst
    have h2 := hymLiftCLM.hasFDerivAt.comp (x, τ) h1
    have e : hymLift w = hymLiftCLM ∘ fun p : LiftSpace => w p.1 := by
      funext p; simp [hymLift]
    rw [e]
    exact h2.fderiv
  · have h' : ¬ DifferentiableAt ℝ (hymLift w) (x, τ) := by
      intro hd
      apply h
      have e : w = fun y => sliceCLM (hymLift w (y, τ)) := by
        funext y; rw [hymLift, sliceCLM_hymLiftAt]
      have hm : DifferentiableAt ℝ (fun y : Space => ((y, τ) : LiftSpace)) x :=
        differentiableAt_id.prodMk (differentiableAt_const τ)
      have h3 : DifferentiableAt ℝ (fun y : Space => hymLift w (y, τ)) x :=
        DifferentiableAt.comp (g := hymLift w) (f := fun y : Space => ((y, τ) : LiftSpace)) x
          hd hm
      rw [e]
      exact DifferentiableAt.comp (g := sliceCLM) x sliceCLM.differentiableAt h3
    rw [fderiv_zero_of_not_differentiableAt h', fderiv_zero_of_not_differentiableAt h]
    simp

/-- The Hodge star as a continuous linear equivalence. -/
noncomputable def hodgeCLE : Form 2 ≃L[ℝ] Form 1 :=
  flux.toContinuousLinearEquiv.symm.trans flat.toContinuousLinearEquiv

/-- `hodgeCLE` is `hodge`. -/
@[simp] theorem hodgeCLE_apply (b : Form 2) : hodgeCLE b = hodge b := rfl

/-- The derivative of `⋆ω`, with no differentiability hypothesis. -/
theorem fderiv_hodge (w : Space → Form 2) (x : Space) :
    fderiv ℝ (fun y => hodge (w y)) x = (hodgeCLE : Form 2 →L[ℝ] Form 1) ∘L fderiv ℝ w x :=
  hodgeCLE.comp_fderiv

/-- **The exterior derivative of the lifted form** on three vectors, with no differentiability
hypothesis: the part without `dτ` is `dω`, the part with `dτ` is `-d(⋆ω) ∧ dτ`. -/
theorem extDeriv_hymLift_apply (w : Space → Form 2) (x : Space) (τ : ℝ) (u₀ u₁ u₂ : Space)
    (s₀ s₁ s₂ : ℝ) :
    extDeriv (hymLift w) (x, τ) ![(u₀, s₀), (u₁, s₁), (u₂, s₂)] =
      extDeriv w x ![u₀, u₁, u₂] -
        (s₀ * extDeriv (fun y => hodge (w y)) x ![u₁, u₂] -
          s₁ * extDeriv (fun y => hodge (w y)) x ![u₀, u₂] +
          s₂ * extDeriv (fun y => hodge (w y)) x ![u₀, u₁]) := by
  have r0 : Fin.removeNth (0 : Fin 3) ![((u₀, s₀) : LiftSpace), (u₁, s₁), (u₂, s₂)]
      = ![(u₁, s₁), (u₂, s₂)] := by ext i <;> fin_cases i <;> rfl
  have r1 : Fin.removeNth (1 : Fin 3) ![((u₀, s₀) : LiftSpace), (u₁, s₁), (u₂, s₂)]
      = ![(u₀, s₀), (u₂, s₂)] := by ext i <;> fin_cases i <;> rfl
  have r2 : Fin.removeNth (2 : Fin 3) ![((u₀, s₀) : LiftSpace), (u₁, s₁), (u₂, s₂)]
      = ![(u₀, s₀), (u₁, s₁)] := by ext i <;> fin_cases i <;> rfl
  have q0 : Fin.removeNth (0 : Fin 3) ![u₀, u₁, u₂] = ![u₁, u₂] := by
    ext i; fin_cases i <;> rfl
  have q1 : Fin.removeNth (1 : Fin 3) ![u₀, u₁, u₂] = ![u₀, u₂] := by
    ext i; fin_cases i <;> rfl
  have q2 : Fin.removeNth (2 : Fin 3) ![u₀, u₁, u₂] = ![u₀, u₁] := by
    ext i; fin_cases i <;> rfl
  have p0 (a b : Space) : Fin.removeNth (0 : Fin 2) ![a, b] = ![b] := by
    ext i; fin_cases i; rfl
  have p1 (a b : Space) : Fin.removeNth (1 : Fin 2) ![a, b] = ![a] := by
    ext i; fin_cases i; rfl
  simp [extDeriv, fderiv_hymLift, fderiv_hodge,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
    r0, r1, r2, q0, q1, q2, p0, p1, hymLiftAt_apply]
  ring

/-- **Closedness of the lift is the pair of vacuum equations.** At every point `(x, τ)`,
`dF = 0` exactly when `dω = 0` (Gauss) and `d(⋆ω) = 0` (Ampère with no current) at `x`. No
differentiability hypothesis is needed: where `ω` is not differentiable all three exterior
derivatives are `0` by Mathlib's convention. -/
theorem extDeriv_hymLift_eq_zero_iff (w : Space → Form 2) (x : Space) (τ : ℝ) :
    extDeriv (hymLift w) (x, τ) = 0 ↔
      extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  constructor
  · intro h
    have h1 : extDeriv w x = 0 := by
      ext v
      have e : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
      have := extDeriv_hymLift_apply w x τ (v 0) (v 1) (v 2) 0 0 0
      rw [h] at this
      rw [e]
      simpa using this.symm
    refine ⟨h1, ?_⟩
    ext v
    have e : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    have := extDeriv_hymLift_apply w x τ 0 (v 0) (v 1) 1 0 0
    rw [h, h1] at this
    rw [e]
    simpa using this.symm
  · rintro ⟨h1, h2⟩
    ext v
    have e : v = ![((v 0).1, (v 0).2), ((v 1).1, (v 1).2), ((v 2).1, (v 2).2)] := by
      funext i; fin_cases i <;> rfl
    rw [e, extDeriv_hymLift_apply, h1, h2]
    simp

/-- **A vacuum form has a closed lift** on `Ω × ℝ`. -/
theorem VacuumForm.hymLift_closed {Ω : Set Space} {w : Space → Form 2} (h : VacuumForm Ω w) :
    ∀ p ∈ Ω ×ˢ (Set.univ : Set ℝ), extDeriv (hymLift w) p = 0 := by
  rintro ⟨x, τ⟩ ⟨hx, -⟩
  exact (extDeriv_hymLift_eq_zero_iff w x τ).2 ⟨h.closed x hx, h.coclosed x hx⟩

/-- **The lift is closed on `Ω × ℝ` exactly for vacuum forms**, for `ω` of class `C²` on an open
set `Ω`. -/
theorem hymLift_closed_iff_vacuumForm {Ω : Set Space} {w : Space → Form 2} (hΩ : IsOpen Ω)
    (hw : ContDiffOn ℝ 2 w Ω) :
    (∀ p ∈ Ω ×ˢ (Set.univ : Set ℝ), extDeriv (hymLift w) p = 0) ↔ VacuumForm Ω w := by
  refine ⟨fun h => ⟨hΩ, hw, fun x hx => ?_, fun x hx => ?_⟩, fun h => h.hymLift_closed⟩
  · exact ((extDeriv_hymLift_eq_zero_iff w x 0).1 (h (x, 0) ⟨hx, Set.mem_univ _⟩)).1
  · exact ((extDeriv_hymLift_eq_zero_iff w x 0).1 (h (x, 0) ⟨hx, Set.mem_univ _⟩)).2

/-- **A vacuum field has a closed lift** (vector language): the lift of `ι_B vol` is closed on
`Ω × ℝ`. -/
theorem hymLift_closed_of_vacuumField {Ω : Set Space} {B : Space → Space}
    (h : VacuumField Ω B) :
    ∀ p ∈ Ω ×ˢ (Set.univ : Set ℝ), extDeriv (hymLift (fluxField B)) p = 0 :=
  (vacuumForm_flux_iff.2 h).hymLift_closed

/-- **Vector-language converse**: for `B` of class `C²` on an open set `Ω`, the lift of its flux
form is closed on `Ω × ℝ` exactly when `B` is a vacuum field. -/
theorem hymLift_closed_iff_vacuumField {Ω : Set Space} {B : Space → Space} (hΩ : IsOpen Ω)
    (hB : ContDiffOn ℝ 2 B Ω) :
    (∀ p ∈ Ω ×ˢ (Set.univ : Set ℝ), extDeriv (hymLift (fluxField B)) p = 0) ↔
      VacuumField Ω B := by
  rw [← vacuumForm_flux_iff]
  exact hymLift_closed_iff_vacuumForm hΩ (flux.toContinuousLinearEquiv.comp_contDiffOn_iff.2 hB)

/-! ## Anti-self-duality -/

/-- **Anti-self-duality in components.** For the Euclidean metric on `ℝ³ × ℝ` and the
orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`, the Hodge star on 2-forms is determined by
`(⋆F)(eᵢ, e_τ) = F(eⱼ, eₖ)` and `(⋆F)(eⱼ, eₖ) = F(eᵢ, e_τ)` for `(i, j, k)` a cyclic permutation
of `(0, 1, 2)`. So `⋆F = -F` says `F(eᵢ, e_τ) = -F(eⱼ, eₖ)` for the three cyclic triples. -/
def IsAntiSelfDual (F : LiftForm 2) : Prop :=
  F ![(coordVec 0, 0), (0, 1)] = -F ![(coordVec 1, 0), (coordVec 2, 0)] ∧
  F ![(coordVec 1, 0), (0, 1)] = -F ![(coordVec 2, 0), (coordVec 0, 0)] ∧
  F ![(coordVec 2, 0), (0, 1)] = -F ![(coordVec 0, 0), (coordVec 1, 0)]

/-- The Hodge star of a 2-form on `ℝ³` on the unit vectors. -/
theorem hodge_apply_coordVec (b : Form 2) :
    hodge b ![coordVec 0] = b ![coordVec 1, coordVec 2] ∧
    hodge b ![coordVec 1] = b ![coordVec 2, coordVec 0] ∧
    hodge b ![coordVec 2] = b ![coordVec 0, coordVec 1] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hodge, flat_apply, flux_symm_eq, coordVec, EuclideanSpace.inner_single_right]

/-- **The lift is anti-self-dual at every point, for every 2-form** (no field equation is
used). -/
theorem hymLiftAt_isAntiSelfDual (b : Form 2) : IsAntiSelfDual (hymLiftAt b) := by
  obtain ⟨h0, h1, h2⟩ := hodge_apply_coordVec b
  have z (a : Space) : b ![a, 0] = 0 := b.map_coord_zero 1 rfl
  have z' : hodge b ![0] = 0 := (hodge b).map_coord_zero 0 rfl
  refine ⟨?_, ?_, ?_⟩ <;> rw [hymLiftAt_apply, hymLiftAt_apply] <;> simp [h0, h1, h2, z, z']

/-- The lifted form is anti-self-dual at every point. -/
theorem hymLift_isAntiSelfDual (w : Space → Form 2) (p : LiftSpace) :
    IsAntiSelfDual (hymLift w p) :=
  hymLiftAt_isAntiSelfDual _

end PlasmaLean.Forms
