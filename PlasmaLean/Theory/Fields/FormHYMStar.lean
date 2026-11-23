/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMLift
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.TwoForm
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic

/-!
# The Hodge star on 2-forms of `ℝ³ × ℝ` and the anti-self-dual lift

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, section "A
complex-surface lift that retains the Euclidean metric" (assessment claim S-13, orientation
note N-37 in `notes/theory/holomorphic-lift-orientation-patch.md`). This file continues
`Theory/Fields/FormHYMLift`, where anti-self-duality of the lift `ℱ = π^*ω - π^*(⋆₃ω) ∧ dτ` was
a component condition written by hand (`IsAntiSelfDual`) and the quotient by `τ ↦ τ + ℓ` was
not formalized.

## Conventions

* Metric: the product Euclidean metric on `ℝ³ × ℝ`. Orientation: `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`.
* Every 2-form on `ℝ³ × ℝ` is `F = π^*a + π^*e ∧ dτ` with `a(u, v) = F((u,0),(v,0))` (a 2-form
  on `ℝ³`, the spatial part) and `e(u) = F((u,0),(0,1))` (a 1-form on `ℝ³`, the mixed part).
  The wedge is TauCeti's `ContinuousAlternatingMap.wedge`
  (`(α ∧ β)(v, w) = α(v) β(w) - α(w) β(v)` on 1-forms).
* The star is `⋆₄(π^*a + π^*e ∧ dτ) = π^*(⋆₃⁻¹e) + π^*(⋆₃a) ∧ dτ` (`liftStar`), with
  `⋆₃ = hodge : Form 2 ≃ₗ Form 1` of the kernel. Both signs are `+`: on the coordinate forms
  `⋆(dx₁ ∧ dx₂) = dx₀ ∧ dτ` and `⋆(dx₀ ∧ dτ) = dx₁ ∧ dx₂`, and cyclically, because
  `dx₁ ∧ dx₂ ∧ dx₀ ∧ dτ` and `dx₀ ∧ dτ ∧ dx₁ ∧ dx₂` are both the volume form.

## What is proved

* The decomposition `liftParts : LiftForm 2 ≃ₗ[ℝ] Form 2 × Form 1`; `finrank_liftForm2`.
* The star `liftStar : LiftForm 2 ≃ₗ[ℝ] LiftForm 2`, its values on the six coordinate 2-forms
  (`liftStar_dX_wedge_dX`, `liftStar_dX_wedge_dTau`) and on the coordinate planes
  (`liftStar_apply_mixed`, `liftStar_apply_spatial`), and `⋆⋆ = 1` (`liftStar_liftStar`).
* **The star is not only an explicit formula**: `euclidForm_liftStar` identifies it with
  TauCeti's `Orientation.formHodgeStar` (the star characterised by `α ∧ ⋆β = ⟨α, β⟩ vol`) on
  the inner product space `WithLp 2 (ℝ³ × ℝ)` with the orientation of the frame
  `(e₀, e₁, e₂, e_τ)`. Consequences: `wedge_liftStar_apply` (`F ∧ ⋆G = ⟨F, G⟩ vol`),
  `liftInner_eq` (the six coordinate 2-forms are orthonormal), `liftVol_frame`
  (`vol(e₀, e₁, e₂, e_τ) = 1`), and `euclidForm_neg_liftStar` (the star of the opposite
  orientation is `-liftStar`).
* `isAntiSelfDual_iff_liftStar`: the component definition `IsAntiSelfDual F` of
  `FormHYMLift` is `⋆₄F = -F`. Corollaries `liftStar_hymLiftAt`, `liftStar_hymLift`.
* The eigenspaces `selfDualForms`, `antiSelfDualForms`: each has dimension three, they are
  complementary, and the lift is a linear isomorphism of `Form 2` onto the anti-self-dual
  forms (`hymLiftEquiv`; surjectivity is `eq_hymLiftAt_of_liftStar_eq_neg`). The self-dual
  forms are the lifts with the other sign (`sdLiftEquiv`).
* Descent to the circle: the lifted field is periodic in `τ` with every period, and
  `hymLiftCircle ℓ ω : ℝ³ × (ℝ/ℓℤ) → LiftForm 2` is the unique field of forms with
  `hymLiftCircle ℓ ω (x, [τ]) = hymLift ω (x, τ)`. As a rough 2-form on the manifold
  `ℝ³ × AddCircle ℓ` (`hymLiftCircleForm`) its manifold pullback along the covering map is
  `hymLift ω` (`mpullback_hymLiftCircleForm`).

## What is not proved

* In this file, smoothness and closedness of `hymLiftCircleForm` as a form on the manifold
  `ℝ³ × AddCircle ℓ`, and the energy identity `∫|ℱ|² = 2ℓ ∫|B|²`: both are in
  `Theory/Fields/FormHYMCircle`.
* The complex structure, the type `(1,1)` and primitivity statements, the line bundle and its
  Chern class, and Yang–Mills minimality.
* A Hodge star in degrees other than two, or for a metric other than the product Euclidean
  one.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix Module
open scoped RealInnerProductSpace

/-! ## Algebra of 2-forms on the lift space -/

/-- A 2-form on the lift space changes sign when its arguments are exchanged. -/
theorem liftForm2_swap (F : LiftForm 2) (a b : LiftSpace) : F ![a, b] = -F ![b, a] := by
  have h := F.toAlternatingMap.map_swap ![b, a] (show (0 : Fin 2) ≠ 1 by simp)
  have e : ![b, a] ∘ Equiv.swap (0 : Fin 2) 1 = ![a, b] := by
    ext i <;> fin_cases i <;> simp
  rw [e] at h
  exact h

/-- A 2-form on the lift space is additive in its first argument. -/
theorem liftForm2_add_left (F : LiftForm 2) (a a' b : LiftSpace) :
    F ![a + a', b] = F ![a, b] + F ![a', b] :=
  F.toAlternatingMap.map_vecCons_add ![b] a a'

/-- A 2-form on the lift space is homogeneous in its first argument. -/
theorem liftForm2_smul_left (F : LiftForm 2) (c : ℝ) (a b : LiftSpace) :
    F ![c • a, b] = c * F ![a, b] :=
  F.toAlternatingMap.map_vecCons_smul ![b] c a

/-- A 2-form on the lift space is additive in its second argument. -/
theorem liftForm2_add_right (F : LiftForm 2) (a b b' : LiftSpace) :
    F ![a, b + b'] = F ![a, b] + F ![a, b'] := by
  rw [liftForm2_swap, liftForm2_add_left, liftForm2_swap F a b, liftForm2_swap F a b']
  ring

/-- A 2-form on the lift space is homogeneous in its second argument. -/
theorem liftForm2_smul_right (F : LiftForm 2) (c : ℝ) (a b : LiftSpace) :
    F ![a, c • b] = c * F ![a, b] := by
  rw [liftForm2_swap, liftForm2_smul_left, liftForm2_swap F a b]
  ring

/-- A 2-form on the lift space vanishes on a repeated vector. -/
theorem liftForm2_self (F : LiftForm 2) (a : LiftSpace) : F ![a, a] = 0 := by
  have h := liftForm2_swap F a a
  linarith

/-- **Expansion of a 2-form on the lift space** in its spatial values `F((u,0),(v,0))` and its
mixed values `F((u,0),(0,1))`. -/
theorem liftForm2_apply (F : LiftForm 2) (u v : Space) (s t : ℝ) :
    F ![(u, s), (v, t)] =
      F ![(u, 0), (v, 0)] + (F ![(u, 0), (0, 1)] * t - F ![(v, 0), (0, 1)] * s) := by
  have e (a : Space) (r : ℝ) : ((a, r) : LiftSpace) = (a, 0) + r • ((0, 1) : LiftSpace) := by
    ext <;> simp
  rw [e u s, e v t]
  simp only [liftForm2_add_left, liftForm2_add_right, liftForm2_smul_left, liftForm2_smul_right,
    liftForm2_self]
  rw [liftForm2_swap F (0, 1) (v, 0)]
  ring

/-! ## The decomposition `F = π^*a + π^*e ∧ dτ` -/

/-- **The form with given parts**: `π^*a + π^*e ∧ dτ` for a 2-form `a` and a 1-form `e` on
`ℝ³`. -/
noncomputable def ofParts (a : Form 2) (e : Form 1) : LiftForm 2 :=
  a.compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ) +
    (ContinuousAlternatingMap.wedge
      (e.compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ)) dTau : LiftForm 2)

/-- **Evaluation of the form with given parts**: `a(u, v) + (e(u) t - e(v) s)`. -/
theorem ofParts_apply (a : Form 2) (e : Form 1) (u v : Space) (s t : ℝ) :
    ofParts a e ![(u, s), (v, t)] = a ![u, v] + (e ![u] * t - e ![v] * s) := by
  have h : ((Prod.fst : LiftSpace → Space) ∘ ![(u, s), (v, t)]) = ![u, v] := by
    funext i; fin_cases i <;> rfl
  have h1 (a : Space) (r : ℝ) :
      ((Prod.fst : LiftSpace → Space) ∘ ![(a, r)]) = ![a] := by
    funext i; fin_cases i; rfl
  simp [ofParts, ContinuousAlternatingMap.compContinuousLinearMap_apply, h, h1]

/-- The lift of the source is the form with parts `(b, -⋆b)`. -/
theorem hymLiftAt_eq_ofParts (b : Form 2) : hymLiftAt b = ofParts b (-hodge b) := by
  apply liftForm2_ext
  intro u v s t
  rw [hymLiftAt_apply, ofParts_apply]
  simp only [ContinuousAlternatingMap.neg_apply]
  ring

/-- **The spatial part** of a 2-form on the lift space: its restriction to a slice
`τ = const`, `a(u, v) = F((u,0),(v,0))`. -/
noncomputable def spatialPart : LiftForm 2 →ₗ[ℝ] Form 2 := sliceCLM.toLinearMap

/-- The spatial part on two vectors. -/
theorem spatialPart_apply (F : LiftForm 2) (u v : Space) :
    spatialPart F ![u, v] = F ![(u, 0), (v, 0)] := by
  have e : (⇑(ContinuousLinearMap.inl ℝ Space ℝ) ∘ ![u, v]) = ![(u, 0), (v, 0)] := by
    funext i; fin_cases i <;> rfl
  simp [spatialPart, sliceCLM, ContinuousAlternatingMap.compContinuousLinearMap_apply, e]

/-- **The mixed part** of a 2-form on the lift space: the 1-form `e(u) = F((u,0),(0,1))` on
`ℝ³`. -/
noncomputable def mixedPart : LiftForm 2 →ₗ[ℝ] Form 1 where
  toFun F := -((F.curryLeft ((0, 1) : LiftSpace)).compContinuousLinearMap
    (ContinuousLinearMap.inl ℝ Space ℝ))
  map_add' F G := by ext w; simp [add_comm]
  map_smul' c F := by ext w; simp

/-- The mixed part on a vector. -/
theorem mixedPart_apply (F : LiftForm 2) (u : Space) :
    mixedPart F ![u] = F ![(u, 0), (0, 1)] := by
  have e : (vecCons ((0, 1) : LiftSpace) (⇑(ContinuousLinearMap.inl ℝ Space ℝ) ∘ ![u])) =
      ![(0, 1), (u, 0)] := by
    funext i; fin_cases i <;> rfl
  rw [liftForm2_swap]
  simp [mixedPart, ContinuousAlternatingMap.compContinuousLinearMap_apply, e]

/-- Two 1-forms on `ℝ³` are equal if they agree on all one-vector tuples. -/
theorem form1_ext {f g : Form 1} (h : ∀ u : Space, f ![u] = g ![u]) : f = g := by
  ext w
  have e : w = ![w 0] := by funext i; fin_cases i; rfl
  rw [e]
  exact h _

/-- Two 2-forms on `ℝ³` are equal if they agree on all pairs of vectors. -/
theorem form2_ext {f g : Form 2} (h : ∀ u v : Space, f ![u, v] = g ![u, v]) : f = g := by
  ext w
  have e : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
  rw [e]
  exact h _ _

/-- The spatial part of the form with parts `(a, e)` is `a`. -/
@[simp] theorem spatialPart_ofParts (a : Form 2) (e : Form 1) :
    spatialPart (ofParts a e) = a := by
  apply form2_ext
  intro u v
  rw [spatialPart_apply, ofParts_apply]
  simp

/-- The mixed part of the form with parts `(a, e)` is `e`. -/
@[simp] theorem mixedPart_ofParts (a : Form 2) (e : Form 1) :
    mixedPart (ofParts a e) = e := by
  apply form1_ext
  intro u
  have z : a ![u, 0] = 0 := a.map_coord_zero 1 rfl
  have z' : e ![0] = 0 := e.map_coord_zero 0 rfl
  rw [mixedPart_apply, ofParts_apply]
  simp [z, z']

/-- **Every 2-form on the lift space is `π^*a + π^*e ∧ dτ`** with `a` its spatial part and `e`
its mixed part. -/
@[simp] theorem ofParts_parts (F : LiftForm 2) : ofParts (spatialPart F) (mixedPart F) = F := by
  apply liftForm2_ext
  intro u v s t
  rw [ofParts_apply, spatialPart_apply, mixedPart_apply, mixedPart_apply]
  exact (liftForm2_apply F u v s t).symm

/-- **The decomposition of 2-forms on `ℝ³ × ℝ`** as a linear equivalence
`F ↦ (spatial part, mixed part)`, with inverse `(a, e) ↦ π^*a + π^*e ∧ dτ`. -/
noncomputable def liftParts : LiftForm 2 ≃ₗ[ℝ] Form 2 × Form 1 where
  toFun F := (spatialPart F, mixedPart F)
  map_add' F G := by simp
  map_smul' c F := by simp
  invFun p := ofParts p.1 p.2
  left_inv F := ofParts_parts F
  right_inv p := by simp

/-- The decomposition in components. -/
@[simp] theorem liftParts_apply (F : LiftForm 2) :
    liftParts F = (spatialPart F, mixedPart F) := rfl

/-- The inverse of the decomposition. -/
@[simp] theorem liftParts_symm_apply (p : Form 2 × Form 1) :
    liftParts.symm p = ofParts p.1 p.2 := rfl

/-- The space of 2-forms on `ℝ³ × ℝ` has dimension six. -/
theorem finrank_liftForm2 : finrank ℝ (LiftForm 2) = 6 := by
  have h2 : finrank ℝ (Form 2) = 3 := by rw [← flux.finrank_eq]; simp
  have h1 : finrank ℝ (Form 1) = 3 := by rw [← flat.finrank_eq]; simp
  have : Module.Finite ℝ (Form 2) := Module.finite_of_finrank_pos (by omega)
  have : Module.Finite ℝ (Form 1) := Module.finite_of_finrank_pos (by omega)
  rw [liftParts.finrank_eq, Module.finrank_prod, h1, h2]

/-! ## The Hodge star -/

/-- **The Hodge star on 2-forms of `ℝ³ × ℝ`** for the product Euclidean metric and the
orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`:
`⋆₄(π^*a + π^*e ∧ dτ) = π^*(⋆₃⁻¹e) + π^*(⋆₃a) ∧ dτ`. -/
noncomputable def liftStar : LiftForm 2 ≃ₗ[ℝ] LiftForm 2 :=
  (liftParts.trans ((LinearEquiv.prodComm ℝ (Form 2) (Form 1)).trans
    (LinearEquiv.prodCongr hodge.symm hodge))).trans liftParts.symm

/-- The star in terms of the parts of a form. -/
theorem liftStar_eq (F : LiftForm 2) :
    liftStar F = ofParts (hodge.symm (mixedPart F)) (hodge (spatialPart F)) := rfl

/-- **The star of the form with parts `(a, e)`** has parts `(⋆₃⁻¹e, ⋆₃a)`. -/
@[simp] theorem liftStar_ofParts (a : Form 2) (e : Form 1) :
    liftStar (ofParts a e) = ofParts (hodge.symm e) (hodge a) := by
  rw [liftStar_eq, spatialPart_ofParts, mixedPart_ofParts]

/-- The spatial part of the star is the inverse 3-dimensional star of the mixed part. -/
@[simp] theorem spatialPart_liftStar (F : LiftForm 2) :
    spatialPart (liftStar F) = hodge.symm (mixedPart F) := by
  rw [liftStar_eq, spatialPart_ofParts]

/-- The mixed part of the star is the 3-dimensional star of the spatial part. -/
@[simp] theorem mixedPart_liftStar (F : LiftForm 2) :
    mixedPart (liftStar F) = hodge (spatialPart F) := by
  rw [liftStar_eq, mixedPart_ofParts]

/-- **`⋆₄⋆₄ = 1` on 2-forms.** -/
@[simp] theorem liftStar_liftStar (F : LiftForm 2) : liftStar (liftStar F) = F := by
  rw [liftStar_eq (liftStar F)]
  simp

/-- The star is its own inverse. -/
theorem liftStar_symm : liftStar.symm = liftStar := by
  ext1 F
  rw [LinearEquiv.symm_apply_eq, liftStar_liftStar]

/-- **The star on the coordinate planes, first half**: `(⋆F)(eᵢ, e_τ) = F(eⱼ, eₖ)` for
`(i, j, k)` a cyclic permutation of `(0, 1, 2)`. -/
theorem liftStar_apply_mixed (F : LiftForm 2) :
    liftStar F ![(coordVec 0, 0), (0, 1)] = F ![(coordVec 1, 0), (coordVec 2, 0)] ∧
    liftStar F ![(coordVec 1, 0), (0, 1)] = F ![(coordVec 2, 0), (coordVec 0, 0)] ∧
    liftStar F ![(coordVec 2, 0), (0, 1)] = F ![(coordVec 0, 0), (coordVec 1, 0)] := by
  obtain ⟨h0, h1, h2⟩ := hodge_apply_coordVec (spatialPart F)
  simp only [← mixedPart_apply, ← spatialPart_apply, mixedPart_liftStar]
  exact ⟨h0, h1, h2⟩

/-- **The star on the coordinate planes, second half**: `(⋆F)(eⱼ, eₖ) = F(eᵢ, e_τ)` for
`(i, j, k)` a cyclic permutation of `(0, 1, 2)`. -/
theorem liftStar_apply_spatial (F : LiftForm 2) :
    liftStar F ![(coordVec 1, 0), (coordVec 2, 0)] = F ![(coordVec 0, 0), (0, 1)] ∧
    liftStar F ![(coordVec 2, 0), (coordVec 0, 0)] = F ![(coordVec 1, 0), (0, 1)] ∧
    liftStar F ![(coordVec 0, 0), (coordVec 1, 0)] = F ![(coordVec 2, 0), (0, 1)] := by
  have h := liftStar_apply_mixed (liftStar F)
  simp only [liftStar_liftStar] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-! ## The coordinate 2-forms -/

/-- The coordinate 1-form `dxᵢ` on the lift space. -/
noncomputable def dX (i : Fin 3) : LiftForm 1 :=
  (flat (coordVec i)).compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ)

/-- `dxᵢ` reads off the `i`-th spatial component. -/
theorem dX_apply (i : Fin 3) (p : LiftSpace) : dX i ![p] = p.1 i := by
  simp [dX, coordVec, EuclideanSpace.inner_single_left]

/-- The form with parts `(a, e)` is additive in the pair. -/
theorem ofParts_add (a a' : Form 2) (e e' : Form 1) :
    ofParts (a + a') (e + e') = ofParts a e + ofParts a' e' :=
  map_add liftParts.symm (a, e) (a', e')

/-- The form with parts `(a, e)` is homogeneous in the pair. -/
theorem ofParts_smul (c : ℝ) (a : Form 2) (e : Form 1) :
    ofParts (c • a) (c • e) = c • ofParts a e :=
  map_smul liftParts.symm c (a, e)

/-- The form with parts `(a, e)` commutes with negation. -/
theorem ofParts_neg (a : Form 2) (e : Form 1) : ofParts (-a) (-e) = -ofParts a e :=
  map_neg liftParts.symm (a, e)

/-- The spatial coordinate 2-forms: `dx₁ ∧ dx₂`, `dx₂ ∧ dx₀`, `dx₀ ∧ dx₁` are the pullbacks of
the flux forms of `e₀`, `e₁`, `e₂`. -/
theorem dX_wedge_dX :
    (ContinuousAlternatingMap.wedge (dX 1) (dX 2) : LiftForm 2) = ofParts (flux (coordVec 0)) 0 ∧
    (ContinuousAlternatingMap.wedge (dX 2) (dX 0) : LiftForm 2) = ofParts (flux (coordVec 1)) 0 ∧
    (ContinuousAlternatingMap.wedge (dX 0) (dX 1) : LiftForm 2) =
      ofParts (flux (coordVec 2)) 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply liftForm2_ext
    intro u v s t
    rw [ContinuousAlternatingMap.wedge_apply_one_one, ofParts_apply, flux_apply, volForm_vec]
    simp [dX_apply, coordVec]
    ring

/-- The mixed coordinate 2-forms: `dxᵢ ∧ dτ` has parts `(0, eᵢ♭)`. -/
theorem dX_wedge_dTau (i : Fin 3) :
    (ContinuousAlternatingMap.wedge (dX i) dTau : LiftForm 2) = ofParts 0 (flat (coordVec i)) := by
  apply liftForm2_ext
  intro u v s t
  rw [ContinuousAlternatingMap.wedge_apply_one_one, ofParts_apply]
  simp [dX_apply, coordVec, EuclideanSpace.inner_single_left]

/-- **The star on the coordinate 2-forms, spatial ones**: `⋆(dx₁ ∧ dx₂) = dx₀ ∧ dτ`,
`⋆(dx₂ ∧ dx₀) = dx₁ ∧ dτ`, `⋆(dx₀ ∧ dx₁) = dx₂ ∧ dτ`. Each is forced by `α ∧ ⋆α = vol` for the
orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`: for instance `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ` is the volume form
itself. -/
theorem liftStar_dX_wedge_dX :
    liftStar (ContinuousAlternatingMap.wedge (dX 1) (dX 2) : LiftForm 2) =
      (ContinuousAlternatingMap.wedge (dX 0) dTau : LiftForm 2) ∧
    liftStar (ContinuousAlternatingMap.wedge (dX 2) (dX 0) : LiftForm 2) =
      (ContinuousAlternatingMap.wedge (dX 1) dTau : LiftForm 2) ∧
    liftStar (ContinuousAlternatingMap.wedge (dX 0) (dX 1) : LiftForm 2) =
      (ContinuousAlternatingMap.wedge (dX 2) dTau : LiftForm 2) := by
  obtain ⟨h0, h1, h2⟩ := dX_wedge_dX
  rw [h0, h1, h2]
  simp [dX_wedge_dTau]

/-- **The star on the coordinate 2-forms, mixed ones**: `⋆(dx₀ ∧ dτ) = dx₁ ∧ dx₂`,
`⋆(dx₁ ∧ dτ) = dx₂ ∧ dx₀`, `⋆(dx₂ ∧ dτ) = dx₀ ∧ dx₁`. -/
theorem liftStar_dX_wedge_dTau :
    liftStar (ContinuousAlternatingMap.wedge (dX 0) dTau : LiftForm 2) =
      (ContinuousAlternatingMap.wedge (dX 1) (dX 2) : LiftForm 2) ∧
    liftStar (ContinuousAlternatingMap.wedge (dX 1) dTau : LiftForm 2) =
      (ContinuousAlternatingMap.wedge (dX 2) (dX 0) : LiftForm 2) ∧
    liftStar (ContinuousAlternatingMap.wedge (dX 2) dTau : LiftForm 2) =
      (ContinuousAlternatingMap.wedge (dX 0) (dX 1) : LiftForm 2) := by
  obtain ⟨h0, h1, h2⟩ := liftStar_dX_wedge_dX
  rw [← h0, ← h1, ← h2]
  simp

/-! ## Anti-self-duality is `⋆F = -F` -/

/-- Two 1-forms on `ℝ³` are equal if they agree on the three unit vectors. -/
theorem form1_ext_coord {f g : Form 1} (h0 : f ![coordVec 0] = g ![coordVec 0])
    (h1 : f ![coordVec 1] = g ![coordVec 1]) (h2 : f ![coordVec 2] = g ![coordVec 2]) :
    f = g := by
  apply ext_basis
  intro v _
  have e : (fun i => coordVec (v i)) = ![coordVec (v 0)] := by
    funext i; fin_cases i; rfl
  rw [e]
  generalize v 0 = p
  fin_cases p <;> assumption

/-- The component form of anti-self-duality says that the mixed part is minus the
3-dimensional star of the spatial part. -/
theorem isAntiSelfDual_iff_mixedPart (F : LiftForm 2) :
    IsAntiSelfDual F ↔ mixedPart F = -hodge (spatialPart F) := by
  obtain ⟨h0, h1, h2⟩ := hodge_apply_coordVec (spatialPart F)
  unfold IsAntiSelfDual
  simp only [← mixedPart_apply, ← spatialPart_apply, ← h0, ← h1, ← h2]
  constructor
  · rintro ⟨k0, k1, k2⟩
    apply form1_ext_coord <;> simpa using by assumption
  · intro h
    rw [h]
    simp

/-- `⋆F = -F` says that the mixed part is minus the 3-dimensional star of the spatial part. -/
theorem liftStar_eq_neg_iff_mixedPart (F : LiftForm 2) :
    liftStar F = -F ↔ mixedPart F = -hodge (spatialPart F) := by
  constructor
  · intro h
    have := congrArg mixedPart h
    rw [mixedPart_liftStar, map_neg] at this
    rw [this, neg_neg]
  · intro h
    have k := ofParts_neg (spatialPart F) (mixedPart F)
    rw [ofParts_parts] at k
    rw [h, neg_neg] at k
    rw [liftStar_eq, h, map_neg, LinearEquiv.symm_apply_apply]
    exact k

/-- `⋆F = F` says that the mixed part is the 3-dimensional star of the spatial part. -/
theorem liftStar_eq_self_iff_mixedPart (F : LiftForm 2) :
    liftStar F = F ↔ mixedPart F = hodge (spatialPart F) := by
  constructor
  · intro h
    have := congrArg mixedPart h
    rw [mixedPart_liftStar] at this
    exact this.symm
  · intro h
    rw [liftStar_eq, h, LinearEquiv.symm_apply_apply, ← h, ofParts_parts]

/-- **The component definition `IsAntiSelfDual` is anti-self-duality for the star `liftStar`**:
`IsAntiSelfDual F ↔ ⋆₄F = -F`. -/
theorem isAntiSelfDual_iff_liftStar (F : LiftForm 2) : IsAntiSelfDual F ↔ liftStar F = -F := by
  rw [isAntiSelfDual_iff_mixedPart, liftStar_eq_neg_iff_mixedPart]

/-- **The lift of the source is anti-self-dual**: `⋆₄(π^*b - π^*(⋆₃b) ∧ dτ) = -(…)`. -/
theorem liftStar_hymLiftAt (b : Form 2) : liftStar (hymLiftAt b) = -hymLiftAt b :=
  (isAntiSelfDual_iff_liftStar _).1 (hymLiftAt_isAntiSelfDual b)

/-- **The lifted form of any field of 2-forms is anti-self-dual at every point.** -/
theorem liftStar_hymLift (w : Space → Form 2) (p : LiftSpace) :
    liftStar (hymLift w p) = -hymLift w p :=
  liftStar_hymLiftAt _

/-- **The self-dual lift** `π^*b + π^*(⋆₃b) ∧ dτ` of a 2-form on `ℝ³` (the lift for the
opposite orientation, N-37). -/
noncomputable def sdLiftAt (b : Form 2) : LiftForm 2 := ofParts b (hodge b)

/-- The self-dual lift is self-dual. -/
theorem liftStar_sdLiftAt (b : Form 2) : liftStar (sdLiftAt b) = sdLiftAt b := by
  simp [sdLiftAt]

/-- **An anti-self-dual form is the lift of its spatial part.** -/
theorem eq_hymLiftAt_of_liftStar_eq_neg {F : LiftForm 2} (h : liftStar F = -F) :
    F = hymLiftAt (spatialPart F) := by
  rw [hymLiftAt_eq_ofParts, ← (liftStar_eq_neg_iff_mixedPart F).1 h, ofParts_parts]

/-- **A self-dual form is the self-dual lift of its spatial part.** -/
theorem eq_sdLiftAt_of_liftStar_eq_self {F : LiftForm 2} (h : liftStar F = F) :
    F = sdLiftAt (spatialPart F) := by
  rw [sdLiftAt, ← (liftStar_eq_self_iff_mixedPart F).1 h, ofParts_parts]

/-- **The anti-self-dual 2-forms are exactly the lifts** `π^*b - π^*(⋆₃b) ∧ dτ`. -/
theorem liftStar_eq_neg_iff_exists (F : LiftForm 2) :
    liftStar F = -F ↔ ∃ b : Form 2, F = hymLiftAt b :=
  ⟨fun h => ⟨_, eq_hymLiftAt_of_liftStar_eq_neg h⟩, fun ⟨b, hb⟩ => hb ▸ liftStar_hymLiftAt b⟩

/-! ## The eigenspaces -/

/-- The self-dual 2-forms on `ℝ³ × ℝ`: the `+1` eigenspace of the star. -/
noncomputable def selfDualForms : Submodule ℝ (LiftForm 2) :=
  Module.End.eigenspace (liftStar : LiftForm 2 →ₗ[ℝ] LiftForm 2) 1

/-- The anti-self-dual 2-forms on `ℝ³ × ℝ`: the `-1` eigenspace of the star. -/
noncomputable def antiSelfDualForms : Submodule ℝ (LiftForm 2) :=
  Module.End.eigenspace (liftStar : LiftForm 2 →ₗ[ℝ] LiftForm 2) (-1)

/-- Membership in the self-dual forms. -/
theorem mem_selfDualForms {F : LiftForm 2} : F ∈ selfDualForms ↔ liftStar F = F := by
  simp [selfDualForms]

/-- Membership in the anti-self-dual forms. -/
theorem mem_antiSelfDualForms {F : LiftForm 2} : F ∈ antiSelfDualForms ↔ liftStar F = -F := by
  simp [antiSelfDualForms]

/-- The anti-self-dual forms are those satisfying the component condition. -/
theorem mem_antiSelfDualForms_iff_isAntiSelfDual {F : LiftForm 2} :
    F ∈ antiSelfDualForms ↔ IsAntiSelfDual F := by
  rw [mem_antiSelfDualForms, isAntiSelfDual_iff_liftStar]

/-- **The lift is a linear isomorphism from the 2-forms of `ℝ³` onto the anti-self-dual
2-forms of `ℝ³ × ℝ`**; its inverse is the restriction to a slice `τ = const`. -/
noncomputable def hymLiftEquiv : Form 2 ≃ₗ[ℝ] antiSelfDualForms where
  toFun b := ⟨hymLiftAt b, mem_antiSelfDualForms.2 (liftStar_hymLiftAt b)⟩
  map_add' a b := Subtype.ext (hymLiftAt_add a b)
  map_smul' c b := Subtype.ext (hymLiftAt_smul c b)
  invFun F := spatialPart F.1
  left_inv b := sliceCLM_hymLiftAt b
  right_inv F := Subtype.ext (eq_hymLiftAt_of_liftStar_eq_neg (mem_antiSelfDualForms.1 F.2)).symm

/-- The underlying form of `hymLiftEquiv b` is the lift. -/
@[simp] theorem coe_hymLiftEquiv (b : Form 2) : (hymLiftEquiv b : LiftForm 2) = hymLiftAt b := rfl

/-- **The self-dual lift is a linear isomorphism from the 2-forms of `ℝ³` onto the self-dual
2-forms of `ℝ³ × ℝ`.** -/
noncomputable def sdLiftEquiv : Form 2 ≃ₗ[ℝ] selfDualForms where
  toFun b := ⟨sdLiftAt b, mem_selfDualForms.2 (liftStar_sdLiftAt b)⟩
  map_add' a b := Subtype.ext (by simp only [sdLiftAt, map_add, ofParts_add]; rfl)
  map_smul' c b := Subtype.ext (by simp only [sdLiftAt, map_smul, ofParts_smul]; rfl)
  invFun F := spatialPart F.1
  left_inv b := spatialPart_ofParts b _
  right_inv F := Subtype.ext (eq_sdLiftAt_of_liftStar_eq_self (mem_selfDualForms.1 F.2)).symm

/-- The underlying form of `sdLiftEquiv b` is the self-dual lift. -/
@[simp] theorem coe_sdLiftEquiv (b : Form 2) : (sdLiftEquiv b : LiftForm 2) = sdLiftAt b := rfl

/-- The space of 2-forms on `ℝ³` has dimension three. -/
theorem finrank_form2 : finrank ℝ (Form 2) = 3 := by rw [← flux.finrank_eq]; simp

/-- **The anti-self-dual 2-forms have dimension three.** -/
theorem finrank_antiSelfDualForms : finrank ℝ antiSelfDualForms = 3 := by
  rw [← hymLiftEquiv.finrank_eq, finrank_form2]

/-- **The self-dual 2-forms have dimension three.** -/
theorem finrank_selfDualForms : finrank ℝ selfDualForms = 3 := by
  rw [← sdLiftEquiv.finrank_eq, finrank_form2]

/-- **Every 2-form on `ℝ³ × ℝ` is uniquely the sum of a self-dual and an anti-self-dual
form.** -/
theorem isCompl_selfDualForms_antiSelfDualForms : IsCompl selfDualForms antiSelfDualForms := by
  refine ⟨Submodule.disjoint_def.2 fun F h1 h2 => ?_, codisjoint_iff.2 ?_⟩
  · have h := (mem_selfDualForms.1 h1).symm.trans (mem_antiSelfDualForms.1 h2)
    have h' : (2 : ℝ) • F = 0 := by rw [two_smul]; nth_rewrite 1 [h]; simp
    simpa using h'
  · refine (Submodule.eq_top_iff').2 fun F => Submodule.mem_sup.2
      ⟨(1 / 2 : ℝ) • (F + liftStar F), ?_, (1 / 2 : ℝ) • (F - liftStar F), ?_, ?_⟩
    · rw [mem_selfDualForms, map_smul, map_add, liftStar_liftStar, add_comm]
    · rw [mem_antiSelfDualForms, map_smul, map_sub, liftStar_liftStar, ← smul_neg, neg_sub]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ F, smul_smul]
      norm_num

/-! ## The star is the Hodge star of the oriented Euclidean space `ℝ³ ⊕ ℝ` -/

/-- The lift space with its Euclidean (`L²`) product norm: the inner product space whose
metric is the product Euclidean metric. As a vector space it is `ℝ³ × ℝ`. -/
abbrev LiftEuclid := WithLp 2 (Space × ℝ)

/-- The identification of the Euclidean lift space with `ℝ³ × ℝ` (the identity on vectors). -/
noncomputable def liftEuclidEquiv : LiftEuclid ≃L[ℝ] LiftSpace :=
  WithLp.prodContinuousLinearEquiv 2 ℝ Space ℝ

/-- A form on the lift space as a form on the Euclidean lift space (same values). -/
noncomputable def euclidForm {k : ℕ} : LiftForm k →L[ℝ] (LiftEuclid [⋀^Fin k]→L[ℝ] ℝ) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (liftEuclidEquiv : LiftEuclid →L[ℝ] LiftSpace)

/-- Evaluation of `euclidForm` on two vectors. -/
theorem euclidForm_apply (F : LiftForm 2) (x y : LiftEuclid) :
    euclidForm F ![x, y] = F ![(x.ofLp.1, x.ofLp.2), (y.ofLp.1, y.ofLp.2)] := by
  have e : (⇑(liftEuclidEquiv : LiftEuclid →L[ℝ] LiftSpace) ∘ ![x, y]) =
      ![(x.ofLp.1, x.ofLp.2), (y.ofLp.1, y.ofLp.2)] := by
    funext i; fin_cases i <;> rfl
  rw [euclidForm, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, e]

/-- A form on the lift space is determined by its reading on the Euclidean lift space. -/
theorem euclidForm_injective : Function.Injective (euclidForm : LiftForm 2 → _) := by
  intro F G h
  apply liftForm2_ext
  intro u v s t
  have k := congrArg (fun A : LiftEuclid [⋀^Fin 2]→L[ℝ] ℝ =>
    A ![WithLp.toLp 2 (u, s), WithLp.toLp 2 (v, t)]) h
  simpa only [euclidForm_apply] using k

/-- The standard orthonormal frame `(e₀, e₁, e₂, e_τ)` of the Euclidean lift space. -/
noncomputable def liftFrame : OrthonormalBasis (Fin 4) ℝ LiftEuclid :=
  (stdBasis.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv

/-- **The orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`** of the Euclidean lift space: that of the frame
`(e₀, e₁, e₂, e_τ)`. -/
noncomputable def liftOrientation : Orientation ℝ LiftEuclid (Fin 4) :=
  liftFrame.toBasis.orientation

/-- The Euclidean lift space has dimension four. -/
theorem finrank_liftEuclid : finrank ℝ LiftEuclid = 4 := by
  simpa using finrank_eq_card_basis liftFrame.toBasis

/-- Degree two is the middle degree of the Euclidean lift space. -/
theorem two_add_two_eq_finrank_liftEuclid : 2 + 2 = finrank ℝ LiftEuclid :=
  finrank_liftEuclid.symm

/-- The dimension of the Euclidean lift space, for Mathlib's volume form and TauCeti's Hodge
star. Local: this file exports no instances. Downstream users of `euclidForm_liftStar` (and of
the other statements below that mention Mathlib's volume form or TauCeti's Hodge star on
`LiftEuclid`) must supply this instance themselves, from `finrank_liftEuclid`. -/
local instance : Fact (finrank ℝ LiftEuclid = 4) := ⟨finrank_liftEuclid⟩

/-- The vectors of the standard frame: `(e₀, 0)`, `(e₁, 0)`, `(e₂, 0)`, `(0, 1)`. -/
theorem liftFrame_apply :
    liftFrame 0 = WithLp.toLp 2 (coordVec 0, 0) ∧ liftFrame 1 = WithLp.toLp 2 (coordVec 1, 0) ∧
    liftFrame 2 = WithLp.toLp 2 (coordVec 2, 0) ∧ liftFrame 3 = WithLp.toLp 2 (0, 1) := by
  have h0 : finSumFinEquiv.symm (0 : Fin (3 + 1)) = Sum.inl 0 := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin (3 + 1)) = Sum.inl 1 := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin (3 + 1)) = Sum.inl 2 := rfl
  have h3 : finSumFinEquiv.symm (3 : Fin (3 + 1)) = Sum.inr 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [liftFrame, OrthonormalBasis.reindex_apply, h0, h1, h2, h3, coordVec]

/-- The volume form of the orientation is the determinant of the components in the standard
frame. -/
theorem liftOrientation_volumeForm_apply (v : Fin 4 → LiftEuclid) :
    liftOrientation.volumeForm v = Matrix.det (Matrix.of fun i j => ⟪liftFrame i, v j⟫) := by
  rw [liftOrientation.volumeForm_robust liftFrame rfl, Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

/-- **The orientation is `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`**: the volume form is `1` on the frame
`(e₀, e₁, e₂, e_τ)`. -/
theorem liftOrientation_volumeForm_frame :
    liftOrientation.volumeForm ![WithLp.toLp 2 (coordVec 0, 0), WithLp.toLp 2 (coordVec 1, 0),
      WithLp.toLp 2 (coordVec 2, 0), WithLp.toLp 2 (0, 1)] = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := liftFrame_apply
  rw [liftOrientation_volumeForm_apply, Matrix.det_fin_four]
  simp [h0, h1, h2, h3, coordVec, EuclideanSpace.inner_single_left]

/-- The 4-dimensional volume of `(w, 0)`, `(0, 1)` and two further vectors is the
3-dimensional volume of `w` and the spatial components of the two vectors. -/
theorem liftOrientation_volumeForm_slice (w : Space) (x y : LiftEuclid) :
    liftOrientation.volumeForm ![WithLp.toLp 2 (w, 0), WithLp.toLp 2 (0, 1), x, y] =
      volForm ![w, x.ofLp.1, y.ofLp.1] := by
  obtain ⟨h0, h1, h2, h3⟩ := liftFrame_apply
  rw [liftOrientation_volumeForm_apply, Matrix.det_fin_four, volForm_vec]
  simp [h0, h1, h2, h3, coordVec, EuclideanSpace.inner_single_left]
  ring

/-- The form `π^*(w♭) ∧ dτ`, read on the Euclidean lift space, is the form dual to the
bivector `(w, 0) ∧ (0, 1)`. -/
theorem euclidForm_ofParts_zero_flat (w : Space) :
    euclidForm (ofParts 0 (flat w)) = TauCeti.alternatingFormEquiv LiftEuclid 2
      (exteriorPower.ιMulti ℝ 2 ![WithLp.toLp 2 (w, 0), WithLp.toLp 2 (0, 1)]) := by
  ext v
  have e : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [e, euclidForm_apply, ofParts_apply, TauCeti.alternatingFormEquiv_ιMulti_apply,
    Matrix.det_fin_two]
  simp [WithLp.prod_inner_apply]
  ring

/-- TauCeti's Hodge star of `π^*(w♭) ∧ dτ` is `π^*(ι_w vol)`. -/
theorem formHodgeStar_euclidForm_mixed (w : Space) :
    liftOrientation.formHodgeStar two_add_two_eq_finrank_liftEuclid
      (euclidForm (ofParts 0 (flat w))) = euclidForm (ofParts (flux w) 0) := by
  ext v
  have e : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have a : (Fin.append ![(WithLp.toLp 2 (w, 0) : LiftEuclid), WithLp.toLp 2 (0, 1)] v ∘
      Fin.cast (two_add_two_eq_finrank_liftEuclid.trans finrank_liftEuclid).symm) =
      ![WithLp.toLp 2 (w, 0), WithLp.toLp 2 (0, 1), v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [euclidForm_ofParts_zero_flat, Orientation.formHodgeStar_alternatingFormEquiv_ιMulti_apply,
    a, liftOrientation_volumeForm_slice]
  conv_rhs => rw [e, euclidForm_apply, ofParts_apply, flux_apply]
  simp

/-- **`liftStar` is the Hodge star of the oriented Euclidean space `ℝ³ ⊕ ℝ`.** Reading forms on
`ℝ³ × ℝ` as forms on the inner product space `WithLp 2 (ℝ³ × ℝ)` (product Euclidean metric)
with the orientation of the frame `(e₀, e₁, e₂, e_τ)`, the explicit star `liftStar` is TauCeti's
`Orientation.formHodgeStar`, the star characterised by `α ∧ ⋆β = ⟨α, β⟩ vol`. -/
theorem euclidForm_liftStar (F : LiftForm 2) :
    euclidForm (liftStar F) =
      liftOrientation.formHodgeStar two_add_two_eq_finrank_liftEuclid (euclidForm F) := by
  obtain ⟨v, hv⟩ := flux.surjective (spatialPart F)
  obtain ⟨w, hw⟩ := flat.surjective (mixedPart F)
  have hF : F = ofParts (flux v) 0 + ofParts 0 (flat w) := by
    rw [← ofParts_add, add_zero, zero_add, hv, hw, ofParts_parts]
  have h1 := formHodgeStar_euclidForm_mixed
  have h2 (u : Space) : liftOrientation.formHodgeStar two_add_two_eq_finrank_liftEuclid
      (euclidForm (ofParts (flux u) 0)) = euclidForm (ofParts 0 (flat u)) := by
    rw [← h1 u, Orientation.formHodgeStar_formHodgeStar_of_even _ even_two]
  rw [hF]
  simp only [map_add]
  rw [h1, h2, liftStar_ofParts, liftStar_ofParts]
  simp

/-- **The star for the opposite orientation `dτ ∧ dx₀ ∧ dx₁ ∧ dx₂` is `-liftStar`**, so the
lift of the source is self-dual for that orientation (N-37). -/
theorem euclidForm_neg_liftStar (F : LiftForm 2) :
    euclidForm (-liftStar F) =
      (-liftOrientation).formHodgeStar two_add_two_eq_finrank_liftEuclid (euclidForm F) := by
  rw [Orientation.formHodgeStar_neg_orientation, ← euclidForm_liftStar, map_neg]

/-- The inner product of 2-forms on `ℝ³ × ℝ` for the product Euclidean metric: TauCeti's Gram
inner product of forms on the Euclidean lift space. -/
noncomputable def liftInner (F G : LiftForm 2) : ℝ :=
  TauCeti.alternatingFormInner LiftEuclid 2 (euclidForm F) (euclidForm G)

/-- The volume form of `ℝ³ × ℝ` for the product Euclidean metric and the orientation
`dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`, on four vectors. -/
noncomputable def liftVol (v : Fin (2 + 2) → LiftSpace) : ℝ :=
  liftOrientation.volumeForm fun i => WithLp.toLp 2 (v i)

/-- **The intrinsic characterisation of the star**: `F ∧ ⋆G = ⟨F, G⟩ vol` for 2-forms on
`ℝ³ × ℝ`, with TauCeti's wedge product. -/
theorem wedge_liftStar_apply (F G : LiftForm 2) (v : Fin (2 + 2) → LiftSpace) :
    (ContinuousAlternatingMap.wedge F (liftStar G)) v = liftInner F G * liftVol v := by
  have h := liftOrientation.wedge_formHodgeStar_apply two_add_two_eq_finrank_liftEuclid
    (euclidForm F) (euclidForm G) (fun i => WithLp.toLp 2 (v i))
  rw [← euclidForm_liftStar] at h
  simp only [euclidForm, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.wedge_compContinuousLinearMap] at h
  exact h

/-- The volume form is `1` on the frame `(e₀, e₁, e₂, e_τ)`. -/
theorem liftVol_frame :
    liftVol ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0), (0, 1)] = 1 := by
  have e : (fun i => WithLp.toLp 2 ((![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0),
      (0, 1)] : Fin (2 + 2) → LiftSpace) i)) =
      ![WithLp.toLp 2 (coordVec 0, 0), WithLp.toLp 2 (coordVec 1, 0),
        WithLp.toLp 2 (coordVec 2, 0), WithLp.toLp 2 (0, 1)] := by
    funext i; fin_cases i <;> rfl
  rw [liftVol, e]
  exact liftOrientation_volumeForm_frame

/-- **The inner product of 2-forms in coordinates**: the six coordinate 2-forms are
orthonormal, `⟨F, G⟩ = ∑ F(e_I) G(e_I)` over the six coordinate planes. Derived from the wedge
identity `F ∧ ⋆G = ⟨F, G⟩ vol` and the six-term formula for the wedge of two 2-forms, so it
checks the star against the wedge product. -/
theorem liftInner_eq (F G : LiftForm 2) :
    liftInner F G =
      F ![(coordVec 1, 0), (coordVec 2, 0)] * G ![(coordVec 1, 0), (coordVec 2, 0)] +
      F ![(coordVec 2, 0), (coordVec 0, 0)] * G ![(coordVec 2, 0), (coordVec 0, 0)] +
      F ![(coordVec 0, 0), (coordVec 1, 0)] * G ![(coordVec 0, 0), (coordVec 1, 0)] +
      F ![(coordVec 0, 0), (0, 1)] * G ![(coordVec 0, 0), (0, 1)] +
      F ![(coordVec 1, 0), (0, 1)] * G ![(coordVec 1, 0), (0, 1)] +
      F ![(coordVec 2, 0), (0, 1)] * G ![(coordVec 2, 0), (0, 1)] := by
  have h := wedge_liftStar_apply F G ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0), (0, 1)]
  obtain ⟨m0, m1, m2⟩ := liftStar_apply_mixed G
  obtain ⟨s0, s1, s2⟩ := liftStar_apply_spatial G
  have kG := liftForm2_swap (liftStar G) (coordVec 0, 0) (coordVec 2, 0)
  have kF := liftForm2_swap F (coordVec 0, 0) (coordVec 2, 0)
  rw [liftVol_frame, mul_one, ContinuousAlternatingMap.wedge_def,
    ContinuousAlternatingMap.pairedWedge_mul_apply_two_two, kG, m0, m1, m2, s0, s1, s2, kF] at h
  rw [← h]
  ring

/-! ## Descent to the circle -/

/-- The lifted form is periodic in `τ` with every period. -/
theorem hymLift_add_period (w : Space → Form 2) (x : Space) (τ ℓ : ℝ) :
    hymLift w (x, τ + ℓ) = hymLift w (x, τ) := rfl

/-- For each `x`, the lifted form is a periodic function of `τ`, with every period `ℓ`. -/
theorem hymLift_periodic (w : Space → Form 2) (x : Space) (ℓ : ℝ) :
    Function.Periodic (fun τ : ℝ => hymLift w (x, τ)) ℓ :=
  fun τ => hymLift_add_period w x τ ℓ

/-- **The lifted form on `ℝ³ × (ℝ/ℓℤ)`**: the field of 2-forms obtained from `hymLift ω` by
passing to the quotient of the `τ`-line by `ℓℤ` (`Function.Periodic.lift`). It is defined for
every real `ℓ`, but it is meaningful only for `0 < ℓ`, which the manifold and measure statements
assume (`[Fact (0 < ℓ)]`): for `ℓ = 0` the quotient is the line itself, and there is no
circle. -/
noncomputable def hymLiftCircle (ℓ : ℝ) (w : Space → Form 2) (p : Space × AddCircle ℓ) :
    LiftForm 2 :=
  (hymLift_periodic w p.1 ℓ).lift p.2

/-- **The field of forms factors through `ℝ³ × (ℝ/ℓℤ)`**: on the class of `τ` the circle form
is the lifted form at `τ`. -/
@[simp] theorem hymLiftCircle_coe (ℓ : ℝ) (w : Space → Form 2) (x : Space) (τ : ℝ) :
    hymLiftCircle ℓ w (x, (τ : AddCircle ℓ)) = hymLift w (x, τ) := rfl

/-- The factorisation as an equation of functions on `ℝ³ × ℝ`. -/
theorem hymLiftCircle_comp (ℓ : ℝ) (w : Space → Form 2) :
    hymLiftCircle ℓ w ∘ Prod.map id ((↑) : ℝ → AddCircle ℓ) = hymLift w := by
  funext p
  exact hymLiftCircle_coe ℓ w p.1 p.2

/-- The circle form at a point is the lift of the value of `ω` there. -/
theorem hymLiftCircle_eq (ℓ : ℝ) (w : Space → Form 2) (p : Space × AddCircle ℓ) :
    hymLiftCircle ℓ w p = hymLiftAt (w p.1) := by
  obtain ⟨x, θ⟩ := p
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rfl

/-- **The factorisation is unique**: a field of forms on `ℝ³ × (ℝ/ℓℤ)` whose composition with
the quotient map is the lifted form is `hymLiftCircle`. -/
theorem eq_hymLiftCircle {ℓ : ℝ} {w : Space → Form 2} {G : Space × AddCircle ℓ → LiftForm 2}
    (h : ∀ (x : Space) (τ : ℝ), G (x, (τ : AddCircle ℓ)) = hymLift w (x, τ)) :
    G = hymLiftCircle ℓ w := by
  funext p
  obtain ⟨x, θ⟩ := p
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact h x τ

/-- The circle form is anti-self-dual at every point. -/
theorem liftStar_hymLiftCircle (ℓ : ℝ) (w : Space → Form 2) (p : Space × AddCircle ℓ) :
    liftStar (hymLiftCircle ℓ w p) = -hymLiftCircle ℓ w p := by
  rw [hymLiftCircle_eq]
  exact liftStar_hymLiftAt _

section Manifold

open scoped Manifold

variable (ℓ : ℝ) [Fact (0 < ℓ)]

/-- **The lifted form as a 2-form on the manifold `ℝ³ × (ℝ/ℓℤ)`** (a rough form in TauCeti's
sense: no regularity is recorded). The tangent spaces of the product manifold are `ℝ³ × ℝ`. -/
noncomputable def hymLiftCircleForm (w : Space → Form 2) :
    TauCeti.RoughForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) (Space × AddCircle ℓ) ℝ 2 :=
  fun p => hymLiftCircle ℓ w p

/-- **The pullback of the circle form along the covering `ℝ³ × ℝ → ℝ³ × (ℝ/ℓℤ)` is the lifted
form**, with the manifold pullback (which uses the derivative of the covering map). -/
theorem mpullback_hymLiftCircleForm (w : Space → Form 2) :
    TauCeti.mpullback (𝓘(ℝ, Space).prod 𝓘(ℝ)) (𝓘(ℝ, Space).prod 𝓘(ℝ))
      (Prod.map (id : Space → Space) ((↑) : ℝ → AddCircle ℓ)) (hymLiftCircleForm ℓ w) =
      fun p => hymLift w p := by
  funext p
  refine ContinuousAlternatingMap.ext fun v => ?_
  rw [TauCeti.mpullback_apply,
    mfderiv_prodMap mdifferentiableAt_id (AddCircle.hasMFDerivAt_coe ℓ p.2).mdifferentiableAt,
    mfderiv_id, AddCircle.mfderiv_coe]
  rfl

end Manifold

end PlasmaLean.Forms
