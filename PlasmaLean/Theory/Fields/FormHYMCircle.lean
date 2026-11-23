/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMStar
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The anti-self-dual lift on the manifold `Ω × S¹`

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, section "A
complex-surface lift that retains the Euclidean metric" (assessment claim S-13). This file
continues `Theory/Fields/FormHYMLift` and `Theory/Fields/FormHYMStar`: there the lifted form
`ℱ = π^*ω - π^*(⋆₃ω) ∧ dτ` was shown closed on `ℝ³ × ℝ` exactly for vacuum forms, and it was
descended to a rough form `hymLiftCircleForm ℓ ω` on the manifold `ℝ³ × (ℝ/ℓℤ)`. Here regularity
and closedness are proved on the quotient manifold itself, with TauCeti's manifold exterior
derivative `mextDeriv`, and the pointwise and integrated energy identities are proved.

## Conventions

* `S¹ = AddCircle ℓ = ℝ/ℓℤ` with `0 < ℓ`, with TauCeti's manifold structure, for which the
  quotient map `ℝ → ℝ/ℓℤ` is a local diffeomorphism with derivative the identity of `ℝ`. The
  manifold `ℝ³ × S¹` has model `𝓘(ℝ, ℝ³).prod 𝓘(ℝ)`; every tangent space is `ℝ³ × ℝ`.
* `liftCover ℓ : ℝ³ × ℝ → ℝ³ × S¹` is the covering map `(x, τ) ↦ (x, [τ])`; its source is the
  normed space `ℝ³ × ℝ` with model `𝓘(ℝ, ℝ³ × ℝ)`, so that the pulled-back form is a function
  into `LiftForm 2` and TauCeti's `mextDeriv_eq_extDeriv` applies.
* The region `Ω × S¹` is the open submanifold `circleRegion ℓ U` of `ℝ³ × S¹` for
  `U : Opens ℝ³`, and the form on it is the restriction `hymLiftRegionForm ℓ U ω`.
* Metric and orientation on the fibres `ℝ³ × ℝ` are those of `FormHYMStar`; `liftInner` is the
  inner product of 2-forms there (the six coordinate 2-forms are orthonormal). The measure on
  `ℝ³ × S¹` is the product of Lebesgue measure and the Haar measure of total mass `ℓ`.

## What is proved

* `isLocalDiffeomorph_liftCover`, `mpullback_liftCover_apply`: the covering map is a local
  diffeomorphism and pullback along it is evaluation at the image point.
* Regularity: `contMDiffAt_hymLiftCircleForm_iff`, `isSmoothForm_hymLiftCircleForm_iff`: the
  circle form is a `C^n` form on `ℝ³ × S¹` exactly when `ω : ℝ³ → Form 2` is `C^n` (pointwise and
  globally, for every `n` including `∞` and `ω`); on a region,
  `isSmoothForm_hymLiftRegionForm_iff` (`C^n` on `Ω × S¹` iff `ω` is `C^n` on `Ω`).
* Exterior derivative: `mextDeriv_hymLiftCircleForm_coe`: where `ω` is `C¹` at `x`,
  `d(ℱ)` at `(x, [τ])` is `extDeriv (hymLift ω) (x, τ)`.
* Closedness: `mextDeriv_hymLiftCircleForm_eq_zero_iff` (at a point where `ω` is `C¹`:
  `dℱ = 0 ↔ dω = 0 ∧ d⋆ω = 0`), `mextDeriv_hymLiftCircleForm_eq_zero_iff_forall` (`ω` of class
  `C¹`), `hymLiftCircleForm_closed_iff_vacuumForm`, `hymLiftCircleForm_closed_iff_vacuumField`
  (`ω`, `B` of class `C²` on `ℝ³`: closed on `ℝ³ × S¹` iff vacuum on `Set.univ`).
* An open region: `hymLiftCircleForm_closedOn_iff_vacuumForm`/`…_vacuumField` (closed at the
  points of `Ω × S¹`), and on the open submanifold itself
  `hymLiftRegionForm_closed_iff_vacuumForm`/`…_vacuumField`: for `ω` (or `B`) of class `C²` on
  an open `Ω`, the form on the manifold `Ω × S¹` is closed iff `ω` (or `B`) is vacuum on `Ω`.
* Energy: `liftInner_hymLiftAt_flux` (`⟨ℱ(u), ℱ(v)⟩ = 2⟨u, v⟩`), `liftInner_hymLiftAt_flux_self`
  (`|ℱ|² = 2|B|²`), `ymDensity_hymLiftAt_flux` (the Yang–Mills density `½|ℱ|²` is twice the
  magnetic energy density `½|B|²`), and the integrated identity
  `integral_liftInner_hymLiftCircle`: `∫_{Ω × S¹} |ℱ|² = 2ℓ ∫_Ω |B|²`.

## Hypotheses that are needed

The `C¹` hypothesis in the closedness statements on the manifold is used for TauCeti's
naturality of `mextDeriv` under pullback (`mpullback_mextDeriv_at`). Upstairs, on `ℝ³ × ℝ`,
`extDeriv_hymLift_eq_zero_iff` needs no hypothesis; a hypothesis-free statement on the quotient
would need a direct computation in the charts of `AddCircle` and is not proved.

## What is not proved (from inspection of TauCeti v4.36.0)

* Complex structure: TauCeti has `SmoothAlmostComplexStructure`, its Nijenhuis tensor and the
  type predicate `SmoothForm.IsOfType` for an almost complex structure, but no complex-manifold
  structure on `ℝ³ × S¹` (its `IntTranslationQuotient` covers only `ℂ/ℤ`), no
  Newlander–Nirenberg theorem and no primitivity predicate for a Kähler form; so "`ℱ` is of type
  `(1,1)` and primitive" would need the constant structure `J` on `ℝ³ × S¹` as a
  `SmoothAlmostComplexStructure`, a proof that `ℱ` is `IsOfType J 1 1`, and a definition of
  primitivity.
* Holomorphic line bundle: TauCeti has covariant derivatives on vector bundles with their
  curvature 2-form (`CovariantDerivative/Curvature/Form`, `CurvatureForm`), but no construction
  of a line bundle with connection from a closed 2-form with integral periods (Weil's theorem)
  and no holomorphic structure from a connection with `F^{0,2} = 0`; both would have to be built.
* Chern class: TauCeti has the integral Euler class `complexEulerClass` of a complex vector
  bundle but no `c₁` as a de Rham class and no Chern–Weil identification of `[F/2π]` with it, so
  the quantisation condition on the periods of `ℱ` cannot be stated as a statement about a bundle.
* Yang–Mills minimality: TauCeti has a Hodge star, self-dual and anti-self-dual parts of smooth
  forms on an oriented Riemannian manifold and the identity
  `SmoothForm.integral_inner_self_eq_two_mul_sub` (`∫|F|² = 2∫|F⁺|² - ∫F∧F`), but no Yang–Mills
  functional on connections and no Riemannian-manifold instance on `Ω × S¹` tied to `liftStar`;
  minimality would need that instance, the identification of `liftStar` with TauCeti's manifold
  star, compactness or boundary conditions on `Ω`, and the bundle of the previous items.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix TauCeti Bundle
open scoped RealInnerProductSpace Manifold

/-! ## The covering map -/

/-- **The covering map** `ℝ³ × ℝ → ℝ³ × (ℝ/ℓℤ)`, `(x, τ) ↦ (x, [τ])`. -/
def liftCover (ℓ : ℝ) : LiftSpace → Space × AddCircle ℓ :=
  Prod.map (id : Space → Space) ((↑) : ℝ → AddCircle ℓ)

/-- The covering map in components. -/
@[simp] theorem liftCover_apply (ℓ : ℝ) (x : Space) (τ : ℝ) :
    liftCover ℓ (x, τ) = (x, (τ : AddCircle ℓ)) := rfl

/-- The covering map is surjective. -/
theorem liftCover_surjective (ℓ : ℝ) : Function.Surjective (liftCover ℓ) :=
  Function.surjective_id.prodMap QuotientAddGroup.mk_surjective

/-! ## Regularity of the lift on `ℝ³ × ℝ` -/

/-- The lifted form is `C^n` at `(x, τ)` exactly when `ω` is `C^n` at `x`. -/
theorem contDiffAt_hymLift_iff {n : WithTop ℕ∞} (w : Space → Form 2) (x : Space) (τ : ℝ) :
    ContDiffAt ℝ n (hymLift w) (x, τ) ↔ ContDiffAt ℝ n w x := by
  constructor
  · intro h
    have e : w = fun y => sliceCLM (hymLift w (y, τ)) := by
      funext y; rw [hymLift, sliceCLM_hymLiftAt]
    have hm : ContDiffAt ℝ n (fun y : Space => ((y, τ) : LiftSpace)) x :=
      contDiffAt_id.prodMk contDiffAt_const
    have h3 : ContDiffAt ℝ n (fun y : Space => hymLift w (y, τ)) x :=
      ContDiffAt.comp (g := hymLift w) (f := fun y : Space => ((y, τ) : LiftSpace)) x h hm
    rw [e]
    exact sliceCLM.contDiff.contDiffAt.comp x h3
  · intro h
    have e : hymLift w = fun p : LiftSpace => hymLiftCLM (w p.1) := by
      funext p; simp [hymLift]
    have h1 : ContDiffAt ℝ n (fun p : LiftSpace => w p.1) (x, τ) :=
      ContDiffAt.comp (g := w) (f := Prod.fst) (x, τ) h contDiffAt_fst
    rw [e]
    exact hymLiftCLM.contDiff.contDiffAt.comp (x, τ) h1

/-- The lifted form is `C^n` on `ℝ³ × ℝ` exactly when `ω` is `C^n` on `ℝ³`. -/
theorem contDiff_hymLift_iff {n : WithTop ℕ∞} (w : Space → Form 2) :
    ContDiff ℝ n (hymLift w) ↔ ContDiff ℝ n w := by
  simp only [contDiff_iff_contDiffAt]
  exact ⟨fun h x => (contDiffAt_hymLift_iff w x 0).1 (h (x, 0)),
    fun h p => (contDiffAt_hymLift_iff w p.1 p.2).2 (h p.1)⟩

/-- Over the model space `ℝ³ × ℝ`, a form is a `C^n` section at a point exactly when it is a
`C^n` function there (the pointwise form of TauCeti's `isSmoothForm_modelSpace_iff`). -/
theorem contMDiffAt_liftForm_iff {n : WithTop ℕ∞} {k : ℕ}
    (φ : RoughForm 𝓘(ℝ, LiftSpace) LiftSpace ℝ k) (p : LiftSpace) :
    ContMDiffAt 𝓘(ℝ, LiftSpace) (𝓘(ℝ, LiftSpace).prod 𝓘(ℝ, LiftForm k)) n
        (fun y => TotalSpace.mk' (LiftForm k) y (φ y)) p ↔
      ContDiffAt ℝ (E := LiftSpace) (F := LiftForm k) n φ p := by
  constructor
  · intro h
    exact contDiffWithinAt_univ.1
      (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace (contMDiffWithinAt_univ.2 h))
  · intro h
    refine contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_
    rw [RoughForm.inChartAt_modelSpace, modelWithCornersSelf_coe, Set.range_id]
    exact contDiffWithinAt_univ.2 h

section Manifold

variable (ℓ : ℝ) [Fact (0 < ℓ)]

/-- **The covering map is a local diffeomorphism** of every class `C^n`. -/
theorem isLocalDiffeomorph_liftCover (n : WithTop ℕ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ)) n (liftCover ℓ) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (Diffeomorph.refl 𝓘(ℝ, Space) Space n).isLocalDiffeomorph.prodMap
    (AddCircle.isLocalDiffeomorph_coe ℓ n)

/-- Pullback along the covering map is evaluation at the image point, with `ℝ³ × ℝ` read as a
product manifold. -/
theorem mpullback_prodMap_coe_apply {k : ℕ}
    (G : RoughForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) (Space × AddCircle ℓ) ℝ k) (p : Space × ℝ) :
    mpullback (𝓘(ℝ, Space).prod 𝓘(ℝ)) (𝓘(ℝ, Space).prod 𝓘(ℝ))
      (Prod.map (id : Space → Space) ((↑) : ℝ → AddCircle ℓ)) G p =
      G (p.1, (p.2 : AddCircle ℓ)) := by
  refine ContinuousAlternatingMap.ext fun v => ?_
  rw [mpullback_apply,
    mfderiv_prodMap mdifferentiableAt_id (AddCircle.hasMFDerivAt_coe ℓ p.2).mdifferentiableAt,
    mfderiv_id, AddCircle.mfderiv_coe]
  rfl

/-- **Pullback along the covering map is evaluation at the image point**: the derivative of the
covering map is the identity of `ℝ³ × ℝ`. -/
theorem mpullback_liftCover_apply {k : ℕ}
    (G : RoughForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) (Space × AddCircle ℓ) ℝ k) (p : LiftSpace) :
    mpullback 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ)) (liftCover ℓ) G p = G (liftCover ℓ p) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mpullback_prodMap_coe_apply ℓ G p

/-- The pullback of the circle form along the covering map is the lifted form, as forms on the
normed space `ℝ³ × ℝ`. -/
theorem mpullback_liftCover_hymLiftCircleForm (w : Space → Form 2) :
    mpullback 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ)) (liftCover ℓ) (hymLiftCircleForm ℓ w) =
      fun p => hymLift w p := by
  funext p
  rw [mpullback_liftCover_apply]
  rfl

/-! ## Regularity on the circle product -/

/-- **Regularity at a point of `ℝ³ × S¹`**: the circle form is a `C^n` section at `(x, [τ])`
exactly when `ω` is `C^n` at `x`. -/
theorem contMDiffAt_hymLiftCircleForm_iff {n : WithTop ℕ∞} (w : Space → Form 2) (x : Space)
    (θ : AddCircle ℓ) :
    ContMDiffAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) ((𝓘(ℝ, Space).prod 𝓘(ℝ)).prod 𝓘(ℝ, LiftForm 2)) n
        (fun y => TotalSpace.mk' (LiftForm 2) y (hymLiftCircleForm ℓ w y)) (x, θ) ↔
      ContDiffAt ℝ n w x := by
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have h := (isLocalDiffeomorph_liftCover ℓ ⊤ (x, τ)).contMDiffAt_mpullback_form_iff
    (m := n) le_top (ω := hymLiftCircleForm ℓ w) (F := ℝ) (k := 2)
  rw [mpullback_liftCover_hymLiftCircleForm] at h
  exact h.symm.trans ((contMDiffAt_liftForm_iff _ _).trans (contDiffAt_hymLift_iff w x τ))

/-- **Regularity on `ℝ³ × S¹`**: the circle form is a `C^n` form on the manifold exactly when
`ω` is a `C^n` map `ℝ³ → Form 2`. -/
theorem isSmoothForm_hymLiftCircleForm_iff {n : WithTop ℕ∞} (w : Space → Form 2) :
    IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) n (hymLiftCircleForm ℓ w) ↔ ContDiff ℝ n w := by
  rw [isSmoothForm_def, contDiff_iff_contDiffAt]
  exact ⟨fun h x => (contMDiffAt_hymLiftCircleForm_iff ℓ w x 0).1 (h (x, 0)),
    fun h p => (contMDiffAt_hymLiftCircleForm_iff ℓ w p.1 p.2).2 (h p.1)⟩

/-- A `C^n` field of 2-forms has a `C^n` lift on `ℝ³ × S¹`. -/
theorem isSmoothForm_hymLiftCircleForm {n : WithTop ℕ∞} {w : Space → Form 2}
    (hw : ContDiff ℝ n w) : IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) n (hymLiftCircleForm ℓ w) :=
  (isSmoothForm_hymLiftCircleForm_iff ℓ w).2 hw

/-! ## The exterior derivative on the circle product -/

/-- **The exterior derivative of the circle form** at `(x, [τ])` is the exterior derivative of
the lifted form at `(x, τ)`, where `ω` is `C¹` at `x`. The tangent space of `ℝ³ × S¹` at every
point is `ℝ³ × ℝ`. -/
theorem mextDeriv_hymLiftCircleForm_coe {w : Space → Form 2} {x : Space}
    (hw : ContDiffAt ℝ 1 w x) (τ : ℝ) :
    mextDeriv (hymLiftCircleForm ℓ w) (x, (τ : AddCircle ℓ)) = extDeriv (hymLift w) (x, τ) := by
  have hf : ContMDiffAt 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ)) 2 (liftCover ℓ) (x, τ) :=
    (isLocalDiffeomorph_liftCover ℓ 2).contMDiff.contMDiffAt
  have h := mpullback_mextDeriv_at hf (φ := hymLiftCircleForm ℓ w)
    ((contMDiffAt_hymLiftCircleForm_iff ℓ w x (τ : AddCircle ℓ)).2 hw)
  rw [mpullback_liftCover_apply, mpullback_liftCover_hymLiftCircleForm] at h
  exact h.trans (mextDeriv_eq_extDeriv _ _)

/-- **Closedness at a point of `ℝ³ × S¹`**: where `ω` is `C¹`, the circle form is closed at
`(x, θ)` exactly when `dω = 0` and `d(⋆ω) = 0` at `x`. This covers every open region `Ω ⊆ ℝ³`
at once. -/
theorem mextDeriv_hymLiftCircleForm_eq_zero_iff {w : Space → Form 2} {x : Space}
    (hw : ContDiffAt ℝ 1 w x) (θ : AddCircle ℓ) :
    mextDeriv (hymLiftCircleForm ℓ w) (x, θ) = 0 ↔
      extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← extDeriv_hymLift_eq_zero_iff w x τ, ← mextDeriv_hymLiftCircleForm_coe ℓ hw τ]
  rfl

/-- **Closedness on `ℝ³ × S¹`**: for `ω` of class `C¹`, the circle form is closed exactly when
`dω = 0` and `d(⋆ω) = 0` everywhere. -/
theorem mextDeriv_hymLiftCircleForm_eq_zero_iff_forall {w : Space → Form 2}
    (hw : ContDiff ℝ 1 w) :
    mextDeriv (hymLiftCircleForm ℓ w) = 0 ↔
      ∀ x, extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  constructor
  · intro h x
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff ℓ hw.contDiffAt 0).1 (congrFun h (x, 0))
  · intro h
    funext p
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff ℓ hw.contDiffAt p.2).2 (h p.1)

/-- **The circle form is closed exactly for vacuum forms**: for `ω` of class `C²` on `ℝ³`. -/
theorem hymLiftCircleForm_closed_iff_vacuumForm {w : Space → Form 2} (hw : ContDiff ℝ 2 w) :
    mextDeriv (hymLiftCircleForm ℓ w) = 0 ↔ VacuumForm Set.univ w := by
  rw [mextDeriv_hymLiftCircleForm_eq_zero_iff_forall ℓ (hw.of_le (by norm_num))]
  exact ⟨fun h => ⟨isOpen_univ, hw.contDiffOn, fun x _ => (h x).1, fun x _ => (h x).2⟩,
    fun h x => ⟨h.closed x (Set.mem_univ x), h.coclosed x (Set.mem_univ x)⟩⟩

/-- **Vector language**: for a field `B` of class `C²` on `ℝ³`, the lift of its flux form to
`ℝ³ × S¹` is closed exactly when `B` is a vacuum field. -/
theorem hymLiftCircleForm_closed_iff_vacuumField {B : Space → Space} (hB : ContDiff ℝ 2 B) :
    mextDeriv (hymLiftCircleForm ℓ (fluxField B)) = 0 ↔ VacuumField Set.univ B := by
  rw [← vacuumForm_flux_iff]
  exact hymLiftCircleForm_closed_iff_vacuumForm ℓ (flux.toContinuousLinearEquiv.contDiff.comp hB)

/-! ## An open region `Ω × S¹` -/

/-- **Closedness at the points of `Ω × S¹`** for an open `Ω ⊆ ℝ³` and `ω` of class `C²` on
`Ω`: the circle form is closed at every point of `Ω × S¹` exactly when `ω` is a vacuum form on
`Ω`. -/
theorem hymLiftCircleForm_closedOn_iff_vacuumForm {Ω : Set Space} {w : Space → Form 2}
    (hΩ : IsOpen Ω) (hw : ContDiffOn ℝ 2 w Ω) :
    (∀ p ∈ Ω ×ˢ (Set.univ : Set (AddCircle ℓ)), mextDeriv (hymLiftCircleForm ℓ w) p = 0) ↔
      VacuumForm Ω w := by
  have h1 (x : Space) (hx : x ∈ Ω) : ContDiffAt ℝ 1 w x :=
    (hw.contDiffAt (hΩ.mem_nhds hx)).of_le (by norm_num)
  constructor
  · intro h
    refine ⟨hΩ, hw, fun x hx => ?_, fun x hx => ?_⟩
    · exact ((mextDeriv_hymLiftCircleForm_eq_zero_iff ℓ (h1 x hx) 0).1
        (h (x, 0) ⟨hx, Set.mem_univ _⟩)).1
    · exact ((mextDeriv_hymLiftCircleForm_eq_zero_iff ℓ (h1 x hx) 0).1
        (h (x, 0) ⟨hx, Set.mem_univ _⟩)).2
  · rintro h ⟨x, θ⟩ ⟨hx, -⟩
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff ℓ (h1 x hx) θ).2
      ⟨h.closed x hx, h.coclosed x hx⟩

/-- Vector language for the points of `Ω × S¹`: for `B` of class `C²` on an open `Ω`, the lift
of its flux form is closed at every point of `Ω × S¹` exactly when `B` is a vacuum field on
`Ω`. -/
theorem hymLiftCircleForm_closedOn_iff_vacuumField {Ω : Set Space} {B : Space → Space}
    (hΩ : IsOpen Ω) (hB : ContDiffOn ℝ 2 B Ω) :
    (∀ p ∈ Ω ×ˢ (Set.univ : Set (AddCircle ℓ)),
        mextDeriv (hymLiftCircleForm ℓ (fluxField B)) p = 0) ↔ VacuumField Ω B := by
  rw [← vacuumForm_flux_iff]
  exact hymLiftCircleForm_closedOn_iff_vacuumForm ℓ hΩ
    (flux.toContinuousLinearEquiv.comp_contDiffOn_iff.2 hB)

/-- **The region `Ω × S¹`** as an open subset of the manifold `ℝ³ × S¹`. -/
def circleRegion (U : TopologicalSpace.Opens Space) :
    TopologicalSpace.Opens (Space × AddCircle ℓ) :=
  ⟨(U : Set Space) ×ˢ (Set.univ : Set (AddCircle ℓ)), U.isOpen.prod isOpen_univ⟩

omit [Fact (0 < ℓ)] in
/-- Membership in the region `Ω × S¹`. -/
@[simp] theorem mem_circleRegion {U : TopologicalSpace.Opens Space} {p : Space × AddCircle ℓ} :
    p ∈ circleRegion ℓ U ↔ p.1 ∈ U := by
  simp [circleRegion, ← SetLike.mem_coe]

/-- **The lifted form on the manifold `Ω × S¹`**: the restriction of the circle form to the
open submanifold `circleRegion ℓ U`. -/
noncomputable def hymLiftRegionForm (U : TopologicalSpace.Opens Space) (w : Space → Form 2) :
    RoughForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) (circleRegion ℓ U) ℝ 2 :=
  mpullback (𝓘(ℝ, Space).prod 𝓘(ℝ)) (𝓘(ℝ, Space).prod 𝓘(ℝ))
    (Subtype.val : circleRegion ℓ U → Space × AddCircle ℓ) (hymLiftCircleForm ℓ w)

/-- The form on `Ω × S¹` has the values of the circle form. -/
theorem hymLiftRegionForm_apply (U : TopologicalSpace.Opens Space) (w : Space → Form 2)
    (p : circleRegion ℓ U) :
    hymLiftRegionForm ℓ U w p = hymLiftCircleForm ℓ w p :=
  mpullback_subtype_val_apply _ p

/-- **Regularity on `Ω × S¹`**: the lifted form is a `C^n` form on the manifold `Ω × S¹`
exactly when `ω` is `C^n` on `Ω`. -/
theorem isSmoothForm_hymLiftRegionForm_iff {n : WithTop ℕ∞} (U : TopologicalSpace.Opens Space)
    (w : Space → Form 2) :
    IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) n (hymLiftRegionForm ℓ U w) ↔ ContDiffOn ℝ n w U := by
  have key (p : circleRegion ℓ U) :
      ContMDiffAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) ((𝓘(ℝ, Space).prod 𝓘(ℝ)).prod 𝓘(ℝ, LiftForm 2)) n
        (fun y => TotalSpace.mk' (LiftForm 2) y (hymLiftRegionForm ℓ U w y)) p ↔
      ContDiffAt ℝ n w p.1.1 :=
    ((isLocalDiffeomorph_subtype_val (n := ⊤) p).contMDiffAt_mpullback_form_iff
      (m := n) le_top (ω := hymLiftCircleForm ℓ w)).trans
      (contMDiffAt_hymLiftCircleForm_iff ℓ w p.1.1 p.1.2)
  rw [isSmoothForm_def]
  constructor
  · intro h x hx
    exact ((key ⟨(x, 0), (mem_circleRegion ℓ).2 hx⟩).1 (h _)).contDiffWithinAt
  · intro h p
    exact (key p).2 ((h p.1.1 ((mem_circleRegion ℓ).1 p.2)).contDiffAt
      (U.isOpen.mem_nhds ((mem_circleRegion ℓ).1 p.2)))

/-- **The exterior derivative on `Ω × S¹`** is the restriction of the exterior derivative on
`ℝ³ × S¹`, at the points over which `ω` is `C¹`. -/
theorem mextDeriv_hymLiftRegionForm (U : TopologicalSpace.Opens Space) {w : Space → Form 2}
    (p : circleRegion ℓ U) (hw : ContDiffAt ℝ 1 w p.1.1) :
    mextDeriv (hymLiftRegionForm ℓ U w) p = mextDeriv (hymLiftCircleForm ℓ w) p := by
  have h := mpullback_mextDeriv_at (f := (Subtype.val : circleRegion ℓ U → Space × AddCircle ℓ))
    (x := p) (I := 𝓘(ℝ, Space).prod 𝓘(ℝ)) (I' := 𝓘(ℝ, Space).prod 𝓘(ℝ))
    contMDiff_subtype_val.contMDiffAt (φ := hymLiftCircleForm ℓ w)
    ((contMDiffAt_hymLiftCircleForm_iff ℓ w p.1.1 p.1.2).2 hw)
  rw [mpullback_subtype_val_apply] at h
  exact h.symm

/-- **Closedness on the manifold `Ω × S¹`**: for an open `Ω ⊆ ℝ³` and `ω` of class `C²` on `Ω`,
the lifted form on `Ω × S¹` is closed exactly when `ω` is a vacuum form on `Ω`. -/
theorem hymLiftRegionForm_closed_iff_vacuumForm (U : TopologicalSpace.Opens Space)
    {w : Space → Form 2} (hw : ContDiffOn ℝ 2 w U) :
    mextDeriv (hymLiftRegionForm ℓ U w) = 0 ↔ VacuumForm U w := by
  have h1 (x : Space) (hx : x ∈ U) : ContDiffAt ℝ 1 w x :=
    (hw.contDiffAt (U.isOpen.mem_nhds hx)).of_le (by norm_num)
  rw [← hymLiftCircleForm_closedOn_iff_vacuumForm ℓ U.isOpen hw]
  constructor
  · rintro h ⟨x, θ⟩ ⟨hx, -⟩
    have hp : (x, θ) ∈ circleRegion ℓ U := (mem_circleRegion ℓ).2 hx
    rw [← mextDeriv_hymLiftRegionForm ℓ U ⟨(x, θ), hp⟩ (h1 x hx), h]
    rfl
  · intro h
    funext p
    rw [mextDeriv_hymLiftRegionForm ℓ U p (h1 _ ((mem_circleRegion ℓ).1 p.2))]
    exact h p.1 ⟨(mem_circleRegion ℓ).1 p.2, Set.mem_univ _⟩

/-- **Vector language on the manifold `Ω × S¹`**: for `B` of class `C²` on an open `Ω`, the
lift of its flux form to `Ω × S¹` is closed exactly when `B` is a vacuum field on `Ω`. -/
theorem hymLiftRegionForm_closed_iff_vacuumField (U : TopologicalSpace.Opens Space)
    {B : Space → Space} (hB : ContDiffOn ℝ 2 B U) :
    mextDeriv (hymLiftRegionForm ℓ U (fluxField B)) = 0 ↔ VacuumField U B := by
  rw [← vacuumForm_flux_iff]
  exact hymLiftRegionForm_closed_iff_vacuumForm ℓ U
    (flux.toContinuousLinearEquiv.comp_contDiffOn_iff.2 hB)

end Manifold

/-! ## The energy identity -/

/-- **Pointwise energy identity, polarised**: `⟨ℱ(u), ℱ(v)⟩ = 2 ⟨u, v⟩` for the lifts of the
flux forms of two vectors; the spatial part and the `dτ` part each contribute `⟨u, v⟩`. -/
theorem liftInner_hymLiftAt_flux (u v : Space) :
    liftInner (hymLiftAt (flux u)) (hymLiftAt (flux v)) = 2 * ⟪u, v⟫ := by
  rw [liftInner_eq]
  simp only [hymLiftAt_apply, hodge_flux, flux_apply, volForm_vec, flat_apply]
  simp [coordVec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- **Pointwise energy identity**: `|ℱ|² = 2 |B|²` for the lift of the flux form of `B`. -/
theorem liftInner_hymLiftAt_flux_self (v : Space) :
    liftInner (hymLiftAt (flux v)) (hymLiftAt (flux v)) = 2 * ‖v‖ ^ 2 := by
  rw [liftInner_hymLiftAt_flux, real_inner_self_eq_norm_sq]

/-- The pointwise energy identity for an arbitrary 2-form `b` on `ℝ³`: `|ℱ|² = 2 |B|²` with
`B = flux⁻¹ b` the vector of `b`. -/
theorem liftInner_hymLiftAt_self (b : Form 2) :
    liftInner (hymLiftAt b) (hymLiftAt b) = 2 * ‖flux.symm b‖ ^ 2 := by
  rw [← liftInner_hymLiftAt_flux_self, LinearEquiv.apply_symm_apply]

/-- **The Yang–Mills density** `½ |F|²` of a 2-form on `ℝ³ × ℝ` (a curvature form of a `U(1)`
connection), for the product Euclidean metric. -/
noncomputable def ymDensity (F : LiftForm 2) : ℝ := liftInner F F / 2

/-- **The Yang–Mills density of the lift is twice the magnetic energy density**:
`½ |ℱ|² = 2 · (½ |B|²)`. -/
theorem ymDensity_hymLiftAt_flux (v : Space) :
    ymDensity (hymLiftAt (flux v)) = 2 * (‖v‖ ^ 2 / 2) := by
  rw [ymDensity, liftInner_hymLiftAt_flux_self]
  ring

/-- The energy identity at a point of `ℝ³ × S¹`: `|ℱ|² = 2 |B|²`. -/
theorem liftInner_hymLiftCircle_fluxField (ℓ : ℝ) (B : Space → Space) (p : Space × AddCircle ℓ) :
    liftInner (hymLiftCircle ℓ (fluxField B) p) (hymLiftCircle ℓ (fluxField B) p) =
      2 * ‖B p.1‖ ^ 2 := by
  rw [hymLiftCircle_eq, fluxField_apply, liftInner_hymLiftAt_flux_self]

/-- The Yang–Mills density of the lift at a point of `ℝ³ × S¹` is twice the magnetic energy
density `½ |B|²`. -/
theorem ymDensity_hymLiftCircle_fluxField (ℓ : ℝ) (B : Space → Space)
    (p : Space × AddCircle ℓ) :
    ymDensity (hymLiftCircle ℓ (fluxField B) p) = 2 * (‖B p.1‖ ^ 2 / 2) := by
  rw [hymLiftCircle_eq, fluxField_apply, ymDensity_hymLiftAt_flux]

open MeasureTheory in
/-- **The integrated energy identity** `∫_{Ω × S¹} |ℱ|² = 2ℓ ∫_Ω |B|²`, for every set `Ω` and
every field `B` (both sides are Bochner integrals, so both are `0` when `|B|²` is not
integrable on `Ω`). The measure on `ℝ³ × S¹` is the product of Lebesgue measure and the Haar
measure of total mass `ℓ` on `ℝ/ℓℤ`. -/
theorem integral_liftInner_hymLiftCircle (ℓ : ℝ) [Fact (0 < ℓ)] (B : Space → Space)
    (Ω : Set Space) :
    ∫ p in Ω ×ˢ (Set.univ : Set (AddCircle ℓ)),
        liftInner (hymLiftCircle ℓ (fluxField B) p) (hymLiftCircle ℓ (fluxField B) p) =
      2 * ℓ * ∫ x in Ω, ‖B x‖ ^ 2 := by
  have hm : (volume : Measure (Space × AddCircle ℓ)).restrict (Ω ×ˢ Set.univ) =
      (volume.restrict Ω).prod (volume : Measure (AddCircle ℓ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hℓ : (volume : Measure (AddCircle ℓ)).real Set.univ = ℓ := by
    rw [Measure.real, AddCircle.measure_univ, ENNReal.toReal_ofReal (Fact.out : 0 < ℓ).le]
  simp only [liftInner_hymLiftCircle_fluxField]
  rw [hm, integral_fun_fst (fun x : Space => 2 * ‖B x‖ ^ 2), hℓ, integral_const_mul,
    smul_eq_mul]
  ring

end PlasmaLean.Forms
