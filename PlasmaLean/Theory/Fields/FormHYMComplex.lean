/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMCircle
public import PlasmaLean.Theory.Fields.FieldDerivative

/-!
# The complex structure of the anti-self-dual lift: type `(1,1)` and primitivity

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, section "A
complex-surface lift that retains the Euclidean metric" (line 1; assessment claim S-13,
orientation note N-37 in `notes/theory/holomorphic-lift-orientation-patch.md`). This file
continues `Theory/Fields/FormHYMLift`, `FormHYMStar` and `FormHYMCircle`. It supplies the
pointwise complex geometry of the lift `ℱ = π^*ω - π^*(⋆₃ω) ∧ dτ` (the source's "closed
primitive form of type `(1,1)`", lines 16–18 and 35, and "the primitive condition is the
Abelian Hermitian–Yang–Mills equation", line 45), and it removes the `C¹` hypothesis from the
closedness statements on the circle product.

## Conventions

* Complex structure. The source (line 18) uses the complex coordinates `u = x + iy`,
  `w = exp(2π(z + it)/ℓ)` on `Ω × S¹`; `log w` is a multiple of `z + it`, so in the orthonormal
  frame `(e₀, e₁, e₂, e_τ)` the complex structure is `J e₀ = e₁`, `J e₁ = -e₀`, `J e₂ = e_τ`,
  `J e_τ = -e₂`. The source uses only this direction. Here `liftJ n` is defined for every
  vector `n` of `ℝ³`: `J(u, s) = (n × u - s n, ⟨n, u⟩)`. For a unit `n` it pairs `n` with
  `e_τ` and rotates the plane `n^⊥` by a quarter turn; `liftJ (coordVec 2)` is the structure
  of the source (`liftJ_coordVec_two_frame`). In general `J² = -|n|²` (`liftJ_liftJ`).
* Metric: the product Euclidean metric, written `liftDot p q = ⟨p.1, q.1⟩ + p.2 q.2`; it is
  the inner product of `LiftEuclid = WithLp 2 (ℝ³ × ℝ)` (`liftDot_eq_inner`).
* Kähler form: `ω_J(p, q) = ⟨Jp, q⟩` (`kahlerForm_apply`), that is
  `ω_J = π^*(ι_n vol) + π^*(n♭) ∧ dτ`. For `n = e₂` it is `dx₀ ∧ dx₁ + dx₂ ∧ dτ`
  (`kahlerForm_coordVec_two`), which is the source's
  `ω = (i/2) du ∧ dū + (iℓ²/(8π²|w|²)) dw ∧ dw̄` (lines 22–25) in the coordinates `(x, y, z, t)`.
* Orientation. The complex orientation of `liftJ n` (that of a frame `(X, JX, Y, JY)`) is the
  orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ` of the source (line 10) and of `liftOrientation`, for
  every unit `n`: `ω_J ∧ ω_J = 2 vol` (`kahlerForm_wedge_kahlerForm`), the Kähler form is
  self-dual (`liftStar_kahlerForm`), and for `n = e₂` the complex frame `(e₀, Je₀, e₂, Je₂)`
  is the standard frame (`liftVol_complexFrame`). So the statement that holds is the one with
  anti-self-dual forms, as in the source (line 35). This agrees with N-37: there the lift is
  written `dτ ∧ α - β` with the orientation `dτ ∧ vol₃` and the complex coordinates
  `τ + i x₁`, `x₂ + i x₃`, whose complex orientation is again the orientation for which the
  lift is anti-self-dual. The structure of N-37 pairs `e_τ` with a spatial direction in the
  opposite order, so it is not one of the `liftJ n`; its complex orientation is `-liftOrientation`,
  for which the star is `-liftStar` (`euclidForm_neg_liftStar`).
* Type `(1,1)` for a real 2-form: `F(Jp, Jq) = F(p, q)` (`IsType11`). Primitive:
  `ΛF = ⟨F, ω_J⟩ = 0` (`IsPrimitive`), with `liftInner` the inner product of 2-forms.

## What is proved

* `liftJ_liftJ_of_norm_eq_one`, `liftJ_comp_liftJ` (`J² = -1`),
  `liftDot_liftJ_liftJ_of_norm_eq_one` (`J` is an isometry), `liftDot_liftJ_left` (`J` is skew).
* `liftForm2_liftJ_apply`: for every 2-form `F` and every `n`,
  `F(Jp, Jq) = ⟨F, ω_J⟩ ω_J(p, q) - |n|² (⋆F)(p, q)`. Everything below follows from it.
* `isType11_iff`: `F` is of type `(1,1)` iff `F + ⋆F = ⟨F, ω_J⟩ ω_J` (the forms of type `(1,1)`
  are the anti-self-dual forms plus the multiples of the Kähler form).
* **`liftStar_eq_neg_iff_isType11_and_isPrimitive`**: for a unit `n`,
  `⋆F = -F ↔ IsType11 n F ∧ IsPrimitive n F`. The anti-self-dual 2-forms are exactly the
  primitive forms of type `(1,1)`.
* `isType11_kahlerForm`, `not_isPrimitive_kahlerForm`; `eq_zero_of_liftStar_eq_self` (no
  non-zero self-dual form is primitive of type `(1,1)`); `isType11_sdLiftAt_flux_iff` (the
  self-dual lift of the field `C` is of type `(1,1)` iff `C` is parallel to `n`).
* The lift: `isType11_hymLiftAt`, `isPrimitive_hymLiftAt`, `isType11_and_isPrimitive_hymLift`,
  `isType11_and_isPrimitive_hymLiftCircle`: for every field of 2-forms and every unit `n` the
  lifted form is of type `(1,1)` and primitive at every point. No field equation is used. The
  source states this for its one complex structure; it holds for the whole 2-sphere of
  structures `liftJ n`.
* Closedness with no regularity hypothesis: `inChartAt_hymLiftCircleForm` (the coordinate
  expression of the circle form in a chart of `ℝ³ × S¹` is `hymLift ω`),
  `mextDeriv_hymLiftCircleForm_coe'`, `mextDeriv_hymLiftCircleForm_eq_zero_iff'`
  (`dℱ = 0 ↔ dω = 0 ∧ d⋆ω = 0` at every point, for every `ω`),
  `mextDeriv_hymLiftCircleForm_eq_zero_iff_forall'`, `hymLiftCircleForm_closedOn_iff`, and on
  the open submanifold `Ω × S¹`: `mextDeriv_hymLiftRegionForm'`,
  `mextDeriv_hymLiftRegionForm_eq_zero_iff`. TauCeti's `mextDeriv φ x` is
  `extDerivWithin (φ.inChartAt x) (range I) (extChartAt I x x)`, so at a point where the
  coordinate expression is not differentiable it is the junk value `0`
  (`mextDeriv_hymLiftCircleForm_of_not_differentiableAt`); there the iff is `True ↔ True`.

## What is not proved

* The statements with `VacuumForm`/`VacuumField` keep their `C²` hypothesis: regularity is a
  field of `VacuumForm`, so it cannot be removed from an iff with a vacuum form.
* `J` as an integrable complex structure on the manifold `Ω × S¹` (a
  `SmoothAlmostComplexStructure`, holomorphic coordinates `u`, `w`, the Kähler metric formula
  of the source), the holomorphic line bundle, its Chern class and Yang–Mills minimality.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix TauCeti
open scoped RealInnerProductSpace Manifold

/-! ## Coordinates -/

/-- The components of the cross product. -/
theorem cross_components (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
      cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross, cross_apply]

/-- The Euclidean inner product of `ℝ³` in components. -/
theorem inner_components (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- The squared norm in components. -/
theorem norm_sq_components (n : Space) : ‖n‖ ^ 2 = n 0 * n 0 + n 1 * n 1 + n 2 * n 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_components]

/-! ## The product inner product and the complex structure -/

/-- The product Euclidean inner product on `ℝ³ × ℝ`: `⟨(u, s), (v, t)⟩ = ⟨u, v⟩ + s t`. -/
noncomputable def liftDot (p q : LiftSpace) : ℝ := ⟪p.1, q.1⟫ + p.2 * q.2

/-- `liftDot` is the inner product of the Euclidean lift space `WithLp 2 (ℝ³ × ℝ)`. -/
theorem liftDot_eq_inner (p q : LiftSpace) :
    liftDot p q = ⟪(WithLp.toLp 2 p : LiftEuclid), WithLp.toLp 2 q⟫ := by
  simp only [liftDot, WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial]
  ring

/-- The product inner product is symmetric. -/
theorem liftDot_comm (p q : LiftSpace) : liftDot p q = liftDot q p := by
  simp only [liftDot, real_inner_comm q.1 p.1]
  ring

/-- **The complex structure** of the source on `ℝ³ × ℝ` for the direction `n`:
`J(u, s) = (n × u - s n, ⟨n, u⟩)`. For a unit vector `n` it sends `(n, 0)` to `(0, 1)` and
`(0, 1)` to `(-n, 0)`, and it rotates the plane `n^⊥` by a quarter turn. -/
noncomputable def liftJ (n : Space) : LiftSpace →L[ℝ] LiftSpace :=
  ((crossBilinear n).comp (ContinuousLinearMap.fst ℝ Space ℝ) -
      (ContinuousLinearMap.snd ℝ Space ℝ).smulRight n).prod
    ((innerSL ℝ n).comp (ContinuousLinearMap.fst ℝ Space ℝ))

/-- The complex structure in components. -/
theorem liftJ_apply (n u : Space) (s : ℝ) :
    liftJ n (u, s) = (cross n u - s • n, ⟪n, u⟫) := rfl

/-- **`J² = -|n|²`** for every `n`. -/
theorem liftJ_liftJ (n : Space) (p : LiftSpace) :
    liftJ n (liftJ n p) = -(‖n‖ ^ 2 • p) := by
  obtain ⟨u, s⟩ := p
  obtain ⟨c0, c1, c2⟩ := cross_components n u
  rw [liftJ_apply, liftJ_apply]
  refine Prod.ext ?_ ?_
  · ext i
    obtain ⟨d0, d1, d2⟩ := cross_components n (cross n u - s • n)
    fin_cases i <;>
      simp [d0, d1, d2, c0, c1, c2, norm_sq_components, inner_components] <;> ring
  · simp [c0, c1, c2, norm_sq_components, inner_components]
    ring

/-- **`J² = -1`** for a unit vector `n`. -/
theorem liftJ_liftJ_of_norm_eq_one {n : Space} (hn : ‖n‖ = 1) (p : LiftSpace) :
    liftJ n (liftJ n p) = -p := by
  rw [liftJ_liftJ, hn, one_pow, one_smul]

/-- **`J ∘ J = -1`** for a unit vector `n`, as continuous linear maps. -/
theorem liftJ_comp_liftJ {n : Space} (hn : ‖n‖ = 1) :
    (liftJ n).comp (liftJ n) = -ContinuousLinearMap.id ℝ LiftSpace := by
  refine ContinuousLinearMap.ext fun p => ?_
  exact liftJ_liftJ_of_norm_eq_one hn p

/-- `⟨Jp, Jq⟩ = |n|² ⟨p, q⟩` for every `n`. -/
theorem liftDot_liftJ_liftJ (n : Space) (p q : LiftSpace) :
    liftDot (liftJ n p) (liftJ n q) = ‖n‖ ^ 2 * liftDot p q := by
  obtain ⟨u, s⟩ := p
  obtain ⟨v, t⟩ := q
  obtain ⟨c0, c1, c2⟩ := cross_components n u
  obtain ⟨d0, d1, d2⟩ := cross_components n v
  simp [liftJ_apply, liftDot, inner_components, norm_sq_components, c0, c1, c2, d0, d1, d2]
  ring

/-- **`J` is an isometry of the product metric** for a unit vector `n`. -/
theorem liftDot_liftJ_liftJ_of_norm_eq_one {n : Space} (hn : ‖n‖ = 1) (p q : LiftSpace) :
    liftDot (liftJ n p) (liftJ n q) = liftDot p q := by
  rw [liftDot_liftJ_liftJ, hn, one_pow, one_mul]

/-- `J` is skew for the product metric, for every `n`: `⟨Jp, q⟩ = -⟨p, Jq⟩`. -/
theorem liftDot_liftJ_left (n : Space) (p q : LiftSpace) :
    liftDot (liftJ n p) q = -liftDot p (liftJ n q) := by
  obtain ⟨u, s⟩ := p
  obtain ⟨v, t⟩ := q
  obtain ⟨c0, c1, c2⟩ := cross_components n u
  obtain ⟨d0, d1, d2⟩ := cross_components n v
  simp [liftJ_apply, liftDot, inner_components, c0, c1, c2, d0, d1, d2]
  ring

/-! ## The Kähler form -/

/-- **The Kähler form** `ω_J = π^*(ι_n vol) + π^*(n♭) ∧ dτ` of the complex structure `liftJ n`
and the product metric. For `n = e₂` it is `dx₀ ∧ dx₁ + dx₂ ∧ dτ`, the form of the source. -/
noncomputable def kahlerForm (n : Space) : LiftForm 2 := ofParts (flux n) (flat n)

/-- **The Kähler form is `ω(p, q) = ⟨Jp, q⟩`**, for every `n`. -/
theorem kahlerForm_apply (n : Space) (p q : LiftSpace) :
    kahlerForm n ![p, q] = liftDot (liftJ n p) q := by
  obtain ⟨u, s⟩ := p
  obtain ⟨v, t⟩ := q
  obtain ⟨c0, c1, c2⟩ := cross_components n u
  rw [kahlerForm, ofParts_apply, flux_apply, volForm_vec]
  simp [liftJ_apply, liftDot, inner_components, c0, c1, c2]
  ring

/-- **The Kähler form is self-dual** for the orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`, for every
`n`. -/
theorem liftStar_kahlerForm (n : Space) : liftStar (kahlerForm n) = kahlerForm n := by
  simp [kahlerForm]

/-- The Kähler form is a self-dual form. -/
theorem kahlerForm_mem_selfDualForms (n : Space) : kahlerForm n ∈ selfDualForms :=
  mem_selfDualForms.2 (liftStar_kahlerForm n)

/-- The Kähler form of the direction `e₂` is `dx₀ ∧ dx₁ + dx₂ ∧ dτ`, the Kähler form of the
source. -/
theorem kahlerForm_coordVec_two :
    kahlerForm (coordVec 2) =
      (ContinuousAlternatingMap.wedge (dX 0) (dX 1) : LiftForm 2) +
        (ContinuousAlternatingMap.wedge (dX 2) dTau : LiftForm 2) := by
  rw [dX_wedge_dX.2.2, dX_wedge_dTau, ← ofParts_add, add_zero, zero_add, kahlerForm]

/-- Every 2-form on the lift space is `π^*(ι_A vol) + π^*(E♭) ∧ dτ` for two vectors `A`, `E`
of `ℝ³`. -/
theorem exists_eq_ofParts_flux_flat (F : LiftForm 2) :
    ∃ A E : Space, F = ofParts (flux A) (flat E) := by
  obtain ⟨A, hA⟩ := flux.surjective (spatialPart F)
  obtain ⟨E, hE⟩ := flat.surjective (mixedPart F)
  exact ⟨A, E, by rw [hA, hE, ofParts_parts]⟩

/-- **The inner product of 2-forms in vector language**: for
`F = π^*(ι_A vol) + π^*(E♭) ∧ dτ` and `F' = π^*(ι_A' vol) + π^*(E'♭) ∧ dτ`,
`⟨F, F'⟩ = ⟨A, A'⟩ + ⟨E, E'⟩`. -/
theorem liftInner_ofParts_flux_flat (A E A' E' : Space) :
    liftInner (ofParts (flux A) (flat E)) (ofParts (flux A') (flat E')) =
      ⟪A, A'⟫ + ⟪E, E'⟫ := by
  rw [liftInner_eq]
  simp only [ofParts_apply, flux_apply, volForm_vec, flat_apply]
  simp [coordVec, inner_components]
  ring

/-- **`|ω_J|² = 2 |n|²`.** -/
theorem liftInner_kahlerForm_self (n : Space) :
    liftInner (kahlerForm n) (kahlerForm n) = 2 * ‖n‖ ^ 2 := by
  rw [kahlerForm, liftInner_ofParts_flux_flat, real_inner_self_eq_norm_sq]
  ring

/-- **Anti-self-dual and self-dual forms are orthogonal.** -/
theorem liftInner_eq_zero_of_liftStar {F G : LiftForm 2} (hF : liftStar F = -F)
    (hG : liftStar G = G) : liftInner F G = 0 := by
  obtain ⟨A, hA⟩ := flux.surjective (spatialPart F)
  obtain ⟨C, hC⟩ := flux.surjective (spatialPart G)
  have eF : F = ofParts (flux A) (flat (-A)) := by
    rw [eq_hymLiftAt_of_liftStar_eq_neg hF, ← hA, hymLiftAt_eq_ofParts, hodge_flux, map_neg]
  have eG : G = ofParts (flux C) (flat C) := by
    rw [eq_sdLiftAt_of_liftStar_eq_self hG, ← hC, sdLiftAt, hodge_flux]
  rw [eF, eG, liftInner_ofParts_flux_flat, inner_neg_left]
  ring

/-- **The action of `J` on 2-forms.** For every 2-form `F` and every `n`,
`F(Jp, Jq) = ⟨F, ω_J⟩ ω_J(p, q) - |n|² (⋆F)(p, q)`. So for a unit `n` the involution
`F ↦ F(J·, J·)` is `-⋆` on the orthogonal complement of the Kähler form and the identity on
the Kähler form. -/
theorem liftForm2_liftJ_apply (n : Space) (F : LiftForm 2) (p q : LiftSpace) :
    F ![liftJ n p, liftJ n q] =
      liftInner F (kahlerForm n) * kahlerForm n ![p, q] - ‖n‖ ^ 2 * liftStar F ![p, q] := by
  obtain ⟨A, E, rfl⟩ := exists_eq_ofParts_flux_flat F
  obtain ⟨u, s⟩ := p
  obtain ⟨v, t⟩ := q
  obtain ⟨c0, c1, c2⟩ := cross_components n u
  obtain ⟨d0, d1, d2⟩ := cross_components n v
  rw [liftStar_ofParts, hodge_symm_flat, hodge_flux, kahlerForm, liftInner_ofParts_flux_flat,
    liftJ_apply, liftJ_apply]
  simp only [ofParts_apply, flux_apply, volForm_vec, flat_apply]
  simp [inner_components, norm_sq_components, c0, c1, c2, d0, d1, d2]
  ring

/-! ## Type `(1,1)` and primitivity -/

/-- **Type `(1,1)`** for the complex structure `liftJ n`: a real 2-form is of type `(1,1)`
exactly when it is invariant under `J`, `F(Jp, Jq) = F(p, q)`. -/
def IsType11 (n : Space) (F : LiftForm 2) : Prop :=
  ∀ p q : LiftSpace, F ![liftJ n p, liftJ n q] = F ![p, q]

/-- **Primitivity**: a 2-form is primitive when it is orthogonal to the Kähler form,
`ΛF = ⟨F, ω_J⟩ = 0`. -/
def IsPrimitive (n : Space) (F : LiftForm 2) : Prop := liftInner F (kahlerForm n) = 0

/-- **The forms of type `(1,1)`** for a unit `n` are those whose self-dual part is a multiple
of the Kähler form: `F` is of type `(1,1)` exactly when `F + ⋆F = ⟨F, ω_J⟩ ω_J`. -/
theorem isType11_iff {n : Space} (hn : ‖n‖ = 1) (F : LiftForm 2) :
    IsType11 n F ↔ F + liftStar F = liftInner F (kahlerForm n) • kahlerForm n := by
  constructor
  · intro h
    apply liftForm2_ext
    intro u v s t
    have k := liftForm2_liftJ_apply n F (u, s) (v, t)
    rw [h, hn, one_pow, one_mul] at k
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    linarith
  · intro h p q
    have k := congrArg (fun G : LiftForm 2 => G ![p, q]) h
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at k
    rw [liftForm2_liftJ_apply, hn, one_pow, one_mul]
    linarith

/-- **The anti-self-dual 2-forms are exactly the primitive forms of type `(1,1)`**, for the
orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ` and the complex structure `liftJ n` of any unit vector
`n`. -/
theorem liftStar_eq_neg_iff_isType11_and_isPrimitive {n : Space} (hn : ‖n‖ = 1)
    (F : LiftForm 2) : liftStar F = -F ↔ IsType11 n F ∧ IsPrimitive n F := by
  constructor
  · intro h
    have hp : liftInner F (kahlerForm n) = 0 :=
      liftInner_eq_zero_of_liftStar h (liftStar_kahlerForm n)
    refine ⟨fun p q => ?_, hp⟩
    rw [liftForm2_liftJ_apply, hp, h, hn]
    simp
  · rintro ⟨h1, h2⟩
    apply liftForm2_ext
    intro u v s t
    have k := liftForm2_liftJ_apply n F (u, s) (v, t)
    rw [h1, h2, hn] at k
    simp only [ContinuousAlternatingMap.neg_apply]
    linarith

/-- The same statement for the component definition `IsAntiSelfDual` of `FormHYMLift`. -/
theorem isAntiSelfDual_iff_isType11_and_isPrimitive {n : Space} (hn : ‖n‖ = 1)
    (F : LiftForm 2) : IsAntiSelfDual F ↔ IsType11 n F ∧ IsPrimitive n F := by
  rw [isAntiSelfDual_iff_liftStar, liftStar_eq_neg_iff_isType11_and_isPrimitive hn]

/-- The anti-self-dual forms as a set: the primitive forms of type `(1,1)`. -/
theorem mem_antiSelfDualForms_iff_isType11_and_isPrimitive {n : Space} (hn : ‖n‖ = 1)
    {F : LiftForm 2} : F ∈ antiSelfDualForms ↔ IsType11 n F ∧ IsPrimitive n F := by
  rw [mem_antiSelfDualForms, liftStar_eq_neg_iff_isType11_and_isPrimitive hn]

/-- **The Kähler form is of type `(1,1)`.** -/
theorem isType11_kahlerForm {n : Space} (hn : ‖n‖ = 1) : IsType11 n (kahlerForm n) := by
  rw [isType11_iff hn, liftStar_kahlerForm, liftInner_kahlerForm_self, hn, ← two_smul ℝ]
  norm_num

/-- **The Kähler form is not primitive**: `⟨ω_J, ω_J⟩ = 2`. -/
theorem not_isPrimitive_kahlerForm {n : Space} (hn : ‖n‖ = 1) :
    ¬ IsPrimitive n (kahlerForm n) := by
  rw [IsPrimitive, liftInner_kahlerForm_self, hn]
  norm_num

/-- **A self-dual form of type `(1,1)` is a multiple of the Kähler form**:
`F = ½ ⟨F, ω_J⟩ ω_J`. -/
theorem eq_smul_kahlerForm_of_liftStar_eq_self {n : Space} (hn : ‖n‖ = 1) {F : LiftForm 2}
    (hF : liftStar F = F) (h : IsType11 n F) :
    F = (liftInner F (kahlerForm n) / 2) • kahlerForm n := by
  have k := (isType11_iff hn F).1 h
  rw [hF, ← two_smul ℝ F] at k
  rw [div_eq_inv_mul, ← smul_smul, ← k, smul_smul]
  norm_num

/-- **A self-dual form that is primitive and of type `(1,1)` vanishes.** -/
theorem eq_zero_of_liftStar_eq_self {n : Space} (hn : ‖n‖ = 1) {F : LiftForm 2}
    (hF : liftStar F = F) (h : IsType11 n F) (hp : IsPrimitive n F) : F = 0 := by
  rw [eq_smul_kahlerForm_of_liftStar_eq_self hn hF h, hp]
  simp

/-! ## The orientation of the complex structure -/

/-- **The complex orientation is `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`**: `ω_J ∧ ω_J = 2 |n|² vol`, with
`vol` the volume form of the orientation `liftOrientation` (on a complex surface with its
complex orientation, `ω ∧ ω = 2 vol`; for the opposite orientation the sign would be `-`). -/
theorem kahlerForm_wedge_kahlerForm (n : Space) (v : Fin (2 + 2) → LiftSpace) :
    (ContinuousAlternatingMap.wedge (kahlerForm n) (kahlerForm n)) v =
      2 * ‖n‖ ^ 2 * liftVol v := by
  have h := wedge_liftStar_apply (kahlerForm n) (kahlerForm n) v
  rw [liftStar_kahlerForm, liftInner_kahlerForm_self] at h
  exact h

/-- The complex structure of the direction `e₂` on the standard frame: `J e₀ = e₁`,
`J e₁ = -e₀`, `J e₂ = e_τ`, `J e_τ = -e₂`. These are the complex coordinates `x₀ + i x₁` and
`x₂ + i τ` of the source. -/
theorem liftJ_coordVec_two_frame :
    liftJ (coordVec 2) (coordVec 0, 0) = (coordVec 1, 0) ∧
    liftJ (coordVec 2) (coordVec 1, 0) = (-coordVec 0, 0) ∧
    liftJ (coordVec 2) (coordVec 2, 0) = (0, 1) ∧
    liftJ (coordVec 2) (0, 1) = (-coordVec 2, 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [liftJ_apply] <;> refine Prod.ext ?_ ?_
  · ext i
    obtain ⟨c0, c1, c2⟩ := cross_components (coordVec 2) (coordVec 0)
    fin_cases i <;> simp [c0, c1, c2, coordVec]
  · simp [coordVec, inner_components]
  · ext i
    obtain ⟨c0, c1, c2⟩ := cross_components (coordVec 2) (coordVec 1)
    fin_cases i <;> simp [c0, c1, c2, coordVec]
  · simp [coordVec, inner_components]
  · ext i
    obtain ⟨c0, c1, c2⟩ := cross_components (coordVec 2) (coordVec 2)
    fin_cases i <;> simp [c0, c1, c2, coordVec]
  · simp [coordVec]
  · ext i
    obtain ⟨c0, c1, c2⟩ := cross_components (coordVec 2) 0
    fin_cases i <;> simp [c0, c1, c2, coordVec]
  · simp

/-- **The complex frame `(e₀, J e₀, e₂, J e₂)` is positively oriented** for
`dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`: it is the frame `(e₀, e₁, e₂, e_τ)` itself. -/
theorem liftVol_complexFrame :
    liftVol ![(coordVec 0, 0), liftJ (coordVec 2) (coordVec 0, 0), (coordVec 2, 0),
      liftJ (coordVec 2) (coordVec 2, 0)] = 1 := by
  obtain ⟨h0, -, h2, -⟩ := liftJ_coordVec_two_frame
  rw [h0, h2]
  exact liftVol_frame

/-! ## The lift satisfies the pointwise Hermitian–Yang–Mills conditions -/

/-- **The lift is of type `(1,1)`** for the complex structure of every unit direction `n`. -/
theorem isType11_hymLiftAt {n : Space} (hn : ‖n‖ = 1) (b : Form 2) :
    IsType11 n (hymLiftAt b) :=
  ((liftStar_eq_neg_iff_isType11_and_isPrimitive hn _).1 (liftStar_hymLiftAt b)).1

/-- **The lift is primitive**: `⟨ℱ, ω_J⟩ = 0`, for every direction `n` (unit or not). -/
theorem isPrimitive_hymLiftAt (n : Space) (b : Form 2) : IsPrimitive n (hymLiftAt b) :=
  liftInner_eq_zero_of_liftStar (liftStar_hymLiftAt b) (liftStar_kahlerForm n)

/-- **The pointwise Hermitian–Yang–Mills conditions for the lifted field**: at every point of
`ℝ³ × ℝ`, for every field of 2-forms (no field equation is used) and every unit direction `n`,
the lifted form is of type `(1,1)` and primitive. -/
theorem isType11_and_isPrimitive_hymLift {n : Space} (hn : ‖n‖ = 1) (w : Space → Form 2)
    (p : LiftSpace) : IsType11 n (hymLift w p) ∧ IsPrimitive n (hymLift w p) :=
  ⟨isType11_hymLiftAt hn _, isPrimitive_hymLiftAt n _⟩

/-- The pointwise Hermitian–Yang–Mills conditions on `ℝ³ × (ℝ/ℓℤ)`. -/
theorem isType11_and_isPrimitive_hymLiftCircle {n : Space} (hn : ‖n‖ = 1) (ℓ : ℝ)
    (w : Space → Form 2) (p : Space × AddCircle ℓ) :
    IsType11 n (hymLiftCircle ℓ w p) ∧ IsPrimitive n (hymLiftCircle ℓ w p) := by
  rw [hymLiftCircle_eq]
  exact ⟨isType11_hymLiftAt hn _, isPrimitive_hymLiftAt n _⟩

/-- **The self-dual lift is not of type `(1,1)` unless its field is along `n`**: for a unit
`n`, `π^*b + π^*(⋆b) ∧ dτ` with `b = ι_C vol` is of type `(1,1)` exactly when `C = ⟨C, n⟩ n`. -/
theorem isType11_sdLiftAt_flux_iff {n : Space} (hn : ‖n‖ = 1) (C : Space) :
    IsType11 n (sdLiftAt (flux C)) ↔ C = ⟪C, n⟫ • n := by
  have e : sdLiftAt (flux C) = ofParts (flux C) (flat C) := by rw [sdLiftAt, hodge_flux]
  have hin : liftInner (sdLiftAt (flux C)) (kahlerForm n) = 2 * ⟪C, n⟫ := by
    rw [e, kahlerForm, liftInner_ofParts_flux_flat]
    ring
  have hG (c : ℝ) (D : Space) :
      c • ofParts (flux D) (flat D) = ofParts (flux (c • D)) (flat (c • D)) := by
    rw [map_smul, map_smul, ofParts_smul]
  rw [isType11_iff hn, liftStar_sdLiftAt, hin, e, kahlerForm, ← two_smul ℝ, hG, hG]
  constructor
  · intro h
    have k := congrArg spatialPart h
    rw [spatialPart_ofParts, spatialPart_ofParts] at k
    have k' := flux.injective k
    rw [mul_smul] at k'
    exact smul_right_injective _ (two_ne_zero' ℝ) k'
  · intro h
    rw [mul_smul, ← h]

/-! ## Closedness on the circle product with no regularity hypothesis -/

/-- The exterior derivative of the lifted form on `ℝ³ × ℝ` does not depend on `τ`. -/
theorem extDeriv_hymLift_tau_indep (w : Space → Form 2) (x : Space) (τ τ' : ℝ) :
    extDeriv (hymLift w) (x, τ) = extDeriv (hymLift w) (x, τ') := by
  ext v
  have e : v = ![((v 0).1, (v 0).2), ((v 1).1, (v 1).2), ((v 2).1, (v 2).2)] := by
    funext i; fin_cases i <;> rfl
  rw [e, extDeriv_hymLift_apply, extDeriv_hymLift_apply]

/-- Where `ω` is not differentiable, the exterior derivative of the lifted form on `ℝ³ × ℝ` is
the junk value `0`. -/
theorem extDeriv_hymLift_of_not_differentiableAt {w : Space → Form 2} {x : Space}
    (h : ¬ DifferentiableAt ℝ w x) (τ : ℝ) : extDeriv (hymLift w) (x, τ) = 0 := by
  have h' : ¬ DifferentiableAt ℝ (hymLift w) (x, τ) :=
    fun hd => h ((differentiableAt_hymLift_iff w x τ).1 hd)
  ext v
  simp [extDeriv, fderiv_zero_of_not_differentiableAt h',
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]

section Manifold

variable (ℓ : ℝ) [Fact (0 < ℓ)]

/-- **The derivative of the covering map `ℝ³ × ℝ → ℝ³ × S¹` is the identity** of `ℝ³ × ℝ`. -/
theorem mfderiv_liftCover (p : LiftSpace) :
    (mfderiv 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ)) (liftCover ℓ) p :
      LiftSpace →L[ℝ] LiftSpace) = ContinuousLinearMap.id ℝ LiftSpace := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [liftCover,
    mfderiv_prodMap mdifferentiableAt_id (AddCircle.hasMFDerivAt_coe ℓ p.2).mdifferentiableAt,
    mfderiv_id, AddCircle.mfderiv_coe]
  rfl

/-- **The inverse of a chart of `ℝ³ × S¹` is the covering map** on the chart target. -/
theorem extChartAt_symm_eq_liftCover (x : Space) (θ : AddCircle ℓ) {z : LiftSpace}
    (hz : z ∈ (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).target) :
    (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).symm z = liftCover ℓ z := by
  rw [extChartAt_prod] at hz ⊢
  obtain ⟨z1, z2⟩ := z
  have h2 : z2 ∈ (extChartAt 𝓘(ℝ) θ).target := hz.2
  exact Prod.ext rfl (AddCircle.extChartAt_symm_apply θ h2)

/-- The spatial component of the chart point of `(x, θ)` is `x`. -/
theorem extChartAt_circle_fst (x : Space) (θ : AddCircle ℓ) :
    (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ) (x, θ)).1 = x := by
  rw [extChartAt_prod]
  rfl

/-- **The circle form in a chart is the lifted form.** On the target of the chart of
`ℝ³ × S¹` at `(x, θ)`, the coordinate expression of `hymLiftCircleForm ℓ ω` is `hymLift ω`:
the charts of `ℝ/ℓℤ` are local lifts to `ℝ`, with derivative `1`. No hypothesis on `ω`. -/
theorem inChartAt_hymLiftCircleForm (w : Space → Form 2) (x : Space) (θ : AddCircle ℓ)
    {z : LiftSpace} (hz : z ∈ (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).target) :
    (hymLiftCircleForm ℓ w).inChartAt (x, θ) z = hymLift w z := by
  have hev : ((extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).symm : LiftSpace → _) =ᶠ[nhds z]
      liftCover ℓ := by
    filter_upwards [(isOpen_extChartAt_target (x, θ)).mem_nhds hz] with u hu
    exact extChartAt_symm_eq_liftCover ℓ x θ hu
  have hD : (mfderivWithin 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ))
      (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).symm
      (Set.range (𝓘(ℝ, Space).prod 𝓘(ℝ))) z : LiftSpace →L[ℝ] LiftSpace) =
      ContinuousLinearMap.id ℝ LiftSpace := by
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ, hev.mfderiv_eq, mfderiv_liftCover]
    rfl
  ext v
  rw [RoughForm.inChartAt_apply]
  change hymLiftCircle ℓ w ((extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).symm z)
    (fun i => (mfderivWithin 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ))
      (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, θ)).symm
      (Set.range (𝓘(ℝ, Space).prod 𝓘(ℝ))) z : LiftSpace →L[ℝ] LiftSpace) (v i)) = _
  rw [hD, hymLiftCircle_eq, extChartAt_symm_eq_liftCover ℓ x θ hz]
  rfl

/-- **The exterior derivative of the circle form in the chart, with no hypothesis on `ω`**:
TauCeti's `mextDeriv` is the flat exterior derivative of the coordinate expression of the form
in the chart at the point, and that coordinate expression is `hymLift ω` near the chart
point. -/
theorem mextDeriv_hymLiftCircleForm_eq_chart (w : Space → Form 2) (p : Space × AddCircle ℓ) :
    mextDeriv (hymLiftCircleForm ℓ w) p =
      extDeriv (hymLift w) (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p p) := by
  have h : (hymLiftCircleForm ℓ w).inChartAt p =ᶠ[nhds
      (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p p)] hymLift w := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, Space).prod 𝓘(ℝ)) p] with z hz
    exact inChartAt_hymLiftCircleForm ℓ w p.1 p.2 hz
  rw [mextDeriv_def, h.extDerivWithin_eq_nhds, ModelWithCorners.range_eq_univ,
    extDerivWithin_univ]

/-- **The exterior derivative of the circle form, with no hypothesis on `ω`**: at `(x, [τ])`
it is the exterior derivative of the lifted form at `(x, τ)`. This is
`mextDeriv_hymLiftCircleForm_coe` of `FormHYMCircle` without its `C¹` hypothesis. -/
theorem mextDeriv_hymLiftCircleForm_coe' (w : Space → Form 2) (x : Space) (τ : ℝ) :
    mextDeriv (hymLiftCircleForm ℓ w) (x, (τ : AddCircle ℓ)) = extDeriv (hymLift w) (x, τ) := by
  have e : extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, (τ : AddCircle ℓ)) (x, (τ : AddCircle ℓ)) =
      (x, (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) (x, (τ : AddCircle ℓ))
        (x, (τ : AddCircle ℓ))).2) :=
    Prod.ext (extChartAt_circle_fst ℓ x _) rfl
  rw [mextDeriv_hymLiftCircleForm_eq_chart, e]
  exact extDeriv_hymLift_tau_indep w x _ τ

/-- **Where `ω` is not differentiable, the exterior derivative of the circle form is the junk
value `0`**: the coordinate expression of the form is not differentiable at the chart point,
and TauCeti's `mextDeriv` is then `0`, as Mathlib's `extDeriv` is. -/
theorem mextDeriv_hymLiftCircleForm_of_not_differentiableAt {w : Space → Form 2} {x : Space}
    (h : ¬ DifferentiableAt ℝ w x) (θ : AddCircle ℓ) :
    mextDeriv (hymLiftCircleForm ℓ w) (x, θ) = 0 := by
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [mextDeriv_hymLiftCircleForm_coe' ℓ w x τ, extDeriv_hymLift_of_not_differentiableAt h]
  rfl

/-- **Closedness at a point of `ℝ³ × S¹`, with no hypothesis on `ω`**: the circle form is
closed at `(x, θ)` exactly when `dω = 0` and `d(⋆ω) = 0` at `x`. As for
`extDeriv_hymLift_eq_zero_iff`, at a point where `ω` is not differentiable all three exterior
derivatives are the junk value `0` and the statement is `True ↔ True`. -/
theorem mextDeriv_hymLiftCircleForm_eq_zero_iff' (w : Space → Form 2) (x : Space)
    (θ : AddCircle ℓ) :
    mextDeriv (hymLiftCircleForm ℓ w) (x, θ) = 0 ↔
      extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← extDeriv_hymLift_eq_zero_iff w x τ, ← mextDeriv_hymLiftCircleForm_coe' ℓ w x τ]
  rfl

/-- **Closedness on `ℝ³ × S¹`, with no hypothesis on `ω`**: the circle form is closed exactly
when `dω = 0` and `d(⋆ω) = 0` everywhere. -/
theorem mextDeriv_hymLiftCircleForm_eq_zero_iff_forall' (w : Space → Form 2) :
    mextDeriv (hymLiftCircleForm ℓ w) = 0 ↔
      ∀ x, extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  constructor
  · intro h x
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff' ℓ w x 0).1 (congrFun h (x, 0))
  · intro h
    funext p
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff' ℓ w p.1 p.2).2 (h p.1)

/-- **Closedness at the points of `Ω × S¹`, with no hypothesis on `ω` or on `Ω`.** -/
theorem hymLiftCircleForm_closedOn_iff (Ω : Set Space) (w : Space → Form 2) :
    (∀ p ∈ Ω ×ˢ (Set.univ : Set (AddCircle ℓ)), mextDeriv (hymLiftCircleForm ℓ w) p = 0) ↔
      ∀ x ∈ Ω, extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  constructor
  · intro h x hx
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff' ℓ w x 0).1 (h (x, 0) ⟨hx, Set.mem_univ _⟩)
  · rintro h ⟨x, θ⟩ ⟨hx, -⟩
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff' ℓ w x θ).2 (h x hx)

/-- **The form on the open submanifold `Ω × S¹` in a chart is the lifted form**, near the chart
point. No hypothesis on `ω`. -/
theorem inChartAt_hymLiftRegionForm_eventuallyEq (U : TopologicalSpace.Opens Space)
    (w : Space → Form 2) (p : circleRegion ℓ U) :
    (hymLiftRegionForm ℓ U w).inChartAt p =ᶠ[nhds
      (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p p)] hymLift w := by
  have hc : extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p p =
      extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p.1 p.1 := rfl
  have hs : ((extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p.1).symm : LiftSpace → _) =ᶠ[nhds
      (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p p)]
      Subtype.val ∘ (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p).symm := by
    have h0 := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
      (H := ModelProd Space ℝ) (circleRegion ℓ U) (x := p)
    exact h0
  have ht := extChartAt_target_mem_nhds (I := 𝓘(ℝ, Space).prod 𝓘(ℝ)) p
  have ht' := extChartAt_target_mem_nhds (I := 𝓘(ℝ, Space).prod 𝓘(ℝ)) p.1
  rw [← hc] at ht'
  have hall := ((hs.and ht).and ht').eventually_nhds
  filter_upwards [hall] with z hz
  have hz0 := hz.self_of_nhds
  have hev : (Subtype.val ∘ (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p).symm : LiftSpace → _)
      =ᶠ[nhds z] liftCover ℓ := by
    filter_upwards [hz] with u hu
    rw [← hu.1.1]
    exact extChartAt_symm_eq_liftCover ℓ p.1.1 p.1.2 hu.2
  have hD : (mfderivWithin 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ))
      (Subtype.val ∘ (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p).symm)
      (Set.range (𝓘(ℝ, Space).prod 𝓘(ℝ))) z : LiftSpace →L[ℝ] LiftSpace) =
      ContinuousLinearMap.id ℝ LiftSpace := by
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ, hev.mfderiv_eq, mfderiv_liftCover]
    rfl
  have hval : (Subtype.val ((extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p).symm z) :
      Space × AddCircle ℓ) = liftCover ℓ z := hev.self_of_nhds
  rw [hymLiftRegionForm, RoughForm.inChartAt_mpullback _ _ p hz0.1.2
    (contMDiff_subtype_val.contMDiffAt.mdifferentiableAt one_ne_zero)]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change hymLiftCircle ℓ w (Subtype.val ((extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p).symm z))
    ((mfderivWithin 𝓘(ℝ, LiftSpace) (𝓘(ℝ, Space).prod 𝓘(ℝ))
      (Subtype.val ∘ (extChartAt (𝓘(ℝ, Space).prod 𝓘(ℝ)) p).symm)
      (Set.range (𝓘(ℝ, Space).prod 𝓘(ℝ))) z : LiftSpace →L[ℝ] LiftSpace) ∘ v) = _
  rw [hD, hymLiftCircle_eq, hval]
  rfl

/-- **The exterior derivative on `Ω × S¹` is the restriction of the exterior derivative on
`ℝ³ × S¹`, with no hypothesis on `ω`.** This is `mextDeriv_hymLiftRegionForm` of
`FormHYMCircle` without its `C¹` hypothesis. -/
theorem mextDeriv_hymLiftRegionForm' (U : TopologicalSpace.Opens Space) (w : Space → Form 2)
    (p : circleRegion ℓ U) :
    mextDeriv (hymLiftRegionForm ℓ U w) p = mextDeriv (hymLiftCircleForm ℓ w) p := by
  rw [mextDeriv_hymLiftCircleForm_eq_chart, mextDeriv_def,
    (inChartAt_hymLiftRegionForm_eventuallyEq ℓ U w p).extDerivWithin_eq_nhds,
    ModelWithCorners.range_eq_univ, extDerivWithin_univ]
  rfl

/-- **Closedness on the manifold `Ω × S¹`, with no hypothesis on `ω`**: the lifted form on
the open submanifold is closed exactly when `dω = 0` and `d(⋆ω) = 0` at every point of `Ω`. -/
theorem mextDeriv_hymLiftRegionForm_eq_zero_iff (U : TopologicalSpace.Opens Space)
    (w : Space → Form 2) :
    mextDeriv (hymLiftRegionForm ℓ U w) = 0 ↔
      ∀ x ∈ U, extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0 := by
  constructor
  · intro h x hx
    have hp : (x, (0 : AddCircle ℓ)) ∈ circleRegion ℓ U := (mem_circleRegion ℓ).2 hx
    have k := mextDeriv_hymLiftRegionForm' ℓ U w ⟨(x, 0), hp⟩
    rw [h] at k
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff' ℓ w x 0).1 k.symm
  · intro h
    funext p
    rw [mextDeriv_hymLiftRegionForm' ℓ U w p]
    exact (mextDeriv_hymLiftCircleForm_eq_zero_iff' ℓ w p.1.1 p.1.2).2
      (h p.1.1 ((mem_circleRegion ℓ).1 p.2))

/-- **A vacuum form has a closed lift on the manifold `Ω × S¹`**; the converse needs only the
regularity that is part of the definition of a vacuum form:
for `ω` of class `C²` on the open set `Ω` see `hymLiftRegionForm_closed_iff_vacuumForm`. -/
theorem VacuumForm.hymLiftRegionForm_closed {U : TopologicalSpace.Opens Space}
    {w : Space → Form 2} (h : VacuumForm U w) : mextDeriv (hymLiftRegionForm ℓ U w) = 0 :=
  (mextDeriv_hymLiftRegionForm_eq_zero_iff ℓ U w).2 fun x hx => ⟨h.closed x hx, h.coclosed x hx⟩

end Manifold

end PlasmaLean.Forms
