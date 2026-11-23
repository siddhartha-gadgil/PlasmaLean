/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormContactOpens
public import PlasmaLean.Sanity.FormContactManifold

/-!
# Sanity checks for `Theory/Fields/FormContactOpens`

The region is the open half-space `rightHalf = {x | 0 < x 0}`.

* Accepted, a field that needs the region: `cutHelical` is the helical field on `rightHalf` and
  zero elsewhere. It is not continuous on `ℝ³` (`cutHelical_not_continuous`), but it is smooth
  and Beltrami on `rightHalf`, so its 1-form is a TauCeti contact form on the manifold
  `rightHalf` (`cutHelical_isContactForm`) with Reeb vector field the helical field
  (`cutHelical_reebVectorField`). It is not contact at the origin (`cutHelical_not_contact`).
* Accepted, a smooth field that is contact only on the region: `shearField = (0, x² / 2, 1)`
  has `⟪B, ∇ × B⟫ = x` (`shearField_inner_curl`). Its 1-form is a TauCeti contact form on
  `rightHalf` (`shear_isContactForm`); the contact condition fails exactly on the plane `x = 0`
  (`shear_isContactAt_iff`), so it is not a contact form on `ℝ³`
  (`shear_not_isContactForm_space`) and TauCeti's pointwise condition fails at the origin of
  the manifold `⊤` (`shear_not_isContactFormAt_top`).
* Accepted: the helical field restricted to `rightHalf` (`helical_isContactForm_rightHalf`,
  `helical_reebVectorField_rightHalf`).
* Rejected: the 1-form of a constant field is not a TauCeti contact form on `rightHalf`
  (`const_not_isContactForm`), nor on any nonempty open set
  (`const_not_isContactForm_of_nonempty`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormContactOpens

open PlasmaLean PlasmaLean.Forms PlasmaLean.Vacuum PlasmaLean.Fields
open PlasmaLean.Sanity.FormContactManifold
open TauCeti TopologicalSpace
open scoped Manifold ContDiff RealInnerProductSpace

/-- The open half-space `{x | 0 < x 0}`. -/
def rightHalf : Opens Space :=
  ⟨{x | 0 < x 0}, isOpen_lt continuous_const (continuous_apply 0 |>.comp
    (PiLp.continuous_ofLp 2 _))⟩

/-- Membership in the half-space. -/
theorem mem_rightHalf {x : Space} : x ∈ rightHalf ↔ 0 < x 0 := Iff.rfl

/-- The point `(1, 0, 0)` of the half-space. -/
def pt : Space := WithLp.toLp 2 ![1, 0, 0]

/-- `(1, 0, 0)` lies in the half-space. -/
theorem pt_mem : pt ∈ rightHalf := by
  rw [mem_rightHalf]
  simp [pt]

/-- The origin does not lie in the half-space. -/
theorem zero_notMem : (0 : Space) ∉ rightHalf := by
  rw [mem_rightHalf]
  simp

/-! ## The helical field on the half-space -/

/-- The helical field is Beltrami with `λ = -1` on the half-space. -/
theorem helical_beltrami_rightHalf : IsBeltramiOn helicalField (fun _ => -1) rightHalf :=
  fun x _ => helicalField_beltrami x (Set.mem_univ x)

/-- Accepted: the helical 1-form is a TauCeti contact form on the half-space. -/
theorem helical_isContactForm_rightHalf :
    (flatSmoothFormOn rightHalf helicalField helicalField_contDiff.contDiffOn).IsContactForm :=
  helical_beltrami_rightHalf.isContactForm_flatSmoothFormOn _
    (fun _ _ => by norm_num) fun x _ => helicalField_ne_zero x

/-- Accepted: its Reeb vector field on the half-space is the helical field. -/
theorem helical_reebVectorField_rightHalf (x : rightHalf) :
    (flatSmoothFormOn rightHalf helicalField helicalField_contDiff.contDiffOn).reebVectorField x
      = helicalField x := by
  rw [helical_beltrami_rightHalf.reebVectorField_flatSmoothFormOn _
    (fun _ _ => by norm_num) fun x _ => helicalField_ne_zero x, norm_helicalField]
  exact (by simp : ((1 : ℝ) ^ 2)⁻¹ • helicalField x = helicalField x)

/-! ## A field that is only defined well on the half-space -/

open Classical in
/-- The helical field on the half-space, and zero elsewhere. -/
noncomputable def cutHelical (y : Space) : Space := if 0 < y 0 then helicalField y else 0

/-- On the half-space the cut field is the helical field. -/
theorem cutHelical_of_mem {y : Space} (hy : y ∈ rightHalf) : cutHelical y = helicalField y :=
  by simp [cutHelical, mem_rightHalf.1 hy]

/-- At the origin the cut field vanishes. -/
theorem cutHelical_zero : cutHelical 0 = 0 := by simp [cutHelical]

/-- Near a point of the half-space the cut field is the helical field. -/
theorem cutHelical_eventuallyEq {x : Space} (hx : x ∈ rightHalf) :
    cutHelical =ᶠ[nhds x] helicalField :=
  Filter.eventuallyEq_of_mem (rightHalf.2.mem_nhds hx) fun _ hy => cutHelical_of_mem hy

/-- The cut field is smooth on the half-space. -/
theorem cutHelical_contDiffOn : ContDiffOn ℝ ∞ cutHelical rightHalf :=
  helicalField_contDiff.contDiffOn.congr fun _ hy => cutHelical_of_mem hy

/-- The cut field is Beltrami with `λ = -1` on the half-space. -/
theorem cutHelical_beltrami : IsBeltramiOn cutHelical (fun _ => -1) rightHalf := by
  intro x hx
  have he := cutHelical_eventuallyEq hx
  refine ⟨(helicalField_differentiableAt x).congr_of_eventuallyEq he, ?_⟩
  rw [fieldCurl, he.fderiv_eq, cutHelical_of_mem hx]
  exact helicalField_curl x

/-- The cut field is not continuous on `ℝ³`, so the statements on all of `ℝ³` do not apply to
it. -/
theorem cutHelical_not_continuous : ¬ Continuous cutHelical := by
  intro hc
  have hcl : IsClosed {y : Space | cutHelical y = helicalField y} :=
    isClosed_eq hc helicalField_contDiff.continuous
  have h0 : (0 : Space) ∈ closure (rightHalf : Set Space) := by
    refine mem_closure_iff_seq_limit.2 ⟨fun n => (1 / ((n : ℝ) + 1)) • pt, fun n => ?_, ?_⟩
    · change 0 < ((1 / ((n : ℝ) + 1)) • pt) 0
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa [pt] using this
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const pt
      simpa using h
  have := hcl.closure_subset_iff.2 (fun y hy => cutHelical_of_mem hy) h0
  exact helicalField_ne_zero 0 (this.symm.trans cutHelical_zero)

/-- Accepted: the 1-form of the cut field is a TauCeti contact form on the half-space. -/
theorem cutHelical_isContactForm :
    (flatSmoothFormOn rightHalf cutHelical cutHelical_contDiffOn).IsContactForm :=
  cutHelical_beltrami.isContactForm_flatSmoothFormOn _ (fun _ _ => by norm_num) fun x hx => by
    rw [cutHelical_of_mem hx]
    exact helicalField_ne_zero x

/-- Accepted: the Reeb vector field of the cut field on the half-space is the helical field. -/
theorem cutHelical_reebVectorField (x : rightHalf) :
    (flatSmoothFormOn rightHalf cutHelical cutHelical_contDiffOn).reebVectorField x =
      helicalField x := by
  rw [cutHelical_beltrami.reebVectorField_flatSmoothFormOn _ (fun _ _ => by norm_num)
    fun x hx => by
      rw [cutHelical_of_mem hx]
      exact helicalField_ne_zero x, cutHelical_of_mem x.2, norm_helicalField]
  exact (by simp : ((1 : ℝ) ^ 2)⁻¹ • helicalField x = helicalField x)

/-- Outside the half-space nothing is claimed, and nothing holds: the cut field is not contact
at the origin. -/
theorem cutHelical_not_contact : ¬ IsContactAt (fun y => flat (cutHelical y)) 0 := by
  rw [isContactAt_flat_iff, cutHelical_zero]
  simp

/-! ## A smooth field that is contact only on the half-space -/

/-- The shear field `(0, x² / 2, 1)`. -/
noncomputable def shearField (y : Space) : Space := WithLp.toLp 2 ![0, y 0 ^ 2 / 2, 1]

/-- The Fréchet derivative of the shear field. -/
theorem shearField_hasFDerivAt (x : Space) :
    HasFDerivAt shearField
      ((x 0 • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)).smulRight (basis 1)) x := by
  have hp : HasFDerivAt (fun y : Space => y 0)
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have h1 := (((hp.pow 2).mul_const (1 / 2)).smul_const (basis 1 : Space)).add_const (basis 2)
  have h2 : HasFDerivAt shearField _ x :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
      refine space_ext ?_ ?_ ?_
      · simp [shearField, basis]
      · simp [shearField, basis]
        ring
      · simp [shearField, basis])
  convert h2 using 1
  ext v i
  fin_cases i
  · simp [basis]
  · simp [basis]
    ring
  · simp [basis]

/-- The shear field is smooth. -/
theorem shearField_contDiff : ContDiff ℝ ∞ shearField := by
  have hx : ContDiff ℝ ∞ fun y : Space => y 0 := contDiff_euclidean.1 contDiff_id 0
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · exact contDiff_const
  · exact (hx.pow 2).div_const 2
  · exact contDiff_const

/-- `∇ × B = (0, 0, x)` for the shear field. -/
theorem shearField_curl (x : Space) :
    fieldCurl shearField x = WithLp.toLp 2 ![0, 0, x 0] := by
  apply space_ext <;>
    simp [fieldCurl, curlOp, (shearField_hasFDerivAt x).fderiv, coordVec, basis]

/-- `⟪B, ∇ × B⟫ = x` for the shear field: it changes sign across the plane `x = 0`. -/
theorem shearField_inner_curl (x : Space) : ⟪shearField x, fieldCurl shearField x⟫ = x 0 := by
  rw [shearField_curl, inner_coords3]
  simp [shearField]

/-- The shear 1-form is contact at `x` exactly when `x` is off the plane `x = 0`. -/
theorem shear_isContactAt_iff (x : Space) :
    IsContactAt (fun y => flat (shearField y)) x ↔ x 0 ≠ 0 := by
  rw [isContactAt_flat_iff, shearField_inner_curl]

/-- Accepted: the shear 1-form is a TauCeti contact form on the half-space. -/
theorem shear_isContactForm :
    (flatSmoothFormOn rightHalf shearField shearField_contDiff.contDiffOn).IsContactForm :=
  (isContactForm_flatSmoothFormOn_iff _ _ _).2 fun x hx =>
    (shear_isContactAt_iff x).2 (mem_rightHalf.1 hx).ne'

/-- Rejected: the shear 1-form is not a TauCeti contact form on all of `ℝ³`. -/
theorem shear_not_isContactForm_space :
    ¬ (flatSmoothForm shearField shearField_contDiff).IsContactForm := fun h =>
  (shear_isContactAt_iff 0).1 ((isContactForm_flatSmoothForm_iff _ _).1 h 0) (by simp)

/-- Rejected: nor on the manifold `(⊤ : Opens Space)`. -/
theorem shear_not_isContactForm_top :
    ¬ (flatSmoothFormOn ⊤ shearField shearField_contDiff.contDiffOn).IsContactForm := fun h =>
  shear_not_isContactForm_space ((isContactForm_flatSmoothFormOn_top_iff _ _).1 h)

/-- Rejected: TauCeti's pointwise condition fails at the origin of the manifold `⊤`. -/
theorem shear_not_isContactFormAt_top :
    ¬ IsContactFormAt (onOpens (⊤ : Opens Space) fun y => flat (shearField y))
      (⟨0, trivial⟩ : (⊤ : Opens Space)) := fun h =>
  (shear_isContactAt_iff 0).1
    ((isContactFormAt_onOpens_flat_iff (⊤ : Opens Space) shearField ⟨0, trivial⟩).1 h) (by simp)

/-! ## Rejected: constant fields -/

/-- Rejected: the 1-form of a constant field is not a TauCeti contact form on a nonempty open
set. -/
theorem const_not_isContactForm_of_nonempty (U : Opens Space) {x : Space} (hx : x ∈ U)
    (B₀ : Space) :
    ¬ (flatSmoothFormOn U (fun _ => B₀) contDiffOn_const).IsContactForm := fun h =>
  const_not_contact B₀ x ((isContactForm_flatSmoothFormOn_iff U _ contDiffOn_const).1 h x hx)

/-- Rejected: the 1-form of a constant field is not a TauCeti contact form on the half-space. -/
theorem const_not_isContactForm (B₀ : Space) :
    ¬ (flatSmoothFormOn rightHalf (fun _ => B₀) contDiffOn_const).IsContactForm :=
  const_not_isContactForm_of_nonempty rightHalf pt_mem B₀

end PlasmaLean.Sanity.FormContactOpens
