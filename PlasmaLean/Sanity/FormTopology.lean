/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormTopology
public import PlasmaLean.Sanity.CurvatureObstruction
public import PlasmaLean.Sanity.Forms

/-!
# Sanity checks for the bridge to manifold forms (`Theory/Fields/FormTopology`)

* Rejected fixture for potentials: the field of a straight wire, `B = e_z × x / (x² + y²)`, is a
  vacuum field on the complement of the axis (`wireField_vacuum`) and is **not** a gradient
  there (`wireField_no_potential`): a potential would increase strictly around the unit circle,
  which is a closed field line.
* Topological consequence through the bridge: the complement of a line in `ℝ³` is not simply
  connected (`wireRegion_not_simplyConnected`).
* Accepted fixture: the region below the sheet `z = x²` is simply connected
  (homeomorphic to a half-space) and not star-convex about any point
  (`bentSet_not_starConvex`); the hyperbolic vacuum field has a potential on it by the simply
  connected theorem (`hyperbolic_scalarPotential_bent`).
* Bridge checks: the bridge preserves closedness for the wire form (`wire_closed_onOpens`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormTopology

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-- The complement of the wire axis, as an open subset of `ℝ³`. -/
def wireOpens : Opens Space := ⟨wireRegion, isOpen_wireRegion⟩

/-- The unit circle lies in the wire region. -/
theorem unitCircle_mem (s : ℝ) : unitCircle s ∈ wireRegion := by
  change 0 < wireR2 (unitCircle s)
  rw [wireR2_unitCircle]
  exact one_pos

/-- The unit circle closes up. -/
theorem unitCircle_two_pi : unitCircle (2 * Real.pi) = unitCircle 0 := by
  simp [unitCircle]

/-- **The wire field has no potential on the complement of its axis.** -/
theorem wireField_no_potential :
    ¬ ∃ φ : Space → ℝ, DifferentiableOn ℝ φ wireRegion ∧
      ∀ x ∈ wireRegion, wireField x = gradient φ x := by
  rintro ⟨φ, hφ, hgrad⟩
  have hd (s : ℝ) : HasDerivAt (fun t => φ (unitCircle t))
      (⟪wireField (unitCircle s), wireField (unitCircle s)⟫) s := by
    have hφs : DifferentiableAt ℝ φ (unitCircle s) :=
      (hφ _ (unitCircle_mem s)).differentiableAt (isOpen_wireRegion.mem_nhds (unitCircle_mem s))
    have h := hφs.hasFDerivAt.comp_hasDerivAt s (unitCircle_fieldLine s)
    have e : fderiv ℝ φ (unitCircle s) (wireField (unitCircle s)) =
        ⟪wireField (unitCircle s), wireField (unitCircle s)⟫ := by
      rw [hgrad _ (unitCircle_mem s), inner_gradient_left]
    rw [← e]
    exact h
  have hmono : StrictMono (fun t => φ (unitCircle t)) :=
    strictMono_of_hasDerivAt_pos hd fun s =>
      real_inner_self_pos.2 (wireField_unitCircle_ne_zero s)
  have hlt := hmono (show (0 : ℝ) < 2 * Real.pi by positivity)
  simp only [unitCircle_two_pi] at hlt
  exact lt_irrefl _ hlt

/-- **The complement of a line in `ℝ³` is not simply connected**, proved from a magnetic field:
the wire field is a vacuum field there with no potential. -/
theorem wireRegion_not_simplyConnected : ¬ SimplyConnectedSpace wireOpens :=
  not_simplyConnected_of_no_potential (U := wireOpens) wireField_vacuum wireField_no_potential

/-- Bridge check: the 1-form `B♭` of the wire field is closed as a form on the manifold
`wireOpens`. -/
theorem wire_closed_onOpens :
    mextDeriv (onOpens wireOpens fun y => flat (wireField y)) = 0 := by
  rw [mextDeriv_onOpens_eq_zero_iff]
  intro x hx
  rw [extDeriv_flat, wireField_vacuum.curl_eq_zero x hx, map_zero]

/-- Bridge check: the same form is `C²` on the manifold. -/
theorem wire_isSmoothForm_onOpens :
    IsSmoothForm 𝓘(ℝ, Space) 2 (onOpens wireOpens fun y => flat (wireField y)) := by
  rw [isSmoothForm_onOpens_iff]
  exact flat.toContinuousLinearEquiv.contDiff.comp_contDiffOn wireField_vacuum.contDiffOn

/-! ## A simply connected region that is not star-convex -/

/-- The shear `(x, y, z) ↦ (x, y, z + x²)` of `ℝ³`. -/
noncomputable def shear : Space ≃ₜ Space where
  toFun x := x + (x 0 ^ 2) • coordVec 2
  invFun x := x - (x 0 ^ 2) • coordVec 2
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The lower half-space `z < 0`. -/
def lowerHalf : Set Space := {x | x 2 < 0}

/-- The region below the parabolic sheet `z = x²`. -/
def bentSet : Set Space := {x | x 2 < x 0 ^ 2}

/-- The bent region is open. -/
theorem isOpen_bentSet : IsOpen bentSet :=
  isOpen_lt (by fun_prop) (by fun_prop)

/-- The bent region as an open subset of `ℝ³`. -/
def bentOpens : Opens Space := ⟨bentSet, isOpen_bentSet⟩

/-- The bent region is the image of the lower half-space under the shear. -/
theorem shear_image_lowerHalf : shear '' lowerHalf = bentSet := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : y 2 < 0 := hy
    change (y + (y 0 ^ 2) • coordVec 2) 2 < (y + (y 0 ^ 2) • coordVec 2) 0 ^ 2
    simp
    linarith
  · intro hx
    have h : x 2 < x 0 ^ 2 := hx
    refine ⟨shear.symm x, ?_, shear.apply_symm_apply x⟩
    change (x - (x 0 ^ 2) • coordVec 2) 2 < 0
    simp
    linarith

/-- The bent region is simply connected: it is homeomorphic to a half-space. -/
instance : SimplyConnectedSpace bentOpens := by
  have hc : ContractibleSpace lowerHalf := by
    refine Convex.contractibleSpace ?_ ⟨-coordVec 2, by simp [lowerHalf]⟩
    exact (convex_halfSpace_lt (f := fun x : Space => x 2)
      ⟨fun x y => by simp, fun c x => by simp⟩ 0)
  have e : bentOpens ≃ₜ lowerHalf :=
    ((shear.image lowerHalf).trans (Homeomorph.setCongr shear_image_lowerHalf)).symm
  have : ContractibleSpace bentOpens := e.contractibleSpace
  infer_instance

/-- **The bent region is not star-convex about any point**, so the Poincaré-lemma theorem of
`Theory/Fields/FormCalculus` does not apply to it. -/
theorem bentSet_not_starConvex (c : Space) : ¬ StarConvex ℝ c bentSet := by
  intro h
  set t : ℝ := c 0 ^ 2 - c 2 + 2 with ht
  let p : Space := WithLp.toLp 2 ![c 0 + t, c 1, (c 0 + t) ^ 2 - 1]
  have hp : p ∈ bentSet := by
    change p 2 < p 0 ^ 2
    simp [p]
  have hc : c ∈ bentSet := by
    have := h hp (a := 1) (b := 0) zero_le_one le_rfl (by norm_num)
    simpa using this
  have hc' : c 2 < c 0 ^ 2 := hc
  have hm := h hp (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hm' : ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • p) 2 < ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • p) 0 ^ 2 :=
    hm
  simp [p] at hm'
  nlinarith [sq_nonneg (t - 1), sq_nonneg t]

/-- **Accepted fixture for the simply connected theorem**: on the bent region, which is simply
connected but not star-convex, the hyperbolic vacuum field has a potential. -/
theorem hyperbolic_scalarPotential_bent :
    ∃ φ : Space → ℝ, ContDiffOn ℝ 2 φ bentSet ∧
      ∀ x ∈ bentSet, hyperbolicField x = gradient φ x := by
  have hV : VacuumField (bentOpens : Set Space) (fun y => hyperbolicField y) :=
    ⟨isOpen_bentSet, hyperbolic_gradient_vacuum.contDiffOn.mono (Set.subset_univ _),
      fun x _ => hyperbolic_gradient_vacuum.div_eq_zero x (Set.mem_univ x),
      fun x _ => hyperbolic_gradient_vacuum.curl_eq_zero x (Set.mem_univ x)⟩
  exact hV.exists_scalarPotential_of_simplyConnected

end PlasmaLean.Sanity.FormTopology
