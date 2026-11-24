/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorTwoBackwardSlabs
public import PlasmaLean.Design.DommaschkMirrorTwoSlabs

/-! # A single physical field line on four adjoining integral slabs

The two signed outward solutions start at the same transferred state of one
Q-16 birth. Reversing the backward clock joins their derivatives at the section
and retains the enclosure on each side.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKamC KamNewton Set
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2
open DommaschkJacobian (euclideanFlow velocityJacobian)

/-- Reversing the outward clock restores the increasing geometric-angle field. -/
private theorem reverse_clock (phase t : ℝ) (v : Plane) :
    -euclideanFlow phase (-1) (-t) v = euclideanFlow phase 1 t v := by
  ext i
  fin_cases i <;> simp [euclideanFlow,physicalFlow]

/-- Oppositely directed physical branches with a common start give one differentiable
field line in signed geometric angle, including the common section. -/
theorem join_physical_clocks {f b : ℝ → Plane} {T phase : ℝ} (hT : 0 ≤ T) (same : b 0 = f 0)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (euclideanFlow phase 1 t (f t)) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, HasDerivWithinAt b (euclideanFlow phase (-1) t (b t)) (Icc 0 T) t) :
    ∃ y : ℝ → Plane, EqOn y (fun t => b (-t)) (Icc (-T) 0) ∧ EqOn y f (Icc 0 T) ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-T) T) t := by
  let y := fun t : ℝ => if t ≤ 0 then b (-t) else f t
  have left : EqOn y (fun t => b (-t)) (Icc (-T) 0) := fun t ht => ite_eq_left ht.2
  have right : EqOn y f (Icc 0 T) := by
    intro t ht
    rcases ht.1.eq_or_lt with eq | pos
    · rw [← eq]
      simpa [y] using same
    · exact ite_eq_right pos.not_ge
  have hmap : MapsTo Neg.neg (Icc (-T) 0) (Icc 0 T) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨y,left,right,fun t _ => ?_⟩
  have l : HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-T) 0) t := by
    by_cases ht : t ∈ Icc (-T) 0
    · rw [left ht]
      apply HasDerivWithinAt.congr_of_mem _ (fun u hu => left hu) ht
      have d := (hb (-t) (hmap ht)).scomp t (hasDerivWithinAt_neg t (Icc (-T) 0)) hmap
      simpa only [Function.comp_def,neg_one_smul,reverse_clock] using d
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
  have r : HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc 0 T) t := by
    by_cases ht : t ∈ Icc 0 T
    · rw [right ht]
      exact (hf t ht).congr_of_mem (fun u hu => right hu) ht
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
  rw [← Icc_union_Icc_eq_Icc (neg_nonpos.mpr hT) hT]
  exact l.union r

private theorem forward_chain :
    Chain pilotLimits (MirrorEndpoint.start .q0r470) [twoRows] 2 twoExit := by
  apply Chain.cons (m := twoExit) (n := 0)
  · change run pilotLimits DommaschkPhysicalFirstStep.seed
      [DommaschkPhysicalFirstStep.row,DommaschkPhysicalSecondStep.row] = _
    simp only [run, DommaschkPhysicalFirstStep.checked, DommaschkPhysicalSecondStep.checked,
      Bool.and_true]
  · exact .nil _

private theorem forward_bounds :
    FieldBoundsOn (euclideanFlow 0 1) (velocityJacobian 0 1) (MirrorEndpoint.start .q0r470)
      0 twoRows ballDomain := by
  refine ⟨DommaschkPhysicalFirstStep.ball_field_bounds,?_,trivial⟩
  simpa only [zero_add] using DommaschkPhysicalSecondStep.field_bounds

/-- Archived piecewise reference on the common signed interval. -/
def twoSidedReference (t : ℝ) :=
  if t ≤ 0 then twoBackwardReference (-t) else twoReference t

/-- Physical trajectory from a single incoming state, with both ends and the uniform
position error certified through all three joins. -/
theorem four_slabs_from_state {x : Plane} (hx : x ∈ stateSet (MirrorEndpoint.start .q0r470)) :
    ∃ y : ℝ → Plane, y 0 = x ∧ y (-(1/32)) ∈ stateSet twoBackwardExit ∧
      y (1/32) ∈ stateSet twoExit ∧ ∀ t ∈ Icc (-(1/32)) (1/32 : ℝ),
        HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-(1/32)) (1/32)) t ∧
        dist (y t) (twoSidedReference t) ≤ 1232 / 10^9 := by
  obtain ⟨f,fs,fe,fd,ft⟩ := forward_chain.trajectory forward_bounds hx
  obtain ⟨b,bs,be,bd,bt⟩ := two_backward_checked.trajectory two_backward_bounds hx
  norm_num at fe fd be bd
  obtain ⟨y,left,right,ode⟩ := join_physical_clocks (by norm_num : (0:ℝ) ≤ 1/32)
    (bs.trans fs.symm) (fun t ht => fd t ht.1 ht.2) (fun t ht => bd t ht.1 ht.2)
  refine ⟨y,(right (by norm_num : (0:ℝ) ∈ Icc 0 (1/32))).trans fs,?_,?_,fun t ht => ⟨ode t ht,?_⟩⟩
  · rw [left (by norm_num : -(1/32:ℝ) ∈ Icc (-(1/32)) 0)]
    simpa using be
  · rw [right (by norm_num : (1/32:ℝ) ∈ Icc 0 (1/32))]
    exact fe
  · by_cases h : t ≤ 0
    · rw [twoSidedReference,ite_eq_left h,left ⟨ht.1,h⟩]
      exact two_backward_tube_error bt ⟨by linarith,by linarith [ht.1]⟩
    · have pos : t ∈ Icc 0 (1/32:ℝ) := ⟨(lt_of_not_ge h).le,ht.2⟩
      rw [twoSidedReference,ite_eq_right h,right pos]
      exact two_tube_error ft pos

/-- A single physical approach followed by the common signed-angle line. -/
def FourSlabPassage (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ (direction : ℝ) (approach : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |direction| = 1 ∧ φ + direction*|φ| = 0 ∧ approach 0 = birth uC zC uA zA (47/100) φ ∧
    (∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach (physicalFlow φ direction t (approach t))
      (Icc 0 |φ|) t) ∧ coordinates (y 0) = approach |φ| ∧
    y (-(1/32)) ∈ stateSet twoBackwardExit ∧ y (1/32) ∈ stateSet twoExit ∧
    ∀ t ∈ Icc (-(1/32)) (1/32:ℝ),
      HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-(1/32)) (1/32)) t ∧
      dist (y t) (twoSidedReference t) ≤ 1232 / 10^9

theorem four_slabs_of_entry {uC zC uA zA : FA} {φ : ℝ} (h : SectionEntry .q0r470 uC zC uA zA φ) :
    FourSlabPassage uC zC uA zA φ := by
  obtain ⟨sign,approach,hs,ha,hb,ode,inside⟩ := h
  simp only [MirrorEndpoint.opposite,azimuth,Bool.false_eq_true,↓reduceIte,sub_zero]
    at ha ode inside
  have entry : coordinates.symm (approach |φ|) ∈ stateSet (MirrorEndpoint.start .q0r470) :=
    (mem_stateSet_identity (by rfl) _).mpr inside
  obtain ⟨y,hy,back,out,flow⟩ := four_slabs_from_state entry
  have radius : MirrorEndpoint.radius .q0r470 = 47/100 := by norm_num [MirrorEndpoint.radius]
  exact ⟨sign,approach,y,hs,ha,radius ▸ hb,ode,
    (congrArg coordinates hy).trans (coordinates.apply_symm_apply _),back,out,flow⟩

/-- Every qualifying birth on the same nested profiles has the four-slab passage. -/
theorem exists_nested_four_slabs :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2^19 → FourSlabPassage uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entries⟩ := exists_nested_section_entry
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => four_slabs_of_entry (entries _ φ ?_)⟩
  simpa [MirrorEndpoint.width,MirrorEndpoint.opposite,azimuth] using h

end PlasmaLean.Design.DommaschkMirrorLaunch
