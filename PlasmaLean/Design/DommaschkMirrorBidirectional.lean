/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalBackwardFirstStep
public import PlasmaLean.Design.DommaschkMirrorFirstPassage

/-! # One physical QA2R field line on both sides of the section

The two recorded outward integrations share their actual transferred state.
Changing the backward elapsed time to negative geometric angle gives a single
differentiable line through the section, with the two saved endpoint ellipsoids.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKamC KamNewton Set
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2
open DommaschkJacobian (euclideanFlow)

abbrev pairedForwardRow := DommaschkPhysicalFirstStep.row
abbrev pairedBackwardRow := DommaschkJacobianBackward000.row

/-- The nominal reference uses elapsed angle on its own side of the section. -/
def pairedReference (t : ℝ) : Plane :=
  if t ≤ 0 then reference 0 pairedBackwardRow (-t) else reference 0 pairedForwardRow t

private theorem reverse_field (t : ℝ) (x : Plane) :
    -euclideanFlow 0 (-1) (-t) x = euclideanFlow 0 1 t x := by
  ext i
  fin_cases i <;> simp [euclideanFlow,physicalFlow]

/-- One differentiable physical line for every actual point in the common incoming set. -/
theorem paired_trajectory {x : Plane} (hx : x ∈ stateSet DommaschkPhysicalFirstStep.seed) :
    ∃ y : ℝ → Plane, y 0 = x ∧ y (-(1/64)) ∈ stateSet (next pairedBackwardRow) ∧
      y (1/64) ∈ stateSet (next pairedForwardRow) ∧ ∀ t ∈ Icc (-(1/64)) (1/64 : ℝ),
        HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-(1/64)) (1/64)) t ∧
        dist (y t) (pairedReference t) ≤ 123/10^8 := by
  obtain ⟨f, ef, xf, hf⟩ := DommaschkPhysicalFirstStep.physical_first_step.solve x hx
  obtain ⟨b, eb, xb, hb⟩ :=
    DommaschkPhysicalBackwardFirstStep.physical_backward_step.solve x hx
  change f 0 = x at ef
  change b 0 = x at eb
  let y := fun t : ℝ => if t ≤ 0 then b (-t) else f t
  have left : EqOn y (fun t => b (-t)) (Icc (-(1/64)) 0) := fun t ht => ite_eq_left ht.2
  have right : EqOn y f (Icc 0 (1/64)) := by
    intro t ht
    rcases ht.1.eq_or_lt with eq | pos
    · rw [← eq]
      simp [y,eb,ef]
    · exact ite_eq_right pos.not_ge
  have hmap : MapsTo Neg.neg (Icc (-(1/64:ℝ)) 0) (Icc 0 (1/64)) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have eqL {t : ℝ} (ht : t ∈ Icc (-(1/64)) 0) :
      HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-(1/64)) 0) t := by
    have b' := (hb (-t) (by simpa [physicalSlab] using hmap ht)).1
    have br : HasDerivWithinAt b (euclideanFlow 0 (-1) (-t) (b (-t)))
        (Icc 0 (1/64)) (-t) := by simpa [physicalSlab] using b'
    have d := br.scomp t (hasDerivWithinAt_neg t (Icc (-(1/64)) 0)) hmap
    rw [left ht]
    apply HasDerivWithinAt.congr_of_mem _ (fun u hu => left hu) ht
    simpa only [Function.comp_def,neg_one_smul,reverse_field] using d
  have eqR {t : ℝ} (ht : t ∈ Icc 0 (1/64)) :
      HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc 0 (1/64)) t := by
    rw [right ht]
    apply HasDerivWithinAt.congr_of_mem _ (fun u hu => right hu) ht
    simpa [physicalSlab] using (hf t (by simpa [physicalSlab] using ht)).1
  refine ⟨y, by simpa [y] using eb, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simpa [y,physicalSlab] using xb
  · rw [right (by norm_num : (1/64:ℝ) ∈ Icc 0 (1/64))]
    simpa [physicalSlab] using xf
  · have l : HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-(1/64)) 0) t := by
      by_cases h : t ∈ Icc (-(1/64:ℝ)) 0
      · exact eqL h
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
    have r : HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc 0 (1/64)) t := by
      by_cases h : t ∈ Icc 0 (1/64:ℝ)
      · exact eqR h
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
    rw [← Icc_union_Icc_eq_Icc (show -(1/64:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 1/64 by norm_num)]
    exact l.union r
  · by_cases h : t ≤ 0
    · have hm := hmap ⟨ht.1,h⟩
      have e := (hb (-t) (by simpa [physicalSlab] using hm)).2.2
      simp only [pairedReference,y,h,ite_true]
      refine e.trans ?_
      change (1481700234749866733 : ℝ) / 2^80 ≤ _
      norm_num
    · have hh : t ∈ Icc 0 (1/64:ℝ) := ⟨(lt_of_not_ge h).le,ht.2⟩
      have e := (hf t (by simpa [physicalSlab] using hh)).2.2
      simp only [pairedReference,y,h,ite_false]
      refine e.trans ?_
      change (1481700234749866732:ℝ) / 2^80 ≤ _
      norm_num

/-- A birth reaches a single physical curve across the section, with both
exit enclosures and the same position error on the whole signed arc. -/
def BidirectionalPassage (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ (sign : ℝ) (approach : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |sign| = 1 ∧ φ + sign * |φ| = 0 ∧ approach 0 = birth uC zC uA zA (47/100) φ ∧
    (∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach (physicalFlow φ sign t (approach t))
      (Icc 0 |φ|) t) ∧ coordinates (y 0) = approach |φ| ∧
    y (-(1/64)) ∈ stateSet (next pairedBackwardRow) ∧ y (1/64) ∈ stateSet (next pairedForwardRow) ∧
    ∀ t ∈ Icc (-(1/64)) (1/64 : ℝ),
      HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-(1/64)) (1/64)) t ∧
      dist (y t) (pairedReference t) ≤ 123/10^8

theorem bidirectional_of_entry {uC zC uA zA : FA} {φ : ℝ} (h : SectionEntry .q0r470 uC zC uA zA φ) :
    BidirectionalPassage uC zC uA zA φ := by
  obtain ⟨sign,approach,hs,ha,hb,ode,inside⟩ := h
  simp only [MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ↓reduceIte, sub_zero]
    at ha ode inside
  have entry : coordinates.symm (approach |φ|) ∈ stateSet DommaschkPhysicalFirstStep.seed :=
    (mem_stateSet_identity (by rfl) _).mpr inside
  obtain ⟨y,hy,ey,fy,flow⟩ := paired_trajectory entry
  have radius : MirrorEndpoint.radius .q0r470 = 47/100 := by norm_num [MirrorEndpoint.radius]
  exact ⟨sign,approach,y,hs,ha,radius ▸ hb,ode,
    (congrArg coordinates hy).trans (coordinates.apply_symm_apply _),ey,fy,flow⟩

/-- Every qualifying birth on the same nested pair has the two-sided, signed-angle passage. -/
theorem exists_nested_bidirectional :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2^19 → BidirectionalPassage uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entries⟩ := exists_nested_section_entry
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => bidirectional_of_entry (entries _ φ ?_)⟩
  simpa [MirrorEndpoint.width, MirrorEndpoint.opposite, azimuth] using h

end PlasmaLean.Design.DommaschkMirrorLaunch
