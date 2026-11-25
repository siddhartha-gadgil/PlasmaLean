/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSectorHeightCrossings
public import PlasmaLean.Theory.Geometry.UniformRadialWindow

/-! # Positive radial measure for the action of the original first wells -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialActionWindows

open Set MeasureTheory Theory.KAM DommaschkRadialActionAlternative DommaschkSectorAction
open DommaschkRadialMirrorHeightBand DommaschkSectorHeightAction DommaschkSectorHeightCrossings
open DommaschkSectorActionBand DommaschkNativeWellAction DommaschkRadialSectionAction
open Kinetic.MirrorHeightAction UniformRadialWindow

variable {uC zC uA zA : FA}

/-- Integrate between the two first mirrors on the path born at this phase and radius. -/
def firstAction (family : Family uC zC uA zA) (φ : Phase) (h : Heights) (u : Radius) : ℝ :=
  let q : Domain := ((φ,u),h)
  action (field (family.path q.1)) (density (family.path q.1)) (family.L q) (family.R q) h

/-- A common positive radius length works for all phases, heights and target actions.
Consequently these quantities can be prescribed independently in each phase fiber. -/
def Samples (family : Family uC zC uA zA) : Prop :=
  ∀ ε > 0, ∃ length > 0, ∀ (φ : Phase) (h : Heights) (j : ℝ),
    |(h:ℝ) - level| ≤ delta → j ∈ Icc lowTarget highTarget →
      HasInterval (window (firstAction family φ h) j ε) length ∧
        ENNReal.ofReal length ≤ volume (window (firstAction family φ h) j ε)

/-- The uniformity comes from all three jointly continuous physical coordinates.
The strict radial face bounds ensure attainment individually in every fiber. -/
theorem of_faces (family : Family uC zC uA zA) (faces : ∀ φ : Phase, BandFaces uC zC uA zA φ) :
    Samples family := by
  let F (p : (Phase × Heights) × Radius) := firstAction family p.1.1 p.1.2 p.2
  have reorder : Continuous (fun p : (Phase × Heights) × Radius => ((p.1.1,p.2),p.1.2)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
      (continuous_snd.comp continuous_fst)
  have cf : Continuous F := (family.continuous_action.comp reorder).congr
    (fun p => (family.physical ((p.1.1,p.2),p.1.2)).mass)
  intro ε eps
  obtain ⟨length,pos,every⟩ := uniform (by norm_num) cf eps
  refine ⟨length,pos,?_⟩
  intro φ h j height target
  obtain ⟨below,above⟩ := face_signs family φ (faces φ) h j height target
  have inner_eq := (family.physical ((φ,inner),h)).mass
  have outer_eq := (family.physical ((φ,outer),h)).mass
  have fiber : Continuous (fun r : Radius => F ((φ,h),r)) :=
    cf.comp (continuous_const.prodMk continuous_id)
  let _ : PreconnectedSpace Radius := Subtype.preconnectedSpace isPreconnected_Icc
  have hit := intermediate_value_univ DommaschkRadialActionAlternative.inner outer fiber
    (show j ∈ Icc (F ((φ,h),inner)) (F ((φ,h),outer)) from
      ⟨(inner_eq.symm.trans_lt below).le,(above.trans_eq outer_eq).le⟩)
  have secured := every (φ,h) j hit
  exact ⟨secured,secured.volume⟩

end PlasmaLean.Design.DommaschkRadialActionWindows
