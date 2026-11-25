/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRibbonFirstMirrors
public import PlasmaLean.Theory.Kinetic.FirstWellContinuation

/-! # Excluding the first-well grazing alternative for the radial ribbon -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRibbonFirstMirrors
open Set Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign
open Kinetic.MirrorActionEnvelope

/-- The true signed field profile begins strictly below the target height. -/
theorem NoGrazing.birth {y : ℝ → Plane} (h : NoGrazing y) : strength 0 (y 0) < height true :=
  h.1 0 (by norm_num [lowerClock])

/-- Every first well containing the common section has nonstationary endpoints, with the
physical derivative negative on the left and positive on the right. -/
theorem NoGrazing.well_slopes {y : ℝ → Plane} {l r : ℝ} (good : NoGrazing y)
    (well : LaunchWell (fun t => strength t (y t)) 0 (height true) l r) :
    deriv (fun t => strength t (y t)) l < 0 ∧ 0 < deriv (fun t => strength t (y t)) r := by
  obtain ⟨_early,⟨⟨f,hf,fhit,fearly,_,_⟩,⟨b,hb,bhit,bearly,_,_⟩⟩,signed⟩ := good
  have zero : (0:ℝ) < lowerClock := by norm_num [lowerClock]
  have left : -b < 0 := neg_lt_zero.mpr (zero.trans hb.1)
  have right : 0 < f := zero.trans hf.1
  have same : LaunchWell (fun t => strength t (y t)) 0 (height true) (-b) f := by
    refine ⟨left,right,bhit,fhit,?_⟩
    intro t ht
    rcases le_total 0 t with pos | neg
    · exact fearly t ⟨pos,ht.2⟩
    · simpa only [neg_neg] using bearly (-t) ⟨neg_nonneg.mpr neg,by linarith [ht.1]⟩
  obtain ⟨leftEq,rightEq⟩ := well.unique same
  rw [leftEq,rightEq]
  have bl : -b ∈ Ioo (-capClock) capClock := ⟨neg_lt_neg hb.2,left.trans (right.trans hf.2)⟩
  have fr : f ∈ Ioo (-capClock) capClock := ⟨bl.1.trans (left.trans right),hf.2⟩
  exact ⟨(signed _ bl bhit).2 left,(signed _ fr fhit).1 right⟩

/-- This excludes exactly the local-maximum alternative in first-well continuation. -/
theorem NoGrazing.excludes_localMax {y : ℝ → Plane} {l r : ℝ} (good : NoGrazing y)
    (well : LaunchWell (fun t => strength t (y t)) 0 (height true) l r) :
    ¬(IsLocalMax (fun t => strength t (y t)) l ∨ IsLocalMax (fun t => strength t (y t)) r) := by
  obtain ⟨left,right⟩ := good.well_slopes well
  rintro (hl | hr)
  · exact left.ne hl.deriv_eq_zero
  · exact right.ne' hr.deriv_eq_zero

end PlasmaLean.Design.DommaschkRibbonFirstMirrors
