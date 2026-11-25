/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.ClosedIntervalODEUniqueness

/-! # Uniqueness from an interior point of a closed ODE interval -/

@[expose] public section
namespace PlasmaLean.Fields
open Set

/-- The paths need only have the ordinary within-interval derivatives, including at
either end. Joint local smoothness along the second path gives uniqueness. -/
theorem ode_eqOn_of_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {a b c : ℝ} {x y : ℝ → E} (hc : c ∈ Icc a b)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (F t (x t)) (Icc a b) t)
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (F t (y t)) (Icc a b) t)
    (regular : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 (fun p : ℝ × E => F p.1 p.2) (t,y t))
    (at_c : x c = y c) : EqOn x y (Icc a b) := by
  have left : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hc.2
  have before := ode_eqOn_of_terminal (fun t ht => (hx t (left ht)).mono left)
    (fun t ht => (hy t (left ht)).mono left) (fun t ht => regular t (left ht)) at_c
  have rev : MapsTo (fun t : ℝ => -t) (Icc (-b) (-c)) (Icc a b) :=
    fun _ ht => ⟨by linarith [ht.2,hc.1],by linarith [ht.1]⟩
  let G := fun (t : ℝ) (p : E) => -F (-t) p
  have flip (z : ℝ → E) (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (F t (z t)) (Icc a b) t)
      (t : ℝ) (ht : t ∈ Icc (-b) (-c)) :
      HasDerivWithinAt (fun s => z (-s)) (G t (z (-t))) (Icc (-b) (-c)) t := by
    simpa only [G,Function.comp_def,neg_one_smul] using
      (hz (-t) (rev ht)).scomp t (hasDerivAt_neg t).hasDerivWithinAt rev
  have reg (t : ℝ) (ht : t ∈ Icc (-b) (-c)) :
      ContDiffAt ℝ 1 (fun p : ℝ × E => G p.1 p.2) (t,y (-t)) := by
    let ρ := fun p : ℝ × E => (-p.1,p.2)
    have smooth : ContDiff ℝ 1 ρ := contDiff_fst.neg.prodMk contDiff_snd
    exact ((regular (-t) (rev ht)).comp (t,y (-t)) smooth.contDiffAt).neg
  have after := ode_eqOn_of_terminal (flip x hx) (flip y hy) reg
    (by simpa only [neg_neg] using at_c)
  intro t ht
  rcases le_total t c with h | h
  · exact before ⟨ht.1,h⟩
  · simpa only [neg_neg] using after (show -t ∈ Icc (-b) (-c) from ⟨neg_le_neg ht.2,neg_le_neg h⟩)

end PlasmaLean.Fields
