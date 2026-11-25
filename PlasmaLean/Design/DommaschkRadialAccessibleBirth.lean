/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialSectionAction

/-! # The original birth lies in the accessible component of the symmetry section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialAccessibleBirth
open Set Theory.KAM
open Certificates.PositionFrameSlabs (Plane coordinates stateSet mem_stateSet_identity)
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkRadialRibbonEntry
open DommaschkMirrorLaunch DommaschkNativeWellAction Kinetic.MirrorActionEnvelope

/-- A true two-sided neighborhood of the symmetry section with a low-field central segment. -/
def Accessible (y : ℝ → Plane) : Prop :=
  Enclosed y (-(15 / 64)) (15 / 64) ∧ ∀ t ∈ Icc (-(1 / 8)) (1 / 8), field y t < level

theorem from_seed {uC zC uA zA : FA} {u φ : ℝ} {k : Fin 4}
    (small : |φ| ≤ 1 / 2 ^ 19) (entry : Passage uC zC uA zA u φ k)
    (solve : ∀ x ∈ stateSet (seed k), ∃ y : ℝ → Plane, y 0 = x ∧ Accessible y) :
    ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧ Accessible y := by
  obtain ⟨σ, a, unit, clock, start, approach, ball, _⟩ := entry
  obtain ⟨y, atZero, ode, low⟩ := solve (coordinates.symm (a |φ|))
    ((mem_stateSet_identity (s := seed k) (by rfl) _).mpr ball)
  have original := DommaschkPhysicalFirstMirrorValues.original_position
    (T := 15 / 64) (phase := 0) (φ := φ) (σ := σ) (a := a) (y := y) (by norm_num)
    (by simpa only [sub_zero] using small.trans (by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 1 / 64))
    unit (by simpa only [sub_zero] using clock) (by simpa only [sub_zero] using atZero)
    (by simpa only [sub_zero] using approach) (fun t ht => (ode.ode t ht).hasDerivWithinAt)
    (fun t ht => ode.region _ (Icc_subset_Icc (by norm_num) (by norm_num) ht))
  exact ⟨y, by simpa only [sub_zero, start] using original, ode, low⟩

/-- Every first well around the section is also a first well around the actual birth on
any independent full trajectory through that birth. The mirror pair and its integral agree. -/
theorem well_at_birth {z y : ℝ → Plane} {l r φ : ℝ} (short : Accessible z)
    (small : |φ| ≤ 1 / 2 ^ 19) (path : Enclosed y (-(15 / 64)) (15 / 64))
    (born : z φ = y φ) (well : LaunchWell (field y) 0 level l r) :
    LaunchWell (field y) φ level l r := by
  obtain ⟨zl, low⟩ := short
  have inCore : φ ∈ Icc (-(1 / 8)) (1 / 8) := abs_le.mp (small.trans (by norm_num))
  have core : Icc (-(1 / 8 : ℝ)) (1 / 8) ⊆ Icc (-(15 / 64)) (15 / 64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  obtain ⟨same, _⟩ := zl.agree path (core inCore) born
  have good (t : ℝ) (ht : t ∈ Icc (-(1 / 8)) (1 / 8)) : field y t < level :=
    (same (core ht)) ▸ low t ht
  have left : l < φ := by
    by_contra! earlier
    exact (good l ⟨inCore.1.trans earlier, by linarith [well.left_lt]⟩).ne well.left_hit
  have right : φ < r := by
    by_contra! later
    exact (good r ⟨by linarith [well.lt_right], later.trans inCore.2⟩).ne well.right_hit
  exact ⟨left, right, well.left_hit, well.right_hit, well.accessible⟩

end PlasmaLean.Design.DommaschkRadialAccessibleBirth
