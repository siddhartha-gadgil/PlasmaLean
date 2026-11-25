/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialAccessibleBirth
public import PlasmaLean.Design.DommaschkRibbonFirstMirrors

/-! # Parallel speed through a regular segment of the original radial birth family -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialPassingCore
open Set Theory.KAM
open Certificates.PositionFrameSlabs (Plane coordinates stateSet mem_stateSet_identity)
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkRadialRibbonEntry
open DommaschkMirrorLaunch DommaschkNativeWellAction DommaschkFirstMirrorLaunchSign
open DommaschkRibbonFirstMirrors

/-- For any energy-to-moment ratio at or above the lower archived level, the normalized
parallel speed stays uniformly positive throughout this signed angular interval. -/
def Passing (y : ℝ → Plane) (T : ℝ) : Prop :=
  ∀ t ∈ Icc (-T) T, field y t < 132 / 125 ∧
    ∀ h : ℝ, (height false : ℝ) ≤ h → 1 / 12 < Real.sqrt (2 * (h - field y t))

theorem passing_of_below {y : ℝ → Plane} {T : ℝ} (low : Below y 0 T (132 / 125)) :
    Passing y T := by
  intro t ht
  have f : field y t < 132 / 125 := low.signed t ht
  refine ⟨f, fun h hh => ?_⟩
  have margin : (1 / 12 : ℝ) ^ 2 < 2 * ((height false : ℝ) - 132 / 125) := by
    norm_num [height]
  apply (Real.lt_sqrt (by norm_num)).2
  linarith

/-- Transfer both existence and the certified path property from a section ball to the
original interpolated birth at its own phase, on any sufficiently long regular window. -/
theorem from_seed {uC zC uA zA : FA} {u φ T : ℝ} {k : Fin 4} {P : (ℝ → Plane) → Prop}
    (wide : 1 / 64 ≤ T) (small : |φ| ≤ 1 / 2 ^ 19) (entry : Passage uC zC uA zA u φ k)
    (solve : ∀ x ∈ stateSet (seed k), ∃ y : ℝ → Plane, y 0 = x ∧ Enclosed y (-T) T ∧ P y) :
    ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧ Enclosed y (-T) T ∧ P y := by
  obtain ⟨σ, a, unit, clock, start, approach, ball, _⟩ := entry
  obtain ⟨y, atZero, path, prop⟩ := solve (coordinates.symm (a |φ|))
    ((mem_stateSet_identity (s := seed k) (by rfl) _).mpr ball)
  have eq := DommaschkPhysicalFirstMirrorValues.original_position
    (T := T) (phase := 0) (φ := φ) (σ := σ) (a := a) (y := y) wide
    (by simpa only [sub_zero] using small.trans (by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 1 / 64))
    unit (by simpa only [sub_zero] using clock) (by simpa only [sub_zero] using atZero)
    (by simpa only [sub_zero] using approach) (fun t ht => (path.ode t ht).hasDerivWithinAt)
    (fun t ht => path.region _ (Icc_subset_Icc (neg_le_neg wide) wide ht))
  exact ⟨y, by simpa only [sub_zero, start] using eq, path, prop⟩

end PlasmaLean.Design.DommaschkRadialPassingCore
