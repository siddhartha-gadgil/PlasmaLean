/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionBlockBounds
public import PlasmaLean.Design.DommaschkSignedMirrorSlope
public import ActionBlockCache.DommaschkPhysicalLaunchBlocks
public import ActionPhysicalCellCache.DommaschkFirstPhysicalActionCell

/-! # Original quadrature covers on a single physical trajectory of any adequate length -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedActionBounds
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature
open DommaschkMirrorTubeCrossing DommaschkSignedObservable DommaschkPhysicalActionPanel
open DommaschkPhysicalLaunchBlocks DommaschkKam DommaschkBounceField Set

abbrev height : ℝ := 5300546391395933 / 5000000000000000

/-- Physical Cartesian arclength per radian along this very trajectory. -/
def physicalDensity (y : ℝ → Plane) (t : ℝ) : ℝ :=
  ‖deriv (fun s => Contract.cylPoint (y s 0) s (y s 1)) t‖

/-- Strengthen a property of an already selected trajectory, preserving the birth,
section state, tori, and the trajectory itself. -/
theorem keep {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {P Q : (ℝ → Plane) → Prop}
    (given : BirthWith (fun x => ∃ y, Path n fs bs fr br x y ∧ P y))
    (extra : ∀ x y, Path n fs bs fr br x y → Q y) :
    BirthWith (fun x => ∃ y, Path n fs bs fr br x y ∧ P y ∧ Q y) := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,each⟩ := given
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ hφ => ?_⟩
  obtain ⟨sign, approach, hs, ha, hx, ode, y, path, prop⟩ := each φ hφ
  exact ⟨sign, approach, hs, ha, hx, ode, y, path, prop, extra _ _ path⟩

/-- Both archived launch blocks with the actual Cartesian arclength density on this path. -/
def BirthBlocksOn (y : ℝ → Plane) : Prop :=
  Covers true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
    height (-(1/64)) birthBlocks ∧
  Covers true (physicalDensity y) (fun t => strength t (y t)) height (-(1/64)) birthBlocks ∧
  IntervalIntegrable (fun t => physicalDensity y t * Real.sqrt (2*(height-strength t (y t))))
    MeasureTheory.volume (-(1/64)) (1/64) ∧
  Kinetic.MirrorHeightAction.action (fun t => strength t (y t)) (physicalDensity y)
    (-(1/64)) (1/64) height < 5587/1000000

private theorem pack {w f : ℝ → ℝ}
    (limits : ∀ t ∈ Icc (-(1/64) : ℝ) (1/64),
      w t ≤ 1046878 / 1048576 ∧ max (2 * (height - f t)) 0 ≤ 2151939 / 67108864) :
    Covers true w f height (-(1/64)) birthBlocks := by
  apply covers_of_floor (A := 1046878) (G := 2151939)
  · intro b hb
    simp only [birthBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change floorTest 1046878 2151939 48 DommaschkActionQ0R470.slabGroup20[4].packed = true
      kernel_fact
    · change floorTest 1046878 2151939 48 DommaschkActionQ0R470.slabGroup20[5].packed = true
      kernel_fact
  · have stop : -(1 / 64 : ℝ) + birthBlocks.length / 64 = 1 / 64 := by
      change -(1 / 64 : ℝ) + (2 : ℝ) / 64 = _
      norm_num
    rwa [stop]

theorem launch {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {x : Plane} {y : ℝ → Plane} (path : Path n fs bs fr br x y) (large : 1 < n)
    (hf : 0 < fr.length) (hb : 0 < br.length) (frow : fr[0] = DommaschkPhysicalFirstStep.row)
    (brow : br[0] = DommaschkJacobianBackward000.row) : BirthBlocksOn y := by
  have reached : 0 < n := by omega
  obtain ⟨_, pf, ff⟩ := path.at_row (i := 0) reached false hf
  obtain ⟨_, pb, bf⟩ := path.at_row (i := 0) reached true hb
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_div, zero_add, frow] at ff
  simp only [↓reduceIte, Nat.cast_zero, zero_div, zero_add, brow] at bf
  have bounds (t : ℝ) (ht : t ∈ Icc (-(1/64) : ℝ) (1/64)) :
      (arcDensity (y t 0) t (y t 1) ≤ 1046878 / 1048576 ∧
        max (2 * (height - strength t (y t))) 0 ≤ 2151939 / 67108864) ∧
        0 < y t 0 ∧ 0 < atPoint dD (y t 0) t (y t 1) := by
    rcases le_total 0 t with pos | neg
    · have mem : t ∈ Icc 0 (1/64 : ℝ) := ⟨pos, ht.2⟩
      simpa only [show (1046878 : ℝ)/1048576 = 523439/524288 by norm_num, height] using
        DommaschkActionLaunchGeometry.fwd_bounds mem (ff _ mem)
    · have mem : -t ∈ Icc 0 (1/64 : ℝ) := ⟨by linarith, by linarith [ht.1]⟩
      simpa only [neg_neg, show (1046878 : ℝ)/1048576 = 523439/524288 by norm_num, height] using
        DommaschkActionLaunchGeometry.back_bounds mem (bf _ mem)
  have long : (1 : ℝ) < n := by exact_mod_cast large
  have inside {t : ℝ} (ht : t ∈ Icc (-(1/64) : ℝ) (1/64)) :
      t ∈ Ioo (-(n : ℝ)/64) (n/64) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have actual (t : ℝ) (ht : t ∈ Icc (-(1/64) : ℝ) (1/64)) :
      physicalDensity y t ≤ 1046878 / 1048576 ∧
        max (2 * (height - strength t (y t))) 0 ≤ 2151939 / 67108864 := by
    obtain ⟨b, hr, hd⟩ := bounds t ht
    simpa only [physicalDensity, arcDensity_on_path path (inside ht) hr hd] using b
  have cont : ContinuousOn y (Icc (-(1/64) : ℝ) (1/64)) := by
    intro t ht
    exact ((path.ode t (Ioo_subset_Icc_self (inside ht))).hasDerivAt
      (Icc_mem_nhds (inside ht).1 (inside ht).2)).continuousAt.continuousWithinAt
  have strengthCont : ContinuousOn (fun t => strength t (y t)) (Icc (-(1/64) : ℝ) (1/64)) := by
    simpa only [one_mul] using continuousOn_strength cont 1 (fun t ht => (bounds t ht).2.1)
  obtain ⟨integ, estimate⟩ := action_le_uniform (w := physicalDensity y)
    (A := 1046878 / 1048576) (S := 179071/1000000) (h := height) (by norm_num)
    ((stronglyMeasurable_deriv _).norm.aestronglyMeasurable) strengthCont (by norm_num)
    (fun t ht => ⟨norm_nonneg _, (actual t ht).1, (actual t ht).2.trans (by norm_num)⟩)
  exact ⟨pack (fun t ht => (bounds t ht).1), pack actual, integ, estimate.trans_lt (by norm_num)⟩

/-- The first panel in chronological order, at the upper mirror on the negative branch. -/
def EarliestOn (y : ℝ → Plane) : Prop :=
  Cell true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t)) height
    (-325/64) (DommaschkActionQ0R470.slabs[0]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed

theorem earliest {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {x : Plane} {y : ℝ → Plane} (path : Path n fs bs fr br x y) (reached : 324 < n)
    (hb : 324 < br.length) (row : br[324] = DommaschkFirstPhysicalActionCell.row) : EarliestOn y := by
  obtain ⟨_, prev, tube⟩ := path.at_row reached true hb
  change ∀ t ∈ Icc (324/64 : ℝ) ((324+1)/64), y (-t) ∈ (physicalSlab prev br[324] (324/64)).tube t at tube
  rw [row, show (324 : ℝ) + 1 = 325 by norm_num] at tube
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have clocks := DommaschkSignedMirrorSlope.clock_odes path (show (0 : ℝ) ≤ 324/64 by norm_num)
    (show (325 : ℝ)/64 ≤ n/64 by linarith)
  simpa only [EarliestOn, height, neg_neg] using
    DommaschkFirstPhysicalActionCell.physical_cell clocks.2 tube

end PlasmaLean.Design.DommaschkSignedActionBounds
