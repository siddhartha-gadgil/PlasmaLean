/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorSublevelPanels

/-! # Integer certificates for finite parallel-speed grids

Cell widths are measured in speed ticks. Heights are measured in arclength ticks.
The arithmetic certificate and the inequalities about the measured well are separate.
-/

@[expose] public section

namespace PlasmaLean.Certificates.SublevelActionGrid

open MeasureTheory PlasmaLean.Kinetic.MirrorSublevelAction

/-- Width and a one-sided arclength at the corresponding speed threshold. -/
structure Cell where
  width : ℕ
  height : ℕ
  deriving Inhabited

abbrev Table := Array Cell

/-- Return a zero-width cell beyond the end so the speed grid extends monotonically. -/
def cell (g : Table) (i : ℕ) : Cell := g[i]?.getD default

/-- Cumulative speed at a node in integer ticks. -/
def tick (g : Table) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, (cell g j).width

/-- Unscaled rectangle sum. -/
def mass (g : Table) : ℕ := ∑ j ∈ Finset.range g.size, (cell g j).width * (cell g j).height

/-- Count empty speed panels, using the same cell lookup as the integer mass. -/
def emptyCells (g : Table) : ℕ :=
  ∑ i ∈ Finset.range g.size, if (cell g i).width = 0 then 1 else 0

theorem widths_positive {g : Table} (h : emptyCells g = 0) {i : ℕ} (hi : i < g.size) :
    0 < (cell g i).width := by
  have hle := Finset.single_le_sum (f := fun j => if (cell g j).width = 0 then 1 else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
  change (if (cell g i).width = 0 then 1 else 0) ≤ emptyCells g at hle
  rw [h] at hle
  by_contra! hz
  simp [Nat.eq_zero_of_le_zero hz] at hle

noncomputable def speed (g : Table) (scale i : ℕ) : ℝ := tick g i / (scale : ℝ)

noncomputable def height (g : Table) (scale i : ℕ) : ℝ := (cell g i).height / (scale : ℝ)

/-- For an upper sum use the left endpoint, and for a lower sum use the right endpoint. -/
def NodeBounds {X : Type*} [MeasurableSpace X] (μ : Measure X) (B : X → ℝ) (h : ℝ)
    (g : Table) (s d : ℕ) (upper : Bool) : Prop :=
  ∀ i < g.size, if upper then
    sublevelLength μ B (h - (speed g s i)^2 / 2) ≤ height g d i
  else height g d i ≤ sublevelLength μ B (h - (speed g s (i+1))^2 / 2)

/-- Integer checks for a grid on [0,2] and a strict comparison with target `p/q`. -/
structure Certified (g : Table) (s d : ℕ) (upper : Bool) (p q : ℕ) : Prop where
  speed_pos : 0 < s
  density_pos : 0 < d
  target_den_pos : 0 < q
  finish : tick g g.size = 2*s
  comparison : if upper then mass g * q < p * (s*d) else p * (s*d) < mass g * q

theorem speed_monotone (g : Table) (s : ℕ) : Monotone (speed g s) := by
  apply monotone_nat_of_le_succ
  intro i
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
  exact_mod_cast (show tick g i ≤ tick g (i+1) by simp [tick, Finset.sum_range_succ])

/-- The integer used by the checker equals the real rectangle sum after scaling. -/
theorem panelSum_eq (g : Table) (s d : ℕ) :
    panelSum (speed g s) (height g d) g.size = (mass g : ℝ) / ((s : ℝ)*d) := by
  simp only [panelSum, mass, Nat.cast_sum, Finset.sum_div, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [speed, height, tick, Finset.sum_range_succ, Nat.cast_add, add_div,
    add_sub_cancel_left, div_mul_div_comm]

/-- A physical action bound follows from the correctly directed node inequalities.
The floor guarantees the complete speed range lies in [0,2]. -/
theorem action_target {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {B : X → ℝ} (hB : AEMeasurable B μ) {h : ℝ} (floorB : ∀ᵐ x ∂μ, h - 2 ≤ B x)
    {g : Table} {s d p q : ℕ} {upper : Bool} (cert : Certified g s d upper p q)
    (nodes : NodeBounds μ B h g s d upper) :
    if upper then action μ B h < (p : ℝ)/q else (p : ℝ)/q < action μ B h := by
  have start : speed g s 0 = 0 := by simp [speed, tick]
  have stop : speed g s g.size = Real.sqrt (2 * (h - (h - 2))) := by
    have hs : (s : ℝ) ≠ 0 := by exact_mod_cast cert.speed_pos.ne'
    rw [show (2 * (h - (h - 2))) = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [speed, cert.finish, hs]
  have hsd : 0 < (s : ℝ) * d := mul_pos (by exact_mod_cast cert.speed_pos)
    (by exact_mod_cast cert.density_pos)
  have hq : (0 : ℝ) < q := by exact_mod_cast cert.target_den_pos
  cases upper with
  | false =>
    have lower := (action_between_panel_sums μ hB floorB (speed_monotone g s) start stop
      (lo := height g d) (hi := fun i => sublevelLength μ B (h - (speed g s i)^2/2))
      nodes (fun _ _ => le_rfl)).1
    rw [panelSum_eq] at lower
    apply lt_of_lt_of_le _ lower
    apply (div_lt_div_iff₀ hq hsd).mpr
    exact_mod_cast cert.comparison
  | true =>
    have higher := (action_between_panel_sums μ hB floorB (speed_monotone g s) start stop
      (lo := fun i => sublevelLength μ B (h - (speed g s (i+1))^2/2)) (hi := height g d)
      (fun _ _ => le_rfl) nodes).2
    rw [panelSum_eq] at higher
    apply lt_of_le_of_lt higher
    apply (div_lt_div_iff₀ hsd hq).mpr
    exact_mod_cast cert.comparison

end PlasmaLean.Certificates.SublevelActionGrid
