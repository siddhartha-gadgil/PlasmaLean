/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGroupedMirrorModels

/-! # Transfer a grouped spatial Jacobian to the clock of an individual trial ellipse -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkGroupedTrialJet
open Certificates TrajectoryTaylorModel DommaschkBounceTaylor DommaschkGroupedMirrorModels

/-- Each spatial and angular model for a single trial rectangle fits the same
affine part of the larger group. -/
structure BoxMap (a b : ℚ) (small large : Inputs) : Prop where
  clock : |a| + |b| ≤ 1
  radial : Fits a b small.u large.u
  height : Fits a b small.z large.z
  cosine : Fits a b small.cos large.cos
  sine : Fits a b small.sin large.sin

theorem BoxMap.mem {a b : ℚ} {small large : Inputs} (h : BoxMap a b small large)
    {s u z c v : ℝ} (hs : |s| ≤ 1) (inputs : small.Mem s u z c v) :
    |(a : ℝ) + b * s| ≤ 1 ∧ large.Mem ((a : ℝ) + b * s) u z c v := by
  refine ⟨?_, h.radial.mem hs inputs.1, h.height.mem hs inputs.2.1,
    h.cosine.mem hs inputs.2.2.1, h.sine.mem hs inputs.2.2.2⟩
  calc
    _ ≤ |(a : ℝ)| + |(b : ℝ)| * |s| := by
      simpa only [abs_mul] using abs_add_le (a : ℝ) ((b : ℝ) * s)
    _ ≤ |(a : ℝ)| + |(b : ℝ)| :=
      add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)
    _ ≤ 1 := by exact_mod_cast h.clock

/-- Rounding a value computed on the group into the original normalized time. -/
def Pullback (a b : ℚ) (group row : Model) : Prop :=
  group.radius + magnitude (difference (TrajectoryTrig.affine a b group.poly) row.poly) ≤ row.radius

private theorem eval_affine (a b : ℚ) (p : List ℚ) (s : ℝ) :
    QPoly.eval (TrajectoryTrig.affine a b p) s = QPoly.eval p ((a : ℝ) + b * s) := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [TrajectoryTrig.affine, ih, mul_comm]

theorem Pullback.mem {a b : ℚ} {group row : Model} (h : Pullback a b group row)
    {s x : ℝ} (hs : |s| ≤ 1) (hx : group.Mem ((a : ℝ) + b * s) x) : row.Mem s x := by
  let m : Model := ⟨TrajectoryTrig.affine a b group.poly, group.radius⟩
  have hm : m.Mem s x := by simpa only [Model.Mem, m, eval_affine] using hx
  exact enclose hs hm h

end PlasmaLean.Design.DommaschkGroupedTrialJet
