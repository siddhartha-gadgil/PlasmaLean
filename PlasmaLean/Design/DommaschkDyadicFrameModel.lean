/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.DyadicHornerStep
public import PlasmaLean.Design.DommaschkJacobianFrames

/-! # Integer witnesses for affine-frame entries and matrix arithmetic -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkDyadicFrameModel
open Certificates PositionFrameSlabs TrajectoryTaylorModel DyadicHornerStep

abbrev constant (c : ℤ) := ofDyadic 80 [2^80*c] 0

theorem constant_mem (c : ℤ) (s : ℝ) : (constant c).Mem s c := by
  rw [mem_ofDyadic_iff]
  norm_num [QPoly.eval_cons, QPoly.eval_nil]

theorem mul_mem {a b out : Model} (h : MulAdd a b (constant 0) out)
    {s x y : ℝ} (hs : |s| ≤ 1) (hx : a.Mem s x) (hy : b.Mem s y) :
    out.Mem s (x*y) := by simpa using h.mem hs hx hy (constant_mem 0 s)

theorem add_mem {a b out : Model} (h : MulAdd a (constant 1) b out)
    {s x y : ℝ} (hs : |s| ≤ 1) (hx : a.Mem s x) (hy : b.Mem s y) :
    out.Mem s (x+y) := by simpa using h.mem hs hx (constant_mem 1 s) hy

theorem sub_mem {a b out : Model} (h : MulAdd b (constant (-1)) a out)
    {s x y : ℝ} (hs : |s| ≤ 1) (hx : a.Mem s x) (hy : b.Mem s y) :
    out.Mem s (x-y) := by
  simpa only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, add_comm (-y), sub_eq_add_neg]
    using h.mem hs hy (constant_mem (-1) s) hx

theorem neg_mem {a out : Model} (h : MulAdd a (constant (-1)) (constant 0) out)
    {s x : ℝ} (hs : |s| ≤ 1) (hx : a.Mem s x) : out.Mem s (-x) := by
  simpa using h.mem hs hx (constant_mem (-1) s) (constant_mem 0 s)

/-- The normalized physical frame and its derivative on the original 1/64 clock. -/
theorem frame_mem (l r : ℤ) (s : ℝ) :
    (ofDyadic 80 [2^39*(l+r),2^39*(r-l)] 0).Mem s (entry l r s) := by
  rw [mem_ofDyadic_iff]
  norm_num [entry,QPoly.eval_cons,QPoly.eval_nil,abs_nonpos_iff]
  ring

theorem velocity_mem (l r : ℤ) (s : ℝ) :
    (ofDyadic 80 [2^46*(r-l)] 0).Mem s (64*(entry l r 1 - entry l r (-1))) := by
  rw [mem_ofDyadic_iff]
  norm_num [entry,QPoly.eval_cons,QPoly.eval_nil,abs_nonpos_iff]
  ring

end PlasmaLean.Design.DommaschkDyadicFrameModel
