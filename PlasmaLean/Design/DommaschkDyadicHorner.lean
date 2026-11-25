/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeActionModel
public import PlasmaLean.Certificates.DyadicHornerStep

/-! # Harmonic Horner evaluation with exact integer multiply-add checks

Each proposed intermediate is a dyadic Taylor model. The integer discrepancy test
includes coefficient rounding, omitted powers and the three input radii.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkDyadicHorner
open Certificates.DyadicHornerStep (MulAdd)
open Certificates.TrajectoryTaylorModel DommaschkHarmonicHorner DommaschkBounceTaylor
open DommaschkNativeActionModel (Weight WeightedRows WeightedChannels exactRows exactChannels)

/-- A Horner run records the successive rounded accumulators. -/
inductive Steps (x : Model) : Model → List Model → Model → Prop
  | nil (a : Model) : Steps x a [] a
  | cons {v a q out : Model} {tail : List Model} (check : MulAdd a x q v)
      (rest : Steps x v tail out) : Steps x a (q :: tail) out

inductive Run (x : Model) : List Model → Model → Prop
  | nil : Run x [] (constant 0)
  | cons {a out : Model} {tail : List Model} (steps : Steps x a tail out) :
      Run x (a :: tail) out

theorem Steps.mem {s v : ℝ} {x a out : Model} {ms : List Model}
    (steps : Steps x a ms out)
    (hs : |s| ≤ 1) (hx : x.Mem s v) {y : ℝ} (ha : a.Mem s y) {cs : List ℝ}
    (hc : List.Forall₂ (fun m c => m.Mem s c) ms cs) :
    out.Mem s (cs.foldl (fun acc q => acc * v + q) y) := by
  induction steps generalizing y cs with
  | nil => cases hc; exact ha
  | @cons next a q out tail check rest ih =>
    cases hc with
    | cons hq ht =>
      apply ih _ ht
      exact check.mem hs ha hx hq

theorem Run.mem {s v : ℝ} {x out : Model} {ms : List Model} (run : Run x ms out)
    (hs : |s| ≤ 1) (hx : x.Mem s v) {cs : List ℝ}
    (hc : List.Forall₂ (fun m c => m.Mem s c) ms cs) :
    out.Mem s (horner 0 (fun acc q => acc * v + q) cs) := by
  cases run with
  | nil => cases hc; simpa only [horner, Rat.cast_zero] using constant_mem 0 s
  | cons steps => cases hc with | cons h ht => exact steps.mem hs hx h ht

theorem row_mem {s v : ℝ} {x out : Model} {ws : List Weight}
    (run : Run x (ws.map Weight.model) out) (hs : |s| ≤ 1) (hx : x.Mem s v) :
    out.Mem s (rowValue v (ws.map Weight.q)) := by
  apply run.mem hs hx
  clear run
  rw [List.map_map]
  induction ws with
  | nil => exact .nil
  | cons a ws ih => exact .cons (a.mem s) ih

theorem rows_mem {s u z : ℝ} {zm out : Model} {ms : List Model} {rs : WeightedRows}
    (run : Run zm ms out) (hs : |s| ≤ 1) (hz : zm.Mem s z)
    (hm : List.Forall₂ (fun m r => m.Mem s (rowValue u (r.map Weight.q))) ms rs) :
    out.Mem s (rowsValue u z (exactRows rs)) := by
  apply run.mem hs hz
  clear run
  simp only [exactRows, List.map_map]
  induction hm with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

theorem channel_cons {s u z θ : ℝ} {cs : WeightedChannels} {w : Wave}
    {rs : WeightedRows}
    {amp phase tail out : Model} (hs : |s| ≤ 1)
    (ha : amp.Mem s (rowsValue u z (exactRows rs))) (hw : phase.Mem s (w.value θ))
    (ht : tail.Mem s (value u z θ (exactChannels cs)))
    (check : MulAdd amp phase tail out) :
    out.Mem s (value u z θ (exactChannels ((w, rs) :: cs))) := by
  exact check.mem hs ha hw ht

end PlasmaLean.Design.DommaschkDyadicHorner
