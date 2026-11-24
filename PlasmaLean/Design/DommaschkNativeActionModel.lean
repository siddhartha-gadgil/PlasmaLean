/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkHarmonicHorner

/-! # Pointwise certificates for the native harmonic Taylor-model evaluation -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkNativeActionModel
open Certificates.TrajectoryTaylorModel DommaschkHarmonicHorner DommaschkBounceTaylor

/-- The exact rational weight and its native constant Taylor enclosure. -/
structure Weight where
  q : ℚ
  centre : ℤ
  error : ℤ
  bound : |2 ^ 80 * q - (centre : ℚ)| ≤ (error : ℚ)

def Weight.model (w : Weight) : Model := ofDyadic 80 [w.centre] w.error

theorem Weight.mem (w : Weight) (s : ℝ) : w.model.Mem s (w.q : ℝ) := by
  rw [Weight.model, mem_ofDyadic_iff]
  simp only [List.map_cons, List.map_nil, Certificates.QPoly.eval_cons, Certificates.QPoly.eval_nil,
    mul_zero, add_zero, Rat.cast_intCast]
  exact_mod_cast w.bound

abbrev WeightedRows := List (List Weight)
abbrev WeightedChannels := List (Wave × WeightedRows)
def exactRows (rs : WeightedRows) : Rows := rs.map fun row => row.map Weight.q
def exactChannels (cs : WeightedChannels) : Channels := cs.map fun (w, rs) => (w, exactRows rs)

def roundedStep (x a q : Model) : Model := addModel ((⟨7, 80⟩ : Format).mul a x) q

/-- Every Horner multiplication rounds before the coefficient is added. The stored
intermediates bound the amount of definitional reduction for each check. -/
inductive Steps (x : Model) : Model → List Model → Model → Prop
  | nil (a : Model) : Steps x a [] a
  | cons {v a q out : Model} {tail : List Model} (check : Matches (roundedStep x a q) v)
      (rest : Steps x v tail out) : Steps x a (q :: tail) out

inductive Run (x : Model) : List Model → Model → Prop
  | nil : Run x [] (constant 0)
  | cons {a out : Model} {tail : List Model} (steps : Steps x a tail out) :
      Run x (a :: tail) out

theorem Steps.mem {s v : ℝ} {x a out : Model} {ms : List Model} (steps : Steps x a ms out)
    (hs : |s| ≤ 1) (hx : x.Mem s v) {y : ℝ} (ha : a.Mem s y) {cs : List ℝ}
    (hc : List.Forall₂ (fun m c => m.Mem s c) ms cs) :
    out.Mem s (cs.foldl (fun acc q => acc * v + q) y) := by
  induction steps generalizing y cs with
  | nil => cases hc; exact ha
  | @cons next a q out tail check rest ih =>
    cases hc with
    | cons hq ht =>
      apply ih _ ht
      rw [← check.eq]
      exact mem_add ((⟨7, 80⟩ : Format).mul_mem hs ha hx) hq

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

theorem channel_cons {s u z θ : ℝ} {cs : WeightedChannels} {w : Wave} {rs : WeightedRows}
    {amp phase tail out : Model} (hs : |s| ≤ 1)
    (ha : amp.Mem s (rowsValue u z (exactRows rs))) (hw : phase.Mem s (w.value θ))
    (ht : tail.Mem s (value u z θ (exactChannels cs)))
    (check : Matches (addModel ((⟨7, 80⟩ : Format).mul amp phase) tail) out) :
    out.Mem s (value u z θ (exactChannels ((w, rs) :: cs))) := by
  rw [← check.eq]
  exact mem_add ((⟨7, 80⟩ : Format).mul_mem hs ha hw) ht

end PlasmaLean.Design.DommaschkNativeActionModel
