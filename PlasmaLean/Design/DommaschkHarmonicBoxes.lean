/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkHarmonicHorner
public import PlasmaLean.Certificates.NativeActionInterval

/-! # Spatial interval enclosures for angular harmonics in nested Horner form -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkHarmonicBoxes

open Certificates.NativeActionInterval DommaschkHarmonicHorner

def run (x : Box) (cs : List Box) : Box :=
  DommaschkHarmonicHorner.horner (rational 0) (fun a b => add (mul a x) b) cs

theorem run_mem {x : Box} {v : ℝ} (hv : x.Mem v) {cs : List Box} {qs : List ℝ}
    (hc : List.Forall₂ Box.Mem cs qs) :
    (run x cs).Mem (DommaschkHarmonicHorner.horner 0 (fun a b => a * v + b) qs) := by
  have go {bs ds} (h : List.Forall₂ Box.Mem bs ds) {acc : Box} {t : ℝ} (ha : acc.Mem t) :
      (bs.foldl (fun a b => add (mul a x) b) acc).Mem (ds.foldl (fun a b => a * v + b) t) := by
    induction h generalizing acc t with
    | nil => exact ha
    | cons first _ ih => exact ih (mem_add (mem_mul ha hv) first)
  cases hc with
  | nil => exact_mod_cast mem_rational 0
  | cons first rest => exact go rest first

def row (u : Box) (cs : List ℚ) : Box := run u (cs.map rational)
def rows (u z : Box) (rs : Rows) : Box := run z (rs.map (row u))

theorem row_mem {u : Box} {x : ℝ} (hu : u.Mem x) (cs : List ℚ) :
    (row u cs).Mem (rowValue x cs) := by
  apply run_mem hu
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact .cons (mem_rational c) ih

theorem rows_mem {u z : Box} {x y : ℝ} (hu : u.Mem x) (hz : z.Mem y) (rs : Rows) :
    (rows u z rs).Mem (rowsValue x y rs) := by
  apply run_mem hz
  induction rs with
  | nil => exact .nil
  | cons r rs ih => exact .cons (row_mem hu r) ih

def waveBox : Wave → Box
  | .one => rational 1
  | _ => ⟨-scale, scale⟩

theorem wave_mem (w : Wave) (θ : ℝ) : (waveBox w).Mem (w.value θ) := by
  have unit {v : ℝ} (lo : -1 ≤ v) (hi : v ≤ 1) : (⟨-scale, scale⟩ : Box).Mem v := by
    constructor <;> simp only [Int.cast_neg, Int.cast_ofNat] <;> linarith
  cases w with
  | one => exact_mod_cast mem_rational 1
  | sin1 | sin2 | sin3 => exact unit (Real.neg_one_le_sin _) (Real.sin_le_one _)
  | cos1 | cos2 | cos3 => exact unit (Real.neg_one_le_cos _) (Real.cos_le_one _)

def enclosure (u z : Box) : Channels → Box
  | [] => rational 0
  | (w, rs) :: cs => add (mul (rows u z rs) (waveBox w)) (enclosure u z cs)

theorem enclosure_mem {u z : Box} {x y : ℝ} (hu : u.Mem x) (hz : z.Mem y)
    (θ : ℝ) (cs : Channels) : (enclosure u z cs).Mem (value x y θ cs) := by
  induction cs with
  | nil => exact_mod_cast mem_rational 0
  | cons c cs ih => exact mem_add (mem_mul (rows_mem hu hz c.2) (wave_mem c.1 θ)) ih

end PlasmaLean.Design.DommaschkHarmonicBoxes
