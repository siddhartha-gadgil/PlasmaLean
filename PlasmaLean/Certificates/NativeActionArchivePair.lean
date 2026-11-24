/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeActionColumns

/-! # Reusing a native interval proof when the two original archive records agree -/

@[expose] public section
namespace PlasmaLean.Certificates.NativeActionInterval
open MirrorActionQuadrature

/-- The enclosing chronological block may differ after the low 72 bits. -/
structure SameDigits (p q : ℕ) : Prop where
  density_eq : density p = density q
  sq_eq : speedSq p = speedSq q
  speed_eq : speed p = speed q

theorem Checked.of_sameDigits {upper : Bool} {v : Five Box} {root : Box} {h : ℚ} {p q : ℕ}
    (w : Checked upper v root h p) (d : SameDigits p q) : Checked upper v root h q :=
  { w with
    density_tick := w.density_tick.trans (congrArg (fun n : ℕ => (n : ℤ)) d.density_eq)
    speed_tick := w.speed_tick.trans (congrArg (fun n : ℕ => (n : ℤ)) d.sq_eq)
    packed_root := by simpa only [rootTest, ← d.sq_eq, ← d.speed_eq] using w.packed_root
    packed_neighbor := by
      simpa only [rootNeighbor, ← d.sq_eq, ← d.speed_eq] using w.packed_neighbor }

/-- The time and bit positions in the recursive archive coincide with the indexed physical cells. -/
theorem cells_of_indexed {u : Bool} {w f : ℝ → ℝ} {h a : ℝ} {n p : ℕ}
    (each : ∀ j : Fin n, Cell u w f h (a + j / 3072) (p >>> (72 * (j : ℕ)))) :
    Cells u w f h a n p := by
  induction n generalizing a p with
  | zero => trivial
  | succ n ih =>
    refine ⟨by simpa using each 0, ih ?_⟩
    intro j
    have clock : a + ((j : ℝ) + 1) / 3072 = a + 1 / 3072 + j / 3072 := by ring
    simpa only [Fin.val_succ, Nat.cast_succ, clock, Nat.mul_succ,
      Nat.add_comm (72 * (j:ℕ)) 72, Nat.shiftRight_add] using each j.succ

/-- The positive physical clock lists the 48 cells in increasing normalized time. -/
theorem forward_cells {w f : ℝ → ℝ} {h : ℝ} {i p : ℕ}
    (each : ∀ j : Fin 48, ∀ q ∈ Set.Icc ((i:ℝ)/64) (((i:ℝ)+1)/64),
      128*q-(2*i+1:ℝ) ∈ Set.Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1) →
      w q ≤ density (p >>> (72*(j:ℕ))) / 1048576 ∧
      max (2*(h-f q)) 0 ≤ speedSq (p >>> (72*(j:ℕ))) / 67108864) :
    Cells true w f h ((i:ℝ)/64) 48 p := by
  apply cells_of_indexed
  intro j q hq
  have hj : (j:ℝ) ≤ 47 := by exact_mod_cast (show (j:ℕ) ≤ 47 by omega)
  have jl : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  have a := hq.1
  have b := hq.2
  exact each j q ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

/-- The negative physical clock reverses both the panel number and the normalized parameter. -/
theorem backward_cells {w f : ℝ → ℝ} {h : ℝ} {i p : ℕ}
    (each : ∀ j : Fin 48, ∀ q ∈ Set.Icc ((i:ℝ)/64) (((i:ℝ)+1)/64),
      128*q-(2*i+1:ℝ) ∈ Set.Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1) →
      w (-q) ≤ density (p >>> (72*(47-(j:ℕ)))) / 1048576 ∧
      max (2*(h-f (-q))) 0 ≤ speedSq (p >>> (72*(47-(j:ℕ)))) / 67108864) :
    Cells true w f h (-(((i:ℝ)+1)/64)) 48 p := by
  apply cells_of_indexed
  intro j q hq
  let k : Fin 48 := ⟨47-(j:ℕ), by omega⟩
  have xj : (j:ℕ) ≤ 47 := by omega
  have knight : (k:ℝ) = 47-(j:ℝ) := by
    change ((47-(j:ℕ):ℕ):ℝ) = _
    rw [Nat.cast_sub xj, Nat.cast_ofNat]
  have idx : 47-(k:ℕ) = j := by dsimp [k]; omega
  have hj : (j:ℝ) ≤ 47 := by exact_mod_cast xj
  have jl : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  have a := hq.1
  have b := hq.2
  have out := each k (-q) ⟨by linarith, by linarith⟩
    ⟨by rw [knight]; linarith, by rw [knight]; linarith⟩
  simpa only [MirrorActionQuadrature.Directed, ite_true, neg_neg, idx] using out

end PlasmaLean.Certificates.NativeActionInterval
