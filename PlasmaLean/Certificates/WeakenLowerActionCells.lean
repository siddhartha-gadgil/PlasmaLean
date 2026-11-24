/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Reusing a finer lower-action certificate on a coarser chronological partition -/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorActionQuadrature

/-- Compare the two physical lower columns in each corresponding packed cell. -/
def lowerColumnsLE : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, coarse, fine =>
    (density coarse).ble (density fine) && (speedSq coarse).ble (speedSq fine) &&
      lowerColumnsLE n (coarse >>> 72) (fine >>> 72)

/-- A proved fine lower bound supplies the coarser physical cells at identical times. -/
theorem cells_of_lowerColumnsLE {n coarse fine : ℕ} {w f : ℝ → ℝ} {h a : ℝ}
    (ok : lowerColumnsLE n coarse fine = true) (physical : Cells false w f h a n fine) :
    Cells false w f h a n coarse := by
  induction n generalizing a coarse fine with
  | zero => trivial
  | succ n ih =>
    simp only [lowerColumnsLE, Bool.and_eq_true, Nat.ble_eq] at ok
    refine ⟨?_, ih ok.2 physical.2⟩
    intro t ht
    obtain ⟨dw, ds⟩ := physical.1 t ht
    change ((density coarse : ℕ) : ℝ) / 1048576 ≤ w t ∧
      ((speedSq coarse : ℕ) : ℝ) / 67108864 ≤ max (2*(h-f t)) 0
    refine ⟨le_trans ?_ dw, le_trans ?_ ds⟩
    · gcongr
      exact ok.1.1
    · gcongr
      exact ok.1.2

end PlasmaLean.Certificates.MirrorActionQuadrature
