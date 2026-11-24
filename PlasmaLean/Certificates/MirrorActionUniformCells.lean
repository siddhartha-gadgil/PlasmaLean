/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Share a physical upper bound across consecutive archived action panels -/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorActionQuadrature

/-- Both archived upper columns on each of the next records dominate the supplied ticks. -/
def floorTest (a g : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, p =>
      a.ble (density p) && g.ble (speedSq p) && floorTest a g k (p >>> 72)

/-- One physical estimate on a closed time interval can discharge every one of a
sequence of possibly different packed upper bounds on that interval. -/
theorem cells_of_floor {A G : ℕ} {w f : ℝ → ℝ} {h : ℝ} (n : ℕ) {p : ℕ} {a : ℝ}
    (check : floorTest A G n p = true)
    (bound : ∀ t ∈ Set.Icc a (a + n / 3072),
      w t ≤ A / 1048576 ∧ max (2 * (h - f t)) 0 ≤ G / 67108864) :
    Cells true w f h a n p := by
  induction n generalizing a p with
  | zero => trivial
  | succ n ih =>
    simp only [floorTest, Bool.and_eq_true] at check
    obtain ⟨⟨ca, cg⟩, tail⟩ := check
    have hd : (A : ℝ) ≤ density p := by exact_mod_cast Nat.le_of_ble_eq_true ca
    have hg : (G : ℝ) ≤ speedSq p := by exact_mod_cast Nat.le_of_ble_eq_true cg
    constructor
    · intro t ht
      have ht' : t ∈ Set.Icc a (a + (n + 1 : ℕ) / 3072) :=
        ⟨ht.1, by push_cast; linarith [ht.2, Nat.cast_nonneg (α := ℝ) n]⟩
      obtain ⟨den, speed⟩ := bound t ht'
      exact ⟨den.trans (by gcongr), speed.trans (by gcongr)⟩
    · apply ih tail
      intro t ht
      apply bound t
      refine ⟨by linarith [ht.1], ?_⟩
      push_cast
      linarith [ht.2]

end PlasmaLean.Certificates.MirrorActionQuadrature
