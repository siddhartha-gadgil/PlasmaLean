/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.TrajectoryHarmonicPacket

/-!
# Signed harmonic clocks at both physical launch sections

The opposite-section field tables multiply harmonic `k` by `(-1)^k`.
The unchanged trajectory packet encloses precisely the corresponding signed
component of the shifted physical clock. The final slab includes its right endpoint.
-/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryHarmonicPacket

open TrajectoryTrig

/-- Starting at either actual azimuth gives the clock component used by the
corresponding Fourier coefficient table. -/
theorem physical_section {i : ℕ} (p : Packet i) (opposite back : Bool) (k : Fin 3)
    (sine : Bool) {t : ℝ} (ht : t ∈ Set.Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64)) :
    ((p back k).model sine).Mem (128*t-(2*i+1 : ℝ))
      ((if opposite then (-1 : ℝ)^(k.val+1) else 1) * wave sine (2*((k.val : ℝ)+1)*
        ((if opposite then Real.pi/2 else 0) + (if back then -t else t)))) := by
  have h := physical p back k sine ht
  cases opposite
  · simpa using h
  · simp only [ite_true]
    rw [← Nat.cast_add_one, opposite_section, ← mul_assoc, ← mul_pow]
    simpa only [neg_one_mul, neg_neg, one_pow, one_mul, Nat.cast_add_one] using h

/-- Every outward time through the final cap belongs to at least one closed slab.
The integer index is shared by both directions and all harmonics. -/
theorem time_covered {t : ℝ} (ht : t ∈ Set.Icc 0 (391 / 64 : ℝ)) :
    ∃ i : Fin 391, t ∈ Set.Icc ((i.val : ℝ) / 64) (((i.val : ℝ) + 1) / 64) := by
  rcases ht.2.eq_or_lt with final | before
  · subst t
    exact ⟨390, by norm_num⟩
  · have hn : 0 ≤ 64*t := mul_nonneg (by norm_num) ht.1
    have bound : ⌊64*t⌋₊ < 391 := (Nat.floor_lt hn).mpr (by norm_num; linarith)
    refine ⟨⟨_, bound⟩, ?_⟩
    constructor
    · change (⌊64*t⌋₊ : ℝ) / 64 ≤ t
      linarith [Nat.floor_le hn]
    · change t ≤ ((⌊64*t⌋₊ : ℝ) + 1) / 64
      linarith [Nat.lt_floor_add_one (64*t)]

end PlasmaLean.Certificates.TrajectoryHarmonicPacket
