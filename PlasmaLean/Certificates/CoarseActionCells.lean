/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeLowerAction

/-! # Copying one coarse physical enclosure into consecutive chronological cells -/

@[expose] public section
namespace PlasmaLean.Certificates.NativeActionInterval
open Set MirrorActionQuadrature

def coarseTime (m k : ℕ) : Box :=
  ⟨(rational (2 * k / m - 1)).lo, (rational (2 * ((k : ℚ) + 1) / m - 1)).hi⟩

/-- Every fine cell lying in a coarse tile inherits the enclosure on its entire closed interval. -/
theorem coarse_time_mem {m copies k j : ℕ} {s : ℝ} (count : m * copies = 48)
    (first : k * copies ≤ j) (last : j + 1 ≤ (k + 1) * copies)
    (hs : s ∈ Icc (2 * (j : ℝ) / 48 - 1) (2 * ((j : ℝ) + 1) / 48 - 1)) :
    (coarseTime m k).Mem s := by
  have dn : m ≠ 0 := by rintro rfl; simp at count
  have cn : copies ≠ 0 := by rintro rfl; simp at count
  have dm : (m : ℝ) ≠ 0 := by exact_mod_cast dn
  have cp : (copies : ℝ) ≠ 0 := by exact_mod_cast cn
  have size : (48 : ℝ) = m * copies := by exact_mod_cast count.symm
  have scaled (x : ℝ) : 2*x/m = 2*(x*copies)/48 := by rw [size]; field_simp
  have low : (k : ℝ)*copies ≤ j := by exact_mod_cast first
  have high : (j : ℝ)+1 ≤ ((k : ℝ)+1)*copies := by exact_mod_cast last
  have l := (mem_rational (2 * (k : ℚ)/m-1)).1
  have u := (mem_rational (2 * ((k : ℚ)+1)/m-1)).2
  push_cast only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,
    Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast] at l u
  exact ⟨l.trans (mul_le_mul_of_nonneg_left (by rw [scaled]; linarith [hs.1]) (by norm_num)),
    (mul_le_mul_of_nonneg_left (by rw [scaled]; linarith [hs.2]) (by norm_num)).trans u⟩

/-- The same indexed physical bound feeds either orientation of either directed archive. -/
theorem directed_cells {w f : ℝ → ℝ} {h : ℝ} (upper back : Bool) {i p : ℕ}
    (each : ∀ j : Fin 48, ∀ q ∈ Icc ((i:ℝ)/64) (((i:ℝ)+1)/64),
      128*q-(2*i+1:ℝ) ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1) →
      let k := if back then 47-(j:ℕ) else (j:ℕ)
      let t := if back then -q else q
      Directed upper (w t) (density (p >>> (72*k))/1048576) ∧
        Directed upper (max (2*(h-f t)) 0) (speedSq (p >>> (72*k))/67108864)) :
    Cells upper w f h (if back then -(((i:ℝ)+1)/64) else (i:ℝ)/64) 48 p := by
  cases upper
  · exact lower_cells back each
  · cases back
    · exact forward_cells each
    · exact backward_cells each

end PlasmaLean.Certificates.NativeActionInterval
