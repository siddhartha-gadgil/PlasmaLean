/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeActionArchivePair

/-! # Lower physical action rectangles in chronological order -/

@[expose] public section
namespace PlasmaLean.Certificates.NativeActionInterval
open Set MirrorActionQuadrature

/-- Physical observations along either clock give the corresponding chronological
lower cells. The negative clock reverses both the time coordinate and the packed bits. -/
theorem lower_cells {w f : ℝ → ℝ} {h : ℝ} (back : Bool) {i p : ℕ}
    (each : ∀ j : Fin 48, ∀ q ∈ Icc ((i:ℝ)/64) (((i:ℝ)+1)/64),
      128*q-(2*i+1:ℝ) ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1) →
      let k := if back then 47-(j:ℕ) else (j:ℕ)
      let t := if back then -q else q
      (density (p >>> (72*k)) : ℝ)/1048576 ≤ w t ∧
        (speedSq (p >>> (72*k)) : ℝ)/67108864 ≤ max (2*(h-f t)) 0) :
    Cells false w f h (if back then -(((i:ℝ)+1)/64) else (i:ℝ)/64) 48 p := by
  apply cells_of_indexed
  intro j q hq
  have xj : (j:ℕ) ≤ 47 := by omega
  have hj : (j:ℝ) ≤ 47 := by exact_mod_cast xj
  have jl : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  cases back
  · change q ∈ Icc _ _ at hq
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    exact each j q ⟨by linarith [hq.1],by linarith [hq.2]⟩ ⟨by linarith [hq.1],by linarith [hq.2]⟩
  · let k : Fin 48 := ⟨47-(j:ℕ), by omega⟩
    have kt : (k:ℝ) = 47-(j:ℝ) := by
      change ((47-(j:ℕ):ℕ):ℝ) = _
      rw [Nat.cast_sub xj, Nat.cast_ofNat]
    have idx : 47-(k:ℕ) = j := by dsimp [k]; omega
    simp only [↓reduceIte] at hq
    have out := each k (-q) ⟨by linarith [hq.1,hq.2],by linarith [hq.1,hq.2]⟩
      ⟨by rw [kt]; linarith [hq.2], by rw [kt]; linarith [hq.1]⟩
    simpa only [MirrorActionQuadrature.Directed, Bool.false_eq_true, ↓reduceIte, neg_neg,
      idx] using out

/-- A lower cover proves the exact rectangle sum as a closed lower bound. -/
theorem exact_lower_mass {bs : List (Block false)} {l r : ℕ} (len : bs.length = l + r)
    {f w : ℝ → ℝ} {h : ℝ} (cells : Covers false w f h (-(l : ℝ) / 64) bs)
    (hn : ∀ t ∈ Icc (-(l : ℝ) / 64) (r / 64), 0 ≤ w t)
    (cf : ContinuousOn f (Icc (-(l : ℝ) / 64) (r / 64)))
    (cw : ContinuousOn w (Icc (-(l : ℝ) / 64) (r / 64))) :
    total bs / (3072*1099511627776 : ℝ) ≤ Kinetic.MirrorHeightAction.action f w
      (-(l:ℝ)/64) (r/64) h := by
  by_contra! bad
  obtain ⟨q,low,high⟩ := exists_rat_btwn bad
  have order : -(l:ℝ)/64 ≤ (r:ℝ)/64 := by
    linarith only [Nat.cast_nonneg (α := ℝ) l,Nat.cast_nonneg (α := ℝ) r]
  have a : 0 ≤ Kinetic.MirrorHeightAction.action f w (-(l:ℝ)/64) (r/64) h :=
    intervalIntegral.integral_nonneg order (fun t ht => mul_nonneg (hn t ht) (Real.sqrt_nonneg _))
  have qpos : (0:ℝ) ≤ q := a.trans low.le
  have nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast qpos)
  have cast : (q:ℝ) = q.num.toNat/(q.den:ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg nonneg).symm
  rw [cast] at low high
  have positive : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
  have cross := (div_lt_div_iff₀ positive (by norm_num : (0:ℝ) < 3072*1099511627776)).mp high
  have p : Packet false bs l r q.num.toNat q.den := by
    refine ⟨len, ?_⟩
    change q.num.toNat * 3072 * 1099511627776 < total bs * q.den
    rw [mul_assoc]
    exact_mod_cast cross
  exact lt_asymm low (p.sound q.den_pos cells hn cf cw)

end PlasmaLean.Certificates.NativeActionInterval
