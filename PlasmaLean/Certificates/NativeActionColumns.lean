/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeActionInterval

/-! # From 52-bit Horner enclosures to the original directed action digits -/

@[expose] public section
namespace PlasmaLean.Certificates.NativeActionInterval
open TrajectoryTaylorModel MirrorActionQuadrature Set

structure Five (α : Type) where
  den : α
  r8 : α
  r16 : α
  u : α
  num : α

def Five.map {α β : Type} (f : α → β) (a : Five α) : Five β :=
  ⟨f a.den, f a.r8, f a.r16, f a.u, f a.num⟩

def Five.Rel {α β : Type} (P : α → β → Prop) (a : Five α) (b : Five β) : Prop :=
  P a.den b.den ∧ P a.r8 b.r8 ∧ P a.r16 b.r16 ∧ P a.u b.u ∧ P a.num b.num

/-- Outward endpoints of panel number n in the original increasing normalized parameter. -/
def timeBox (n : ℕ) : Box :=
  ⟨(rational (2 * n / 48 - 1)).lo, (rational (2 * ((n : ℚ) + 1) / 48 - 1)).hi⟩

theorem time_mem {n : ℕ} {s : ℝ}
    (hs : s ∈ Icc (2 * (n : ℝ) / 48 - 1) (2 * ((n : ℝ) + 1) / 48 - 1)) :
    (timeBox n).Mem s := by
  have l := (mem_rational (2 * (n : ℚ) / 48 - 1)).1
  have u := (mem_rational (2 * ((n : ℚ) + 1) / 48 - 1)).2
  push_cast only [Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_add,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast] at l u
  exact ⟨l.trans (mul_le_mul_of_nonneg_left hs.1 (by norm_num)),
    (mul_le_mul_of_nonneg_left hs.2 (by norm_num)).trans u⟩

theorem five_mem {s : ℝ} {t : Box} {m : Five Model} {x : Five ℝ} (ht : t.Mem s)
    (h : Five.Rel (fun p v => p.Mem s v) m x) :
    Five.Rel Box.Mem (m.map (fun p => onPanel p t)) x :=
  ⟨onPanel_mem ht h.1, onPanel_mem ht h.2.1, onPanel_mem ht h.2.2.1,
    onPanel_mem ht h.2.2.2.1, onPanel_mem ht h.2.2.2.2⟩

def ticks (upper : Bool) (b : Box) (units : ℕ) : ℤ :=
  if upper then -(-(b.hi * units) / scale) else b.lo * units / scale

theorem directed_ticks {upper : Bool} {b : Box} {x : ℝ} {units n : ℕ} (hm : b.Mem x)
    (hu : 0 < units) (h : ticks upper b units = n) :
    Directed upper x ((n : ℝ) / units) := by
  have pos : (0:ℝ) < units := by exact_mod_cast hu
  have sp : (0:ℝ) < scale := by norm_num
  cases upper with
  | false =>
    apply (div_le_iff₀ pos).mpr
    have bound := ValidatedQuadrature.fdiv_le (b.lo * units) scale (by norm_num)
    change b.lo * units / scale = n at h
    rw [h] at bound
    simp only [Int.cast_natCast, Int.cast_mul] at bound
    apply bound.trans
    rw [div_le_iff₀ sp, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_comm x] using hm.1) pos.le
  | true =>
    apply (le_div_iff₀ pos).mpr
    have bound := ValidatedQuadrature.le_cdiv (b.hi * units) scale (by norm_num)
    change -(-(b.hi * units) / scale) = n at h
    rw [h] at bound
    simp only [Int.cast_natCast, Int.cast_mul] at bound
    apply le_trans _ bound
    rw [le_div_iff₀ sp, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_comm x] using hm.2) pos.le

/-- The archived speed first divides the positive gap numerator by
R¹⁶(h+√U/R⁸), and only then multiplies by two. This order fixes the rounding. -/
def speedDen (v : Five Box) (root : Box) (h : ℚ) : Box :=
  mul v.r16 (add (rational h) (div root v.r8))

def squared (v : Five Box) (root : Box) (h : ℚ) : Box :=
  mul (rational 2) (div (clip v.num) (speedDen v root h))

/-- Complements the archived one-sided square test by checking the adjacent integer. -/
def rootNeighbor (upper : Bool) (p : ℕ) : Bool :=
  if upper then speed p == 0 || ((speed p - 1)^2).blt (speedSq p * 16384)
  else (speedSq p * 16384).blt ((speed p + 1)^2)

/-- The proposed root has exact integer lower and upper witnesses. The two
computed 52-bit bounds round to the indicated 24-bit archive digits. -/
structure Checked (upper : Bool) (v : Five Box) (root : Box) (h : ℚ) (p : ℕ) : Prop where
  root_valid : Root v.u root
  den_pos : 0 < v.den.lo
  r8_pos : 0 < v.r8.lo
  speed_den_pos : 0 < (speedDen v root h).lo
  density_tick : ticks upper (div root v.den) 1048576 = density p
  speed_tick : ticks upper (squared v root h) 67108864 = speedSq p
  packed_root : rootTest upper p = true
  packed_neighbor : rootNeighbor upper p = true

theorem Checked.sound {upper : Bool} {v : Five Box} {x : Five ℝ} {root : Box} {h : ℚ} {p : ℕ}
    (checked : Checked upper v root h p) (mem : Five.Rel Box.Mem v x) (hu : 0 ≤ x.u) :
    Directed upper (Real.sqrt x.u / x.den) (density p / 1048576) ∧
    Directed upper (2 * (max x.num 0 / (x.r16 * ((h:ℝ) + Real.sqrt x.u / x.r8))))
      (speedSq p / 67108864) := by
  have rt := checked.root_valid.mem mem.2.2.2.1 hu
  have mass := mem_div checked.den_pos rt mem.1
  have mag := mem_div checked.r8_pos rt mem.2.1
  have denom := mem_mul mem.2.2.1 (mem_add (mem_rational h) mag)
  have val := mem_div (b := speedDen v root h) checked.speed_den_pos (mem_clip mem.2.2.2.2) denom
  have sp := mem_mul (mem_rational 2) val
  exact ⟨directed_ticks mass (by norm_num) checked.density_tick,
    by simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
      directed_ticks sp (by norm_num) checked.speed_tick⟩

end PlasmaLean.Certificates.NativeActionInterval
