/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.TrajectoryTrig
public import PlasmaLean.Certificates.DyadicTaylorModel
public import PlasmaLean.Certificates.KernelFact

/-!
# Harmonic packets for the 1/64-radian field-line slabs

Each packet checks the original sine and cosine Taylor models against
independently enclosed centre values. The trigonometric functions are evaluated
on the signed physical clock. Every subinterval is closed, so adjacent packets
both apply at their common time.
-/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryHarmonicPacket

open QPoly TrajectoryTrig TrajectoryTaylorModel

/-- A 96-bit midpoint for one trigonometric component, checked by its scalar Taylor remainder. -/
structure Centre (sine : Bool) (a : ℚ) where
  numerator : ℤ
  degree : ℕ
  checked : |a| ^ (degree+1) / (degree+1).factorial +
    |evalQ (poly sine degree) a - numerator / 2^96| ≤ 1/2^95

/-- Physical uncertainty at the independently approximated centre of the clock. -/
theorem Centre.error {sine : Bool} {a : ℚ} (c : Centre sine a) :
    |wave sine (a : ℝ) - ((c.numerator / 2^96 : ℚ) : ℝ)| ≤ ((1 / 2 ^ 95 : ℚ) : ℝ) :=
  centre_error sine c.degree a _ _ c.checked

/-- The coefficient and error check for one emitted 80-bit sine or cosine polynomial. -/
def Fits {a : ℚ} (w : ℚ) (c : Centre false a) (z : Centre true a)
    (sine : Bool) (m : Model) : Prop :=
  let ref := rotated sine (constant (c.numerator / 2^96) (1/2^95))
    (constant (z.numerator / 2^96) (1/2^95)) 9 w
  ref.radius + magnitude (difference ref.poly m.poly) ≤ m.radius

/-- Sine and cosine data at one harmonic and trace direction. -/
structure Pair (a w : ℚ) where
  cosCentre : Centre false a
  sinCentre : Centre true a
  cosModel : Model
  sinModel : Model
  cosChecked : Fits w cosCentre sinCentre false cosModel
  sinChecked : Fits w cosCentre sinCentre true sinModel

/-- Select the Taylor model used for this actual harmonic component. -/
def Pair.model {a w : ℚ} (p : Pair a w) (sine : Bool) : Model :=
  if sine then p.sinModel else p.cosModel

/-- Soundness of both components throughout the normalized time interval. -/
theorem Pair.sound {a w : ℚ} (p : Pair a w) (sine : Bool) {s : ℝ} (hs : |s| ≤ 1) :
    (p.model sine).Mem s (wave sine ((a : ℝ) + w*s)) := by
  cases sine
  · exact fit_at_centre false 9 w p.cosCentre.error p.sinCentre.error _ p.cosChecked hs
  · exact fit_at_centre true 9 w p.cosCentre.error p.sinCentre.error _ p.sinChecked hs

/-- The three positive harmonic numbers, signed by the traversal direction. -/
def frequency (back : Bool) (k : Fin 3) : ℚ :=
  if back then -(k.val+1 : ℚ) else k.val+1

/-- All six harmonic pairs at the specified outward time-slab index. -/
abbrev Packet (i : ℕ) :=
  (back : Bool) → (k : Fin 3) →
    Pair ((2*i+1 : ℚ)*frequency back k/64) (frequency back k/64)

/-- The recorded order-seven model holds for the named harmonic on every real physical
time of the closed slab, in either trace direction. -/
theorem physical {i : ℕ} (p : Packet i) (back : Bool) (k : Fin 3) (sine : Bool) {t : ℝ}
    (ht : t ∈ Set.Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64)) :
    ((p back k).model sine).Mem (128*t-(2*i+1 : ℝ))
      (wave sine (2*((k.val : ℝ)+1)*(if back then -t else t))) := by
  have hs : |128*t-(2*i+1 : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := (p back k).sound sine hs
  convert h using 2
  cases back <;> simp [frequency] <;> ring

end PlasmaLean.Certificates.TrajectoryHarmonicPacket
