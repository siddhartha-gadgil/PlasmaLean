/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.RadialTile

/-!
# Tangent propagation and observable bounds on radial trace slabs

One record contains the transformed jump, final radius, defect, frame norm,
physical error radius, bounds on the four observables, crossing slope and
logarithmic norm. Each trajectory and its tangent share a 1/64-radian grid.
The operative differential inequalities and the enclosure of the physical
fields in a slab's primitive intervals are separate analytic inputs.
-/

@[expose] public section

namespace PlasmaLean.Certificates.RadialSlabs

/-- Unsigned bounds, with `db` denoting the magnitude of the negative strength derivative. -/
structure Ranges where
  bl : ℕ
  bh : ℕ
  al : ℕ
  ah : ℕ
  dbl : ℕ
  dbh : ℕ
  dal : ℕ
  dah : ℕ

/-- One half trace's directed extrema and maximal errors, in units of 2⁻⁸⁰. -/
structure Envelope extends Ranges where
  core : ℕ
  cap : ℕ
  orientation : ℕ
  maxDefect : ℕ
  maxError : ℕ

/-- Each field up to and including the mirror slope occupies 96 bits. -/
def word (p i : ℕ) : ℕ := (p >>> (96*i)) % (2^96)

/-- Slab log norm upper bound has 128 fractional bits. -/
def growth (p : ℕ) : ℕ := (p >>> 1344) % (2^128)

/-- The four squared observable/derivative intervals on one slab. -/
def ranges (p : ℕ) : Ranges := ⟨word p 5, word p 6, word p 7, word p 8,
  word p 9, word p 10, word p 11, word p 12⟩

/-- Each four-quantity enclosure is ordered and contained in the summary. -/
def contained (r s : Ranges) : Bool :=
  s.bl.ble r.bl && r.bl.ble r.bh && r.bh.ble s.bh &&
  s.al.ble r.al && r.al.ble r.ah && r.ah.ble s.ah &&
  s.dbl.ble r.dbl && r.dbl.ble r.dbh && r.dbh.ble s.dbh &&
  s.dal.ble r.dal && r.dal.ble r.dah && r.dah.ble s.dah

/-- The original rational heights multiplied by their common denominator. -/
def heightDen : ℕ := 5000000000000000

/-- Every slab meeting the height band must carry an outward derivative bound. -/
def oriented (e : Envelope) (p : ℕ) : Bool :=
  ((ranges p).bh * heightDen^2).blt (5297961656084411^2 * 2^80) ||
  (5300546391395933^2 * 2^80).blt ((ranges p).bl * heightDen^2) ||
  e.orientation.ble (word p 13)

/-- Division-free scalar tangent recurrence, frame conversion and recorded maxima. -/
def tangent (e : Envelope) (incoming p : ℕ) : Bool :=
  (growth p).blt (64*2^128) &&
  (((incoming + word p 0)*64 + word p 2)*2^128).ble
    (word p 1 * (64 * 2^128 - growth p)) &&
  (word p 3 * word p 1).ble (word p 4 * 2^40) &&
  (word p 2).ble e.maxDefect && (word p 4).ble e.maxError

/-- Steps 0 through 63 cover the accessible core. The last step contains 61/10. -/
def test (e : Envelope) (i incoming p : ℕ) : Bool :=
  tangent e incoming p && contained (ranges p) e.toRanges &&
  ((64).ble i || (ranges p).bh.ble e.core) &&
  (i != 390 || e.cap.ble (ranges p).bl) && oriented e p

/-- Replay one short digit block, checking its start index and inherited radius. -/
def replay (e : Envelope) : ℕ → ℕ → ℕ → ℕ → Bool × ℕ
  | 0, _, incoming, p => (p == 0, incoming)
  | n+1, i, incoming, p =>
    let rest := replay e n (i+1) (word p 1) (p >>> 1472)
    (test e i incoming p && rest.1, rest.2)

/-- The chain constructor glues both index and radius, including across block boundaries. -/
inductive Chain (e : Envelope) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Prop
  | nil (i s) : Chain e i s i s []
  | cons (n p i s out) {k last rest} (ok : replay e n i s p = (true, out))
      (tail : Chain e (i+n) out k last rest) : Chain e i s k last ((n,p)::rest)

/-- Each propagated tube obeys the exact rational upper bound after its jump and forcing. -/
theorem tangent_bound {e : Envelope} {i s p : ℕ} (checked : test e i s p = true) :
    (growth p : ℝ) < 64 * 2^128 ∧
      (((s : ℝ) + word p 0) + (word p 2 : ℝ)/64) /
        (1 - (growth p : ℝ)/(64*2^128)) ≤ word p 1 ∧
      (word p 3 : ℝ) * word p 1 / 2^40 ≤ word p 4 := by
  simp only [test, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩ := checked
  simp only [tangent, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨hg, hr⟩, hp⟩, _⟩, _⟩ := h
  have g : (growth p : ℝ) < 64 * 2^128 := by exact_mod_cast hg
  have r := Nat.cast_le (α := ℝ).mpr hr
  simp only [Nat.cast_mul, Nat.cast_sub hg.le] at r
  push_cast at r
  refine ⟨g, (div_le_iff₀ (by linarith : 0 < 1-(growth p : ℝ)/(64*2^128))).mpr ?_, ?_⟩
  · linarith only [r]
  · apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast hp

/-- Slab tests available without any assumptions about numerical proposals. -/
def Each (e : Envelope) : ℕ → ℕ → ℕ → ℕ → Prop
  | 0, _, _, _ => True
  | n+1, i, s, p => test e i s p = true ∧ Each e n (i+1) (word p 1) (p >>> 1472)

theorem replay_each {e : Envelope} {n i s p out : ℕ} (h : replay e n i s p = (true, out)) :
    Each e n i s p := by
  induction n generalizing i s p with
  | zero => trivial
  | succ n ih =>
    have accepted := congrArg Prod.fst h
    change (_ && _) = true at accepted
    obtain ⟨ok, tail⟩ := Bool.and_eq_true_iff.mp accepted
    have last := congrArg Prod.snd h
    exact ⟨ok, ih (Prod.ext tail last)⟩

/-- The step conclusions in every consecutive block, carrying the checked radii ahead. -/
def All (e : Envelope) (i s : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (n,p)::rest => Each e n i s p ∧ All e (i+n) (replay e n i s p).2 rest

theorem Chain.sound {e : Envelope} {i s k last : ℕ} {blocks : List (ℕ × ℕ)}
    (h : Chain e i s k last blocks) : All e i s blocks := by
  induction h with
  | nil => trivial
  | cons n p i s out ok _ ih =>
    exact ⟨replay_each ok, by simpa only [ok] using ih⟩

/-- Exact link from the dyadic output extrema to the real radial action certificate. -/
def Envelope.Matches (e : Envelope) (d : RadialTile.Half) : Prop :=
  (d.bLow = e.bl / (2:ℝ)^80 ∧ d.bHigh = e.bh / (2:ℝ)^80) ∧
  (d.aLow = e.al / (2:ℝ)^80 ∧ d.aHigh = e.ah / (2:ℝ)^80) ∧
  (d.dbLow = -(e.dbh : ℝ) / 2^80 ∧ d.dbHigh = -(e.dbl : ℝ) / 2^80) ∧
  (d.daLow = e.dal / (2:ℝ)^80 ∧ d.daHigh = e.dah / (2:ℝ)^80) ∧
  d.coreUpper = e.core / (2:ℝ)^80 ∧ d.capLower = e.cap / (2:ℝ)^80 ∧
  d.outward = e.orientation / (2:ℝ)^80

end PlasmaLean.Certificates.RadialSlabs
