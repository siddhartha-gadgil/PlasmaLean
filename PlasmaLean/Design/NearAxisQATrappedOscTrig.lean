/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Fixed-point enclosures of `cos` and `sin` (for the oscillatory bounce integrals)

Companion to `Design/NearAxisQATrappedOscCells`. The fixed-point enclosures `FIv` of
`Certificates/ValidatedQuadrature` (endpoints `lo/2³²`, `hi/2³²`, validity flag `ok`) are
extended by a joint enclosure `cosSinI Φ` of `(cos z, sin z)` for every `z ∈ Φ`.

**Method.** Scale `y = z / 2¹⁰`. If `|y| ≤ 1`, Mathlib's `Real.cos_bound` and `Real.sin_bound`
give `cos y ∈ 1 − y²/2 ± |y|⁴ · 5/96` and `sin y ∈ y − y³/6 ± |y|⁵/100`. Then ten doublings
`cos 2y = 2cos²y − 1 = 1 − 2sin²y` (both forms, intersected) and `sin 2y = 2 sin y cos y`,
each clamped to `[−1, 1]`, recover `(cos z, sin z)`. All operations are interval operations on
scaled integers (`decide +kernel` friendly). An invalid enclosure contains every real number, so
the soundness lemma `mem_cosSinI` is unconditional; validity requires `|z| ≤ 1024`.

Accuracy: for `|z| ≤ 16` and a thin input the output width is about `10⁻⁵` (the remainder is
`≤ 10⁻⁹` before doubling); for an input of width `w` the width is about `w` (the derivative).

Sanity fixtures: `fixture_cos_zero` (degenerate case `cos 0 = 1`), `fixture_cos_pi_third`
(accepted: `cos(1.0471975512) ∈ [0.49999, 0.50001]`), `fixture_cosSin_rejected` (an input of size
`2000` is rejected).
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.NearAxisQATrappedCells
  FIvX Real

/-- Intersection of two enclosures of the same number. -/
@[expose] def meetI (I J : FIv) : FIv := ⟨max I.lo J.lo, min I.hi J.hi, I.ok && J.ok⟩

/-- Soundness of `meetI`. -/
theorem mem_meetI {I J : FIv} {x : ℝ} (hI : I.Mem x) (hJ : J.Mem x) : (meetI I J).Mem x := by
  intro hok
  simp only [meetI, Bool.and_eq_true] at hok
  obtain ⟨a1, a2⟩ := hI hok.1
  obtain ⟨b1, b2⟩ := hJ hok.2
  simp only [meetI, fxVal] at a1 a2 b1 b2 ⊢
  have hS := fxScale_pos
  constructor
  · rcases le_total I.lo J.lo with h | h
    · rw [max_eq_right h]; exact b1
    · rw [max_eq_left h]; exact a1
  · rcases le_total I.hi J.hi with h | h
    · rw [min_eq_left h]; exact a2
    · rw [min_eq_right h]; exact b2

/-- The unit enclosure `[−1, 1]`. -/
@[expose] def unitI : FIv := ⟨-fxScale, fxScale, true⟩

/-- Every number of absolute value at most `1` is in `unitI`. -/
theorem mem_unitI {x : ℝ} (h : |x| ≤ 1) : unitI.Mem x := by
  intro _
  have hS := fxScale_pos
  simp only [unitI, fxVal]
  push_cast
  rw [neg_div, div_self hS.ne']
  exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- The symmetric enclosure `[−r, r]` of every error bounded by a number of `R` (validity of
`R` is inherited). -/
@[expose] def pmI (R : FIv) : FIv := ⟨-R.hi, R.hi, R.ok⟩

/-- If `|e| ≤ r` and `r ∈ R` then `e ∈ pmI R`. -/
theorem mem_pmI {R : FIv} {e r : ℝ} (hR : R.Mem r) (he : |e| ≤ r) : (pmI R).Mem e := by
  intro hok
  obtain ⟨_, h2⟩ := hR hok
  simp only [pmI, fxVal] at h2 ⊢
  push_cast
  rw [neg_div]
  exact ⟨by linarith [neg_abs_le e], by linarith [le_abs_self e]⟩

/-- The magnitude enclosure `[0, max(−lo, hi)]` of `|y|` (validity inherited). -/
@[expose] def magI (I : FIv) : FIv := ⟨0, max (-I.lo) I.hi, I.ok⟩

/-- Soundness of `magI`. -/
theorem mem_magI {I : FIv} {y : ℝ} (h : I.Mem y) : (magI I).Mem |y| := by
  intro hok
  obtain ⟨h1, h2⟩ := h hok
  have hS := fxScale_pos
  simp only [magI, fxVal] at h1 h2 ⊢
  refine ⟨by rw [Int.cast_zero, zero_div]; exact abs_nonneg y, ?_⟩
  have hm1 : ((-I.lo : ℤ) : ℝ) ≤ ((max (-I.lo) I.hi : ℤ) : ℝ) := by
    exact_mod_cast le_max_left (-I.lo) I.hi
  have hm2 : ((I.hi : ℤ) : ℝ) ≤ ((max (-I.lo) I.hi : ℤ) : ℝ) := by
    exact_mod_cast le_max_right (-I.lo) I.hi
  rw [Int.cast_neg] at hm1
  rw [div_le_iff₀ hS] at h1
  rw [le_div_iff₀ hS] at h2 ⊢
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; linarith
  · rw [abs_of_nonpos hy]; linarith

/-- Validity condition of the Taylor step: `Y` valid and `|y| ≤ 1` on `Y`. -/
@[expose] def okT (Y : FIv) : Bool := Y.ok && decide (max (-Y.lo) Y.hi ≤ fxScale)

/-- Under `okT Y`, every `y ∈ Y` has `|y| ≤ 1`. -/
theorem abs_le_one_of_okT {Y : FIv} {y : ℝ} (hY : Y.Mem y) (h : okT Y = true) : |y| ≤ 1 := by
  simp only [okT, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hb⟩ := mem_magI hY h.1
  simp only [magI, fxVal] at hb
  have : ((max (-Y.lo) Y.hi : ℤ) : ℝ) ≤ fxScale := by exact_mod_cast h.2
  exact hb.trans (by rw [div_le_one fxScale_pos]; exact this)

/-- Polynomial part and remainder of the cosine Taylor step. -/
@[expose] def taylorC (Y : FIv) : FIv :=
  ((C 1 1).sub ((C 1 2).mul Y.sq)).add (pmI ((magI Y).sq.sq.mul (C 5 96)))

/-- Polynomial part and remainder of the sine Taylor step. -/
@[expose] def taylorS (Y : FIv) : FIv :=
  (Y.sub ((C 1 6).mul (Y.mul Y.sq))).add (pmI (((magI Y).sq.sq.mul (magI Y)).mul (C 1 100)))

/-- Taylor step: enclosures of `(cos y, sin y)` for `y ∈ Y`, valid when `|y| ≤ 1` on `Y`. -/
@[expose] def taylorCS (Y : FIv) : FIv × FIv :=
  (⟨(taylorC Y).lo, (taylorC Y).hi, (taylorC Y).ok && okT Y⟩,
    ⟨(taylorS Y).lo, (taylorS Y).hi, (taylorS Y).ok && okT Y⟩)

/-- Soundness of the Taylor step. -/
theorem mem_taylorCS {Y : FIv} {y : ℝ} (hY : Y.Mem y) :
    (taylorCS Y).1.Mem (cos y) ∧ (taylorCS Y).2.Mem (sin y) := by
  have hM := mem_magI hY
  have h1 : (C 1 1).Mem 1 := mem_C (by norm_num)
  have h2 : (C 1 2).Mem (1 / 2) := mem_C (by norm_num)
  have h6 : (C 1 6).Mem (1 / 6) := mem_C (by norm_num)
  have h96 : (C 5 96).Mem (5 / 96) := mem_C (by norm_num)
  have h100 : (C 1 100).Mem (1 / 100) := mem_C (by norm_num)
  have hR4 : ((magI Y).sq.sq.mul (C 5 96)).Mem (|y| ^ 4 * (5 / 96)) := by
    have := FIv.mem_mul (FIv.mem_sq (FIv.mem_sq hM)) h96
    rwa [← pow_mul] at this
  have hR5 : (((magI Y).sq.sq.mul (magI Y)).mul (C 1 100)).Mem (|y| ^ 5 / 100) := by
    have := FIv.mem_mul (FIv.mem_mul (FIv.mem_sq (FIv.mem_sq hM)) hM) h100
    rw [← pow_mul, ← pow_succ] at this
    rwa [div_eq_mul_one_div]
  constructor
  · intro hok
    simp only [taylorCS, Bool.and_eq_true] at hok
    have hy1 := abs_le_one_of_okT hY hok.2
    have hp : ((C 1 1).sub ((C 1 2).mul Y.sq)).Mem (1 - 1 / 2 * y ^ 2) :=
      FIv.mem_sub h1 (FIv.mem_mul h2 (FIv.mem_sq hY))
    have he := mem_pmI hR4 (e := cos y - (1 - y ^ 2 / 2)) (cos_bound hy1)
    have hsum := FIv.mem_add hp he
    have e : 1 - 1 / 2 * y ^ 2 + (cos y - (1 - y ^ 2 / 2)) = cos y := by ring
    rw [e] at hsum
    exact hsum hok.1
  · intro hok
    simp only [taylorCS, Bool.and_eq_true] at hok
    have hy1 := abs_le_one_of_okT hY hok.2
    have hp : (Y.sub ((C 1 6).mul (Y.mul Y.sq))).Mem (y - 1 / 6 * (y * y ^ 2)) :=
      FIv.mem_sub hY (FIv.mem_mul h6 (FIv.mem_mul hY (FIv.mem_sq hY)))
    have he := mem_pmI hR5 (e := sin y - (y - y ^ 3 / 6)) (sin_bound hy1)
    have hsum := FIv.mem_add hp he
    have e : y - 1 / 6 * (y * y ^ 2) + (sin y - (y - y ^ 3 / 6)) = sin y := by ring
    rw [e] at hsum
    exact hsum hok.1

/-- One doubling step `(cos y, sin y) ↦ (cos 2y, sin 2y)`. -/
@[expose] def dblCS (p : FIv × FIv) : FIv × FIv :=
  (meetI unitI (meetI (((C 2 1).mul p.1.sq).sub (C 1 1)) ((C 1 1).sub ((C 2 1).mul p.2.sq))),
    meetI unitI ((C 2 1).mul (p.2.mul p.1)))

/-- Soundness of a doubling step. -/
theorem mem_dblCS {p : FIv × FIv} {y : ℝ} (hc : p.1.Mem (cos y)) (hs : p.2.Mem (sin y)) :
    (dblCS p).1.Mem (cos (2 * y)) ∧ (dblCS p).2.Mem (sin (2 * y)) := by
  have h1 : (C 1 1).Mem 1 := mem_C (by norm_num)
  have h2 : (C 2 1).Mem 2 := mem_C (by norm_num)
  refine ⟨mem_meetI (mem_unitI (abs_cos_le_one _)) (mem_meetI ?_ ?_),
    mem_meetI (mem_unitI (abs_sin_le_one _)) ?_⟩
  · rw [cos_two_mul]; exact FIv.mem_sub (FIv.mem_mul h2 (FIv.mem_sq hc)) h1
  · rw [cos_two_mul, cos_sq']
    have := FIv.mem_sub h1 (FIv.mem_mul h2 (FIv.mem_sq hs))
    convert this using 1; ring
  · rw [sin_two_mul]
    have := FIv.mem_mul h2 (FIv.mem_mul hs hc)
    convert this using 1; ring

/-- `n` doublings. -/
@[expose] def dblN : ℕ → FIv × FIv → FIv × FIv
  | 0, p => p
  | n + 1, p => dblN n (dblCS p)

/-- Soundness of `n` doublings: from `(cos y, sin y)` to `(cos (2ⁿ y), sin (2ⁿ y))`. -/
theorem mem_dblN (n : ℕ) {p : FIv × FIv} {y : ℝ} (hc : p.1.Mem (cos y)) (hs : p.2.Mem (sin y)) :
    (dblN n p).1.Mem (cos (2 ^ n * y)) ∧ (dblN n p).2.Mem (sin (2 ^ n * y)) := by
  induction n generalizing p y with
  | zero => simpa [dblN] using ⟨hc, hs⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := mem_dblCS hc hs
    have := ih h1 h2
    simp only [dblN]
    rwa [show (2 : ℝ) ^ (n + 1) * y = 2 ^ n * (2 * y) by ring]

/-- **Joint enclosure of `(cos z, sin z)`** for `z ∈ Φ` (valid when `|z| ≤ 1024` on `Φ`). -/
@[expose] def cosSinI (Φ : FIv) : FIv × FIv := dblN 10 (taylorCS (Φ.mul (C 1 1024)))

/-- **Soundness of `cosSinI`.** -/
theorem mem_cosSinI {Φ : FIv} {z : ℝ} (h : Φ.Mem z) :
    (cosSinI Φ).1.Mem (cos z) ∧ (cosSinI Φ).2.Mem (sin z) := by
  have hY : (Φ.mul (C 1 1024)).Mem (z * (1 / 1024)) := FIv.mem_mul h (mem_C (by norm_num))
  obtain ⟨hc, hs⟩ := mem_taylorCS hY
  have := mem_dblN 10 hc hs
  rwa [show (2 : ℝ) ^ 10 * (z * (1 / 1024)) = z by ring] at this

/-! ## Quadrant reduction -/

/-- Enclosure of `π/2`. -/
@[expose] def halfPiI : FIv := ⟨6746518852, 6746518853, true⟩

/-- Soundness of `halfPiI` (Mathlib's 20-digit bounds on `π`). -/
theorem mem_halfPiI : halfPiI.Mem (π / 2) := by
  intro _
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  simp only [halfPiI, fxVal, fxScale]
  constructor
  · rw [div_le_iff₀ (by norm_num)]; push_cast; linarith
  · rw [le_div_iff₀ (by norm_num)]; push_cast; linarith

/-- One doubling step `(cos y, sin y) ↦ (1 − 2 sin²y, 2 sin y cos y)`. -/
@[expose] def dblQ (p : FIv × FIv) : FIv × FIv :=
  ((C 1 1).sub ((C 2 1).mul p.2.sq), (C 2 1).mul (p.2.mul p.1))

/-- Soundness of `dblQ`. -/
theorem mem_dblQ {p : FIv × FIv} {y : ℝ} (hc : p.1.Mem (cos y)) (hs : p.2.Mem (sin y)) :
    (dblQ p).1.Mem (cos (2 * y)) ∧ (dblQ p).2.Mem (sin (2 * y)) := by
  have h1 : (C 1 1).Mem 1 := mem_C (by norm_num)
  have h2 : (C 2 1).Mem 2 := mem_C (by norm_num)
  constructor
  · simp only [dblQ]
    rw [cos_two_mul, cos_sq', show 2 * (1 - sin y ^ 2) - 1 = 1 - 2 * sin y ^ 2 by ring]
    exact FIv.mem_sub h1 (FIv.mem_mul h2 (FIv.mem_sq hs))
  · simp only [dblQ]
    rw [sin_two_mul, mul_assoc]
    exact FIv.mem_mul h2 (FIv.mem_mul hs hc)

/-- Four doublings. -/
@[expose] def dbl4 (p : FIv × FIv) : FIv × FIv := dblQ (dblQ (dblQ (dblQ p)))

/-- Soundness of `dbl4`. -/
theorem mem_dbl4 {p : FIv × FIv} {y : ℝ} (hc : p.1.Mem (cos y)) (hs : p.2.Mem (sin y)) :
    (dbl4 p).1.Mem (cos (16 * y)) ∧ (dbl4 p).2.Mem (sin (16 * y)) := by
  obtain ⟨a1, b1⟩ := mem_dblQ hc hs
  obtain ⟨a2, b2⟩ := mem_dblQ a1 b1
  obtain ⟨a3, b3⟩ := mem_dblQ a2 b2
  obtain ⟨a4, b4⟩ := mem_dblQ a3 b3
  rw [show (16 : ℝ) * y = 2 * (2 * (2 * (2 * y))) by ring]
  exact ⟨a4, b4⟩

/-- Rotation by `r` quarter turns: `(cos (y + rπ/2), sin (y + rπ/2))` from `(cos y, sin y)`. -/
@[expose] def rotQ (r : ℤ) (p : FIv × FIv) : FIv × FIv :=
  if r = 0 then p else if r = 1 then (p.2.neg, p.1) else if r = 2 then (p.1.neg, p.2.neg)
  else (p.2, p.1.neg)

/-- Soundness of `rotQ` (for `r = q mod 4`). -/
theorem mem_rotQ {p : FIv × FIv} {y : ℝ} (q : ℤ) (hc : p.1.Mem (cos y)) (hs : p.2.Mem (sin y)) :
    (rotQ (q % 4) p).1.Mem (cos (y + q * (π / 2))) ∧
      (rotQ (q % 4) p).2.Mem (sin (y + q * (π / 2))) := by
  have hq : (q : ℝ) = (q % 4 : ℤ) + ((q / 4 : ℤ) : ℝ) * 4 := by
    have := Int.emod_add_mul_ediv q 4
    have h' : ((q % 4 + 4 * (q / 4) : ℤ) : ℝ) = (q : ℝ) := by rw [this]
    push_cast at h' ⊢; linarith
  have e : y + q * (π / 2) = (y + ((q % 4 : ℤ) : ℝ) * (π / 2)) + ((q / 4 : ℤ) : ℝ) * (2 * π) := by
    rw [hq]; ring
  rw [e, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]
  have h0 : 0 ≤ q % 4 := Int.emod_nonneg q (by norm_num)
  have h4 : q % 4 < 4 := Int.emod_lt_of_pos q (by norm_num)
  have hcases : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h] <;> simp only [rotQ] <;> norm_num
  · exact ⟨hc, hs⟩
  · rw [cos_add_pi_div_two, sin_add_pi_div_two]; exact ⟨FIv.mem_neg hs, hc⟩
  · rw [show y + 2 * (π / 2) = y + π by ring, cos_add_pi, sin_add_pi]
    exact ⟨FIv.mem_neg hc, FIv.mem_neg hs⟩
  · rw [show y + 3 * (π / 2) = (y + π) + π / 2 by ring, cos_add_pi_div_two, sin_add_pi_div_two,
      sin_add_pi, cos_add_pi, neg_neg]
    exact ⟨hs, FIv.mem_neg hc⟩

/-- **Joint enclosure of `(cos m, sin m)` at a thin point** `m = n/2³²`, by quadrant reduction
`m = y + q π/2` (`q` rounded), the Taylor step at `y/16` and four doublings. -/
@[expose] def cosSinQ (n : ℤ) : FIv × FIv :=
  let q : ℤ := (2 * n + 6746518852) / (2 * 6746518852)
  rotQ (q % 4) (dbl4 (taylorCS (((⟨n, n, true⟩ : FIv).sub ((FIv.ofInt q).mul halfPiI)).mul
    (C 1 16))))

/-- Soundness of `cosSinQ`. -/
theorem mem_cosSinQ (n : ℤ) :
    (cosSinQ n).1.Mem (cos (fxVal n)) ∧ (cosSinQ n).2.Mem (sin (fxVal n)) := by
  set q : ℤ := (2 * n + 6746518852) / (2 * 6746518852)
  have hY : (((⟨n, n, true⟩ : FIv).sub ((FIv.ofInt q).mul halfPiI)).mul (C 1 16)).Mem
      ((fxVal n - q * (π / 2)) * (1 / 16)) :=
    FIv.mem_mul (FIv.mem_sub (fun _ => ⟨le_rfl, le_rfl⟩) (FIv.mem_mul (FIv.mem_ofInt q)
      mem_halfPiI)) (mem_C (by norm_num))
  obtain ⟨hc, hs⟩ := mem_taylorCS hY
  obtain ⟨hc4, hs4⟩ := mem_dbl4 hc hs
  have e : 16 * ((fxVal n - q * (π / 2)) * (1 / 16)) = fxVal n - q * (π / 2) := by ring
  rw [e] at hc4 hs4
  have := mem_rotQ q hc4 hs4
  rwa [sub_add_cancel] at this

/-! ## Centered form -/

/-- The scaled midpoint of an enclosure. -/
@[expose] def midI (Φ : FIv) : ℤ := (Φ.lo + Φ.hi) / 2

/-- The scaled radius about `midI`. -/
@[expose] def radI (Φ : FIv) : ℤ := max (midI Φ - Φ.lo) (Φ.hi - midI Φ)

/-- `cos d ∈ [1 − r²/2, 1]` for `|d| ≤ r`, `D = [−r, r]`. -/
@[expose] def cosSmall (D : FIv) : FIv := ⟨((C 1 1).sub ((C 1 2).mul D.sq)).lo, fxScale, D.ok⟩

/-- **Centered joint enclosure of `(cos z, sin z)`** for `z ∈ Φ`: with `m` the midpoint,
`r` the radius and `d = z − m ∈ [−r, r]`,
`cos z = cos m cos d − sin m sin d`, `sin z = sin m cos d + cos m sin d`, where `cos m, sin m`
come from `cosSinI` at the thin point `m`, `cos d ∈ [1 − r²/2, 1]` and `sin d ∈ [−r, r]`. The
width is about `2 |sin m| r` (resp. `2 |cos m| r`), i.e. close to the true range. -/
@[expose] def cosSinC (Φ : FIv) : FIv × FIv :=
  let D : FIv := ⟨-radI Φ, radI Φ, Φ.ok⟩
  let P := cosSinQ (midI Φ)
  (meetI unitI ((P.1.mul (cosSmall D)).sub (P.2.mul D)),
    meetI unitI ((P.2.mul (cosSmall D)).add (P.1.mul D)))

/-- Soundness of `cosSmall`. -/
theorem mem_cosSmall {d : ℝ} {D : FIv} (hD : D.Mem d) : (cosSmall D).Mem (cos d) := by
  intro hok
  have hok' : D.ok = true := hok
  have h1 : ((C 1 1).sub ((C 1 2).mul D.sq)).Mem (1 - 1 / 2 * d ^ 2) :=
    FIv.mem_sub (mem_C (by norm_num)) (FIv.mem_mul (mem_C (by norm_num)) (FIv.mem_sq hD))
  have hok2 : ((C 1 1).sub ((C 1 2).mul D.sq)).ok = true := by
    simp only [FIv.sub, FIv.mul, Bool.and_eq_true]
    refine ⟨rfl, rfl, ?_⟩
    unfold FIv.sq; split_ifs <;> exact hok'
  obtain ⟨a, _⟩ := h1 hok2
  refine ⟨?_, ?_⟩
  · simp only [cosSmall]
    have := one_sub_sq_div_two_le_cos (x := d)
    linarith
  · simp only [cosSmall, fxVal]
    rw [div_self fxScale_pos.ne']
    exact cos_le_one d

/-- The deviation from the midpoint lies in `[−r, r]`. -/
theorem mem_dev {Φ : FIv} {z : ℝ} (h : Φ.Mem z) :
    (⟨-radI Φ, radI Φ, Φ.ok⟩ : FIv).Mem (z - fxVal (midI Φ)) := by
  intro hok
  obtain ⟨h1, h2⟩ := h hok
  have hS := fxScale_pos
  have hr1 : ((midI Φ - Φ.lo : ℤ) : ℝ) ≤ ((radI Φ : ℤ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  have hr2 : ((Φ.hi - midI Φ : ℤ) : ℝ) ≤ ((radI Φ : ℤ) : ℝ) := by
    exact_mod_cast le_max_right _ _
  push_cast at hr1 hr2
  simp only [fxVal] at h1 h2 ⊢
  push_cast
  constructor
  · rw [neg_div, le_sub_iff_add_le, ← sub_eq_neg_add, ← sub_div]; linarith [h1,
      div_le_div_of_nonneg_right (show (midI Φ : ℝ) - radI Φ ≤ Φ.lo by linarith) hS.le]
  · rw [sub_le_iff_le_add, ← add_div]
    linarith [div_le_div_of_nonneg_right (show (Φ.hi : ℝ) ≤ radI Φ + midI Φ by linarith) hS.le]

/-- `sin d ∈ [−r, r]` whenever `d ∈ [−r, r]`. -/
theorem mem_sin_sym {r : ℤ} {b : Bool} {d : ℝ} (hd : (⟨-r, r, b⟩ : FIv).Mem d) :
    (⟨-r, r, b⟩ : FIv).Mem (sin d) := by
  intro hok
  obtain ⟨a, c⟩ := hd hok
  have h1 := abs_sin_le_abs (x := d)
  simp only [fxVal] at a c ⊢
  push_cast at a ⊢
  rw [neg_div] at a ⊢
  have : |d| ≤ (r : ℝ) / fxScale := abs_le.mpr ⟨a, c⟩
  exact ⟨by linarith [neg_abs_le (sin d)], by linarith [le_abs_self (sin d)]⟩

/-- **Soundness of `cosSinC`.** -/
theorem mem_cosSinC {Φ : FIv} {z : ℝ} (h : Φ.Mem z) :
    (cosSinC Φ).1.Mem (cos z) ∧ (cosSinC Φ).2.Mem (sin z) := by
  set m : ℝ := fxVal (midI Φ)
  have hD := mem_dev h
  have hP := mem_cosSinQ (midI Φ)
  have hcd := mem_cosSmall hD
  have hsd := mem_sin_sym hD
  have ez : z = m + (z - m) := by ring
  refine ⟨mem_meetI (mem_unitI (abs_cos_le_one _)) ?_,
    mem_meetI (mem_unitI (abs_sin_le_one _)) ?_⟩
  · rw [ez, cos_add]
    exact FIv.mem_sub (FIv.mem_mul hP.1 hcd) (FIv.mem_mul hP.2 hsd)
  · rw [ez, sin_add]
    exact FIv.mem_add (FIv.mem_mul hP.2 hcd) (FIv.mem_mul hP.1 hsd)

/-! ## Sanity fixtures -/

/-- Sanity (degenerate case): the enclosure of `cos 0` is valid and contains `1`. -/
theorem fixture_cos_zero : (cosSinI (C 0 1)).1.ok = true ∧ (cosSinI (C 0 1)).1.Mem 1 := by
  refine ⟨by decide +kernel, ?_⟩
  have := (mem_cosSinI (z := 0) (mem_C (p := 0) (q := 1) (by norm_num))).1
  rwa [cos_zero] at this

/-- Sanity (accepted fixture): at `z = 1.0471975512 ≈ π/3` the enclosure of `cos z` is valid and
lies in `[0.49999, 0.50001]`. -/
theorem fixture_cos_pi_third :
    (cosSinI (C 10471975512 10000000000)).1.ok = true ∧
      (C 49999 100000).lo ≤ (cosSinI (C 10471975512 10000000000)).1.lo ∧
      (cosSinI (C 10471975512 10000000000)).1.hi ≤ (C 50001 100000).hi := by
  decide +kernel

/-- Sanity (rejected fixture): an input of size `2000 > 1024` is rejected. -/
theorem fixture_cosSin_rejected : (cosSinI (C 2000 1)).1.ok = false := by decide +kernel

end PlasmaLean.Design.NearAxisQATrappedOsc
