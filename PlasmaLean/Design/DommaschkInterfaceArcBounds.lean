/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkInterfaceArcProfiles
public import PlasmaLean.Design.DommaschkKamAInterfaceMoments

/-!
# From degree-four Fourier moments to the three interval tables of torus A

The polynomial is enclosed by Horner evaluation on each endpoint and on one
closed interval covering the arc. Both the Taylor remainder and the analytic
strip error are charged against each face of the proposed jet enclosure.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkInterfaceArcBounds

open PlasmaLean.Certificates.ValidatedQuadrature
open DommaschkInterfaceArcGeometry DommaschkInterfaceArcProfiles DommaschkKamAInterfaceMoments

/-- Signed integer moment for one cylindrical coordinate and Taylor degree. -/
def numerator (k : Jet) (d : ℕ) := moment k.source.1 k.source.2.1 k.source.2.2 d

/-- Absolute fifth moment for one cylindrical coordinate. -/
def fifthNum (k : Jet) := fifth k.source.1 k.source.2.1 k.source.2.2

private def coeffBox (k : Jet) (d : ℕ) :=
  FIv.ofFrac (numerator k d) (2 ^ 128 * d.factorial)

/-- The corresponding real Taylor coefficient, including its factorial. -/
noncomputable def coeff (k : Jet) (d : ℕ) : ℝ :=
  (numerator k d : ℝ) / (2 ^ 128 * d.factorial)

private theorem coeff_mem (k : Jet) (d : ℕ) : (coeffBox k d).Mem (coeff k d) := by
  have h : (((2 : ℤ) ^ 128 * d.factorial : ℤ) : ℝ) = 2 ^ 128 * d.factorial := by norm_num
  unfold coeff
  rw [← h]
  exact FIv.mem_ofFrac _ _

private def offsetBox : Jet → FIv
  | .radius => FIv.ofFrac 29 32
  | _ => FIv.ofInt 0

private theorem offset_mem (k : Jet) : (offsetBox k).Mem (seedOffset k) := by
  cases k
  case radius => exact FIv.mem_ofFrac 29 32
  all_goals simpa only [offsetBox, seedOffset, Int.cast_zero] using FIv.mem_ofInt 0

private def horner (c : ℕ → FIv) (t : FIv) : FIv :=
  let step (s : FIv) (d : ℕ) := (s.mul t).add (c d)
  step (step (step (step (c 4) 3) 2) 1) 0

private theorem horner_mem {k : Jet} {t : ℝ} {iv : FIv} (ht : iv.Mem t) :
    (horner (coeffBox k) iv).Mem (∑ d ∈ Finset.range 5, coeff k d * t ^ d) := by
  have step {i : FIv} {v : ℝ} (hi : i.Mem v) (d : ℕ) :
      ((i.mul iv).add (coeffBox k d)).Mem (v*t + coeff k d) :=
    FIv.mem_add (FIv.mem_mul hi ht) (coeff_mem k d)
  have expand : (∑ d ∈ Finset.range 5, coeff k d * t ^ d) =
      (((coeff k 4 * t + coeff k 3) * t + coeff k 2) * t + coeff k 1) * t + coeff k 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [expand]
  exact step (step (step (step (coeff_mem k 4) 3) 2) 1) 0

private def polyBox (k : Jet) (t : FIv) := (offsetBox k).add (horner (coeffBox k) t)

/-- Template for the absolute fifth-order Taylor error of the finite packed seed series. -/
def TaylorBound (k : Jet) (t : ℝ) : Prop :=
  |packedSeedJet t k - (seedOffset k + ∑ d ∈ Finset.range 5, coeff k d * t ^ d)| ≤
    (fifthNum k : ℝ) / 2 ^ 128 * (|t| ^ 5 / 120)

private def remBox (k : Jet) :=
  FIv.ofFrac (fifthNum k) (2 ^ 128 * 5 ^ 5 * 120)

private theorem rem_upper {k : Jet} {t : ℝ} (ht : |t| ≤ 1 / 5) :
    (fifthNum k : ℝ) / 2 ^ 128 * (|t| ^ 5 / 120) ≤ fxVal (remBox k).hi := by
  have hn : 0 ≤ (fifthNum k : ℝ) := by cases k <;> norm_num [fifthNum, Jet.source, fifth]
  have hq := pow_le_pow_left₀ (abs_nonneg t) ht 5
  have he := (FIv.mem_ofFrac (fifthNum k) (2 ^ 128 * 5 ^ 5 * 120)) (by rfl)
  refine le_trans ?_ he.2
  push_cast
  calc
    _ ≤ (fifthNum k : ℝ) / 2 ^ 128 * ((1 / 5) ^ 5 / 120) := by gcongr
    _ = _ := by ring

/-- One millionth exceeds every real-strip error through order two on this arc. -/
private def kamPad := FIv.ofFrac 1 1000000

private theorem kam_upper (k : Jet) :
    jetError ((1 / 10 ^ 12 : ℚ) : ℝ) k ≤ fxVal kamPad.hi := by
  have hp : (1 / 1000000 : ℝ) ≤ fxVal kamPad.hi := by
    norm_num [kamPad, FIv.ofFrac, fxVal, fxScale]
  refine le_trans ?_ hp
  cases k <;> norm_num [jetError, Jet.source]

private def checkBox (target : Jet → FIv) (iv : FIv) (k : Jet) : Bool :=
  let p := polyBox k iv
  let r := remBox k
  p.ok && (target k).lo ≤ p.lo - r.hi - kamPad.hi && p.hi + r.hi + kamPad.hi ≤ (target k).hi

private theorem margin_of_check {target : Jet → FIv} {iv : FIv} {t : ℝ}
    (ht : iv.Mem t) (ha : |t| ≤ 1 / 5) (hT : ∀ k, TaylorBound k t)
    (hc : ∀ k, checkBox target iv k = true) : SeedMargin target t := by
  intro k
  obtain ⟨⟨hok, hl⟩, hh⟩ : ((polyBox k iv).ok = true ∧
    (target k).lo ≤ (polyBox k iv).lo - (remBox k).hi - kamPad.hi) ∧
    (polyBox k iv).hi + (remBox k).hi + kamPad.hi ≤ (target k).hi := by
      simpa [checkBox] using hc k
  have hp := FIv.mem_add (offset_mem k) (horner_mem (k := k) ht) hok
  have hrem := abs_le.mp ((hT k).trans (rem_upper ha))
  have he := kam_upper k
  have h₁ : fxVal (target k).lo ≤
      fxVal (polyBox k iv).lo - fxVal (remBox k).hi - fxVal kamPad.hi := by
    unfold fxVal
    rw [← sub_div, ← sub_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hl) fxScale_pos.le
  have h₂ : fxVal (polyBox k iv).hi + fxVal (remBox k).hi + fxVal kamPad.hi ≤
      fxVal (target k).hi := by
    unfold fxVal
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hh) fxScale_pos.le
  change fxVal (polyBox k iv).lo ≤ _ ∧ _ ≤ fxVal (polyBox k iv).hi at hp
  constructor <;> linarith [hp.1, hp.2, hrem.1, hrem.2]

private def left : FIv := FIv.ofInt 0
private def right : FIv := FIv.ofFrac 1 5
private def arc : FIv := ⟨0, right.hi, true⟩

private theorem left_check (k : Jet) : checkBox leftBox left k = true := by cases k <;> rfl
private theorem right_check (k : Jet) : checkBox rightBox right k = true := by cases k <;> rfl
private theorem arc_check (k : Jet) : checkBox arcBox arc k = true := by cases k <;> rfl

private theorem right_mem : right.Mem (1 / 5) := by
  simpa only [right, Int.cast_one, Int.cast_ofNat] using FIv.mem_ofFrac 1 5

private theorem left_mem : left.Mem 0 := by
  simpa only [left, Int.cast_zero] using FIv.mem_ofInt 0

private theorem arc_mem {t : ℝ} (ht : t ∈ Set.Icc 0 (1 / 5)) : arc.Mem t := by
  intro _
  constructor
  · simpa [arc, fxVal] using ht.1
  · exact ht.2.trans (right_mem (by rfl)).2

/-- The exact integer moment table fits all three jet boxes as soon as it
supplies the stated Taylor remainder for each physical jet. -/
theorem seedMargins_of_taylor (h : ∀ k t, TaylorBound k t) :
    SeedMargin leftBox 0 ∧ SeedMargin rightBox (1 / 5) ∧
      ∀ t ∈ Set.Icc 0 (1 / 5), SeedMargin arcBox t := by
  refine ⟨margin_of_check left_mem (by norm_num) (fun k => h k 0) left_check,
    margin_of_check right_mem (by norm_num) (fun k => h k _) right_check, ?_⟩
  intro t ht
  exact margin_of_check (arc_mem ht) ((abs_of_nonneg ht.1).symm ▸ ht.2) (fun k => h k t) arc_check

/-- The checked full-grid signed and absolute moments give the physical jet error. -/
theorem packed_taylor (k : Jet) (t : ℝ) : TaylorBound k t := by
  have hab : k.source.2.1 + k.source.2.2 ≤ 2 := by cases k <;> norm_num [Jet.source]
  have h := gridJet_error k.source.1 k.source.2.1 k.source.2.2 hab t
  cases k <;> simpa only [TaylorBound, packedSeedJet, seedOffset, Jet.source, coeff, numerator,
    fifthNum, Bool.false_eq_true, ↓reduceIte, add_sub_add_left_eq_sub] using h

/-- The certified packed degree-four Fourier data meets each input box with room
for the real-strip perturbation of every physical jet. -/
theorem seedMargins : SeedMargin leftBox 0 ∧ SeedMargin rightBox (1 / 5) ∧
    ∀ t ∈ Set.Icc 0 (1 / 5), SeedMargin arcBox t := seedMargins_of_taylor packed_taylor

open PlasmaLean.Theory.KAM WEll1Z2 PlasmaLean.Stability.InterfacePrincipalDirection

/-- The outer profiles carried by Q-16 have the local row obstruction using only their
strip closeness to the stored seed. This statement applies to those very profiles. -/
theorem obstruction_of_close {u z : FA}
    (h : KamNewton.Close (9 / 1400) DommaschkKamDio.dkIotaA u z
      DommaschkKamA.u₀A DommaschkKamA.z₀A ((1 / 10 ^ 12 : ℚ) : ℝ)) :
    ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ v,
      0 < pair (metricRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v →
      0 < pair (curvatureRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v :=
  exists_obstruction (fun k => (continuous_cylindricalJet_of_close h k).continuousOn)
    (inBox_of_close_of_seedMargin h seedMargins.1) (inBox_of_close_of_seedMargin h seedMargins.2.1)
    (fun φ hφ => inBox_of_close_of_seedMargin h (seedMargins.2.2 φ hφ))

/-- Every exact Q-16 torus A has a point on its θ=0 interface arc where a positive
metric pairing forces a strictly positive curvature pairing with the chosen orientation. -/
theorem exactTorusA_obstruction {u z : FA} (h : DommaschkKamA.ExactTorusA u z) :
    ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ v,
      0 < pair (metricRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v →
      0 < pair (curvatureRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v :=
  obstruction_of_close h.close

end PlasmaLean.Design.DommaschkInterfaceArcBounds
