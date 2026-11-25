/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkWideBirthBounds

/-! # A uniform three-harmonic enclosure of the original Q16 birth chart -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPeriodicBirthFourier

open Set DommaschkMirrorLaunch DommaschkKamAInterfaceFourier DommaschkKamC KamNewton
open Theory.KAM WEll1Z2 PlasmaLean.Certificates.IccListCert

def wave (z : Bool) (x : ℝ) : ℝ := if z then Real.sin x else Real.cos x
def offset (z : Bool) : ℝ := if z then 0 else 29/32
def error (z : Bool) : ℝ := if z then 1/3800 else 1/1200
def centre (z : Bool) (m : ℤ) : ℤ := 51 * weight false z m + 49 * weight true z m
def kept (m : ℤ) : Prop := -3 ≤ m ∧ m ≤ 3
instance (m : ℤ) : Decidable (kept m) := inferInstanceAs (Decidable (_ ∧ _))
def cut (z : Bool) (m : ℤ) : ℤ := if kept m then centre z m else 0
def delta (z : Bool) (m : ℤ) : ℤ := weight true z m - weight false z m
def series (z : Bool) (f : ℤ → ℤ) (φ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc (-80 : ℤ) 80, (f m : ℝ) * wave z (2*m*φ)
def low (z : Bool) (φ : ℝ) : ℝ := offset z + series z (cut z) φ / (100 * 2^128)

private theorem series_abs (z : Bool) (f : ℤ → ℤ) (φ : ℝ) :
    |series z f φ| ≤ ((∑ m ∈ Finset.Icc (-80 : ℤ) 80, |f m| : ℤ) : ℝ) := by
  rw [series, Int.cast_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m _
  rw [abs_mul, Int.cast_abs]
  apply mul_le_of_le_one_right (abs_nonneg _)
  cases z <;> first | exact Real.abs_sin_le_one _ | exact Real.abs_cos_le_one _

private theorem seed_jet (o z : Bool) (φ : ℝ) :
    gridJet 128 96 80 (if z then 1 else 0) (grid o z) 0 0 0 φ =
      series z (weight o z) φ / 2^128 := by
  rw [gridJet_slice, series, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have amp : sliceAmplitude 128 96 80 (grid o z) 0 0 m = (weight o z m : ℝ) / 2^128 := by
    rw [sliceAmplitude_eq_numerator, ← column_eq_weight o z hm, slice_eq_column]
  rw [amp]
  cases z
  · simp [wave]; ring
  · simp only [wave, ↓reduceIte, Nat.cast_zero, Nat.cast_one, zero_add, zero_sub, neg_one_mul]
    rw [show -(Real.pi/2)+2*m*φ = 2*m*φ - Real.pi/2 by ring, Real.cos_sub_pi_div_two]
    ring

private theorem seed_inner (φ : ℝ) :
    RofC u₀C 0 φ = offset false + series false (weight false false) φ / 2^128 ∧
    Zof z₀C 0 φ = offset true + series true (weight false true) φ / 2^128 := by
  constructor
  · unfold RofC DommaschkKam.dkR0 Zof
    rw [eval_u₀C, KamTorusA.psi, sub_add_cancel]
    exact congrArg (fun x : ℝ => 29/32+x) ((zeroJet _ _ _ _ _ _ _).trans (seed_jet false false φ))
  · rw [show offset true = 0 by rfl, zero_add, ← seed_jet false true]
    unfold Zof
    rw [eval_z₀C, KamTorusA.psi, sub_add_cancel]
    exact zeroJet _ _ _ _ _ _ _

private theorem seed_outer (φ : ℝ) :
    RofC DommaschkKamA.u₀A 0 φ = offset false + series false (weight true false) φ / 2^128 ∧
    Zof DommaschkKamA.z₀A 0 φ = offset true + series true (weight true true) φ / 2^128 := by
  rw [radius_seed_eq, height_seed_eq]
  exact ⟨congrArg (fun x : ℝ => 29/32+x) (seed_jet true false φ),
    by rw [show offset true = 0 by rfl, zero_add]; exact seed_jet true true φ⟩

private theorem series_delta (z : Bool) (φ : ℝ) :
    series z (delta z) φ = series z (weight true z) φ - series z (weight false z) φ := by
  simp [series, delta, sub_mul, Finset.sum_sub_distrib]

private theorem series_tail (z : Bool) (φ : ℝ) :
    series z (fun m => centre z m - cut z m) φ =
      51 * series z (weight false z) φ + 49 * series z (weight true z) φ -
        series z (cut z) φ := by
  simp only [series, centre, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  ring

private def mass (z : Bool) : ℤ :=
  ∑ m ∈ Finset.Icc (-80 : ℤ) 80, (|centre z m - cut z m| + 5 * |delta z m|)

private theorem mass_eq (z : Bool) :
    mass z = (∑ m ∈ Finset.Icc (-80 : ℤ) 80, |centre z m - cut z m|) +
      5 * (∑ m ∈ Finset.Icc (-80 : ℤ) 80, |delta z m|) := by
  simp [mass, Finset.sum_add_distrib, Finset.mul_sum]

set_option maxRecDepth 8192 in
private theorem mass_bound (z : Bool) :
    (mass z : ℝ)/(100*2^128) + 1/10^12 ≤ error z := by
  have h : mass z = (if z then 8603289951733838333158744067550223178
      else 27971233187301424953630809559859037366) := by
    cases z <;> unfold mass <;> rw [sum_Icc_eq_list] <;> rfl
  rw [h]
  cases z <;> norm_num [error]

private theorem approximate (z : Bool) {u φ x c a : ℝ}
    (hu : u ∈ Icc (11/25 : ℝ) (27/50)) (hc : |c -
      (offset z + series z (weight false z) φ / 2^128)| ≤ 1/10^12)
    (ha : |a - (offset z + series z (weight true z) φ / 2^128)| ≤ 1/10^12)
    (hx : x = blend u c a) : |x - low z φ| ≤ error z := by
  let C := offset z + series z (weight false z) φ / 2^128
  let A := offset z + series z (weight true z) φ / 2^128
  have ue : |100*u-49| ≤ 5 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have he : |x - blend u C A| ≤ 1/10^12 := by
    rw [hx, show blend u c a - blend u C A = (1-u)*(c-C) + u*(a-A) by unfold blend; ring]
    apply (abs_add_le ..).trans
    rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ u by linarith [hu.1]),
      abs_of_nonneg (show 0 ≤ 1-u by linarith [hu.2])]
    calc
      _ ≤ (1-u)*(1/10^12) + u*(1/10^12) := by gcongr <;> linarith [hu.1, hu.2]
      _ = _ := by ring
  have hD := series_abs z (delta z) φ
  have hT := series_abs z (fun m => centre z m - cut z m) φ
  have weighted := mul_le_mul ue hD (abs_nonneg _) (show (0:ℝ) ≤ 5 by norm_num)
  rw [← abs_mul] at weighted
  have bound : |series z (fun m => centre z m - cut z m) φ +
      (100*u-49)*series z (delta z) φ| ≤ (mass z : ℝ) := by
    rw [mass_eq, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    exact (abs_add_le ..).trans (add_le_add hT weighted)
  have ident : blend u C A - low z φ = (series z (fun m => centre z m - cut z m) φ +
      (100*u-49)*series z (delta z) φ)/(100*2^128) := by
    rw [series_tail, series_delta]
    dsimp [C,A,blend,low]
    ring
  have hb : |blend u C A - low z φ| ≤ (mass z : ℝ)/(100*2^128) := by
    rw [ident, abs_div, abs_of_pos (by positivity : (0:ℝ) < 100*2^128)]
    exact div_le_div_of_nonneg_right bound (by positivity)
  linarith only [abs_sub_le x (blend u C A) (low z φ), he, hb, mass_bound z]

/-- The two reference polynomials approximate every point in the original deep strip,
at every real azimuth and with the certified strip errors of both invariant tori. -/
theorem birth_error {uC zC uA zA : FA}
    (hc : Close (9/1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1/10^12))
    (ha : Close (9/1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A (1/10^12))
    {u : ℝ} (hu : u ∈ Icc (11/25 : ℝ) (27/50)) (φ : ℝ) :
    let b := birth uC zC uA zA u φ
    |b 0 - low false φ| ≤ error false ∧ |b 1 - low true φ| ≤ error true := by
  have hr : (0:ℝ) < 9/1400 := by norm_num
  have cR := (DommaschkKamA.profileJetBound hr hc.du ana_u₀C DommaschkKam.dkR0).value 0 φ
  have cZ := (DommaschkKamA.profileJetBound hr hc.dz ana_z₀C 0).value 0 φ
  obtain ⟨aR,aZ⟩ := DommaschkKamA.profileJets_of_close ha
  have r := aR.value 0 φ
  have z := aZ.value 0 φ
  change |RofC _ 0 φ - RofC _ 0 φ| ≤ _ at cR r
  change |0 + Zof _ 0 φ - (0 + Zof _ 0 φ)| ≤ _ at cZ
  rw [(seed_inner φ).1] at cR
  rw [(seed_outer φ).1] at r
  simp only [zero_add, (seed_inner φ).2] at cZ
  rw [(seed_outer φ).2] at z
  exact ⟨approximate false hu cR r rfl, approximate true hu cZ z rfl⟩

/-- The folded rational coefficients in the positive-frequency convention. -/
def coeff (z : Bool) (j : ℕ) : ℚ :=
  if j = 0 then (if z then 0 else 29/32 + (centre z 0 : ℚ)/(100*2^128))
  else ((centre z j : ℚ) + (if z then -1 else 1) * (centre z (-(j : ℤ)) : ℚ))/(100*2^128)

/-- The retained seven signed modes fold into three real harmonics and a constant. -/
theorem low_eq (z : Bool) (φ : ℝ) :
    low z φ = (coeff z 0 : ℝ) + (coeff z 1 : ℝ)*wave z (2*φ) +
      (coeff z 2 : ℝ)*wave z (4*φ) + (coeff z 3 : ℝ)*wave z (6*φ) := by
  have subset : Finset.Icc (-3 : ℤ) 3 ⊆ Finset.Icc (-80 : ℤ) 80 :=
    fun _ h => Finset.mem_Icc.mpr ⟨by linarith [(Finset.mem_Icc.mp h).1],
      by linarith [(Finset.mem_Icc.mp h).2]⟩
  have trunc : series z (cut z) φ =
      ∑ m ∈ Finset.Icc (-3 : ℤ) 3, (centre z m : ℝ)*wave z (2*m*φ) := by
    unfold series
    rw [← Finset.sum_subset subset (fun m _ hm => by
      have hn : ¬kept m := fun h => hm (Finset.mem_Icc.mpr h)
      simp [cut,hn])]
    apply Finset.sum_congr rfl
    intro m hm
    rw [cut, if_pos (show kept m from Finset.mem_Icc.mp hm)]
  rw [low, trunc, sum_Icc_eq_list]
  cases z <;> norm_num [List.range_succ, List.sum_cons, offset, coeff, wave,
    show (-6:ℝ) = -6 by rfl, neg_mul, Real.sin_neg, Real.cos_neg] <;> ring

end PlasmaLean.Design.DommaschkPeriodicBirthFourier
