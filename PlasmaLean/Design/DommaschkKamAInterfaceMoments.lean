/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAInterfaceColumns
public import PlasmaLean.Design.DommaschkKamAInterfaceMomentData
public import Mathlib.Data.List.GetD

/-!
# Certified Taylor moments of the Dommaschk torus-A interface

The same full signed coefficients as the packed torus certificate determine the
signed Taylor polynomial and the absolute fifth moment for each cylindrical jet.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamAInterfaceMoments

open PlasmaLean.Design.DommaschkKamA PlasmaLean.Design.DommaschkKamAInterfaceFourier
open PlasmaLean.Design.DommaschkKamAInterfaceColumns PlasmaLean.Certificates.IccListCert
open PlasmaLean.Stability.InterfaceFourierTaylor

/-- The signed cosine factor after differentiating a cosine (height starts as a sine). -/
def modePhase (h : Bool) (a b d : ℕ) : ℤ :=
  if (a+b+d+(if h then 3 else 0))%4 = 0 then 1
  else if (a+b+d+(if h then 3 else 0))%4 = 2 then -1 else 0

/-- Zero-angle phase in the seed jet. -/
def phaseAngle (h : Bool) (a b : ℕ) : ℝ :=
  ((a : ℝ) + b - (if h then 1 else 0))*(Real.pi/2)

private theorem cosTaylorFour_phase (h : Bool) (a b : ℕ) (hab : a + b ≤ 2) (x : ℝ) :
    cosTaylorFour (phaseAngle h a b) x =
      ∑ d ∈ Finset.range 5, (modePhase h a b d : ℝ) * x^d / d.factorial := by
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  cases h <;> interval_cases a <;> interval_cases b <;> first
   | omega
   | norm_num [cosTaylorFour, phaseAngle, modePhase, Finset.sum_range_succ, Nat.factorial,
       Real.sin_neg, Real.cos_neg, show (2 : ℝ)*(Real.pi/2) = Real.pi by ring]; ring

/-- A lookup of a kernel-checked column of the transverse moments. -/
def storedColumn (m : ℤ) : List ℤ :=
  (storedBlock ((m+80).toNat / 7)).getD ((m+80).toNat % 7) []

private theorem column_eq {m : ℤ} (hm : m ∈ Finset.Icc (-80 : ℤ) 80) :
    baseColumn m = storedColumn m := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hm
  let j := (m+80).toNat
  have hj : j < 161 := by dsimp [j]; omega
  let i : Fin 23 := ⟨j/7, by omega⟩
  change baseColumn m = (storedBlock i).getD (j%7) []
  rw [← blocks_correct]
  have hb : j % 7 < (computedBlock i).length := by simp [computedBlock, Nat.mod_lt]
  rw [List.getD_eq_getElem _ _ hb]
  simp only [computedBlock, List.getElem_map, List.getElem_range]
  congr 1
  dsimp [j,i]
  omega

/-- Scaled amplitude of a single mode from the checked, compressed row. -/
def coeffInt (h : Bool) (a b : ℕ) (m : ℤ) : ℤ :=
  (storedColumn m).getD ((if h then 3 else 0) + a) 0 * (2*m)^b

private theorem slice_eq_coeff (h : Bool) (a b : ℕ) (ha : a ≤ 2)
    {m : ℤ} (hm : m ∈ Finset.Icc (-80 : ℤ) 80) :
    sliceAmplitude Sc Nc Mc (if h then gZ else gU) a b m = (coeffInt h a b m : ℝ)/2^128 := by
  rw [sliceAmplitude_eq_numerator]
  congr 1
  norm_cast
  have hm' (g : ℕ → ℕ → ℤ) : sliceNumerator Nc Mc g a b m =
      baseMoment g a m * (2*m)^b := by
    rw [← baseMoment_eq, sliceNumerator, sliceNumerator, Finset.sum_mul]
    simp
  rw [hm', coeffInt, ← column_eq hm]
  cases h <;> interval_cases a <;> rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
-- Each kernel computation sums one column coefficient at each of 161 frequencies.
/-- The signed moments in the quartic are the finite integer sums of the torus-A columns. -/
theorem signed_moment_eq (h : Bool) (a b d : ℕ) (hab : a + b ≤ 2) (hd : d ≤ 4) :
    modePhase h a b d *
      (∑ m ∈ Finset.Icc (-80 : ℤ) 80, coeffInt h a b m * (2*m)^d) = moment h a b d := by
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  simp only [sum_Icc_eq_list]
  cases h <;> interval_cases a <;> interval_cases b <;> first
    | omega
    | interval_cases d <;> rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
-- Each kernel computation uses absolute values after combining all transverse modes.
/-- The numerical remainder numerator is the full absolute fifth Fourier moment. -/
theorem absolute_fifth_eq (h : Bool) (a b : ℕ) (hab : a + b ≤ 2) :
    (∑ m ∈ Finset.Icc (-80 : ℤ) 80, |coeffInt h a b m| * |2*m|^5) = fifth h a b := by
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  simp only [sum_Icc_eq_list]
  cases h <;> interval_cases a <;> interval_cases b <;> first | omega | rfl

private theorem signed_real (h : Bool) (a b d : ℕ) (hab : a + b ≤ 2) (hd : d ≤ 4) :
    (∑ m ∈ Finset.Icc (-80 : ℤ) 80,
      sliceAmplitude Sc Nc Mc (if h then gZ else gU) a b m *
        (modePhase h a b d : ℝ) * (2*m : ℝ)^d) = (moment h a b d : ℝ)/2^128 := by
  rw [← signed_moment_eq h a b d hab hd]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [slice_eq_coeff h a b (by omega) hm]
  ring

private theorem fifth_real (h : Bool) (a b : ℕ) (hab : a + b ≤ 2) :
    (∑ m ∈ Finset.Icc (-80 : ℤ) 80,
      |sliceAmplitude Sc Nc Mc (if h then gZ else gU) a b m| * |(2*m : ℝ)|^5) =
      (fifth h a b : ℝ)/2^128 := by
  rw [← absolute_fifth_eq h a b hab]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [slice_eq_coeff h a b (by omega) hm, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2^128)]
  ring

/-- The degree-four polynomial and error bound for every actual radial or vertical torus-A
seed jet on the θ = 0 interface arc. The radial profile's constant 29/32 is added separately. -/
theorem gridJet_error (h : Bool) (a b : ℕ) (hab : a + b ≤ 2) (φ : ℝ) :
    |gridJet Sc Nc Mc (if h then 1 else 0) (if h then gZ else gU) a b 0 φ -
      ∑ d ∈ Finset.range 5, (moment h a b d : ℝ)/(2^128 * d.factorial) * φ^d| ≤
      (fifth h a b : ℝ)/2^128 * (|φ|^5/120) := by
  have ht := gridJet_slice_taylor Sc Nc Mc (if h then 1 else 0) (if h then gZ else gU) a b φ
  have hp : ((a : ℝ) + b - ((if h then 1 else 0 : ℕ) : ℝ)) * (Real.pi/2) =
      phaseAngle h a b := by cases h <;> simp [phaseAngle]
  rw [hp] at ht
  change |_ - ∑ m ∈ Finset.Icc (-80 : ℤ) 80,
    sliceAmplitude Sc Nc Mc (if h then gZ else gU) a b m *
      cosTaylorFour (phaseAngle h a b) ((2*m)*φ)| ≤ _ at ht
  have ep : (∑ m ∈ Finset.Icc (-80 : ℤ) 80,
      sliceAmplitude Sc Nc Mc (if h then gZ else gU) a b m *
        cosTaylorFour (phaseAngle h a b) ((2*m)*φ)) =
      ∑ d ∈ Finset.range 5, (moment h a b d : ℝ)/(2^128 * d.factorial) * φ^d := by
    simp_rw [cosTaylorFour_phase h a b hab, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hd5 := Finset.mem_range.mp hd
    have H := signed_real h a b d hab (by omega)
    calc
      _ = (∑ m ∈ Finset.Icc (-80 : ℤ) 80,
        sliceAmplitude Sc Nc Mc (if h then gZ else gU) a b m *
          (modePhase h a b d : ℝ) * (2*m : ℝ)^d) * (φ^d / d.factorial) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro m _
            ring
      _ = _ := by rw [H]; ring
  rw [ep] at ht
  exact ht.trans_eq (congrArg (· * (|φ|^5/120)) (fifth_real h a b hab))

end PlasmaLean.Design.DommaschkKamAInterfaceMoments
