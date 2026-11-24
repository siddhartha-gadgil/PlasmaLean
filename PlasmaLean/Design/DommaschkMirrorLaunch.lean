/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorLaunchData
public import PlasmaLean.Design.DommaschkInterfaceJets

/-!
# Mirror launch coordinates on the two KAM sections

The packed Fourier grids determine the launch radius on the symmetry sections.
The vertical seed vanishes there. Strip closeness transfers both values to the
true tori and to every convex combination of their section coordinates.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open DommaschkKamAInterfaceFourier DommaschkKamC KamNewton
open PlasmaLean.Theory.KAM WEll1Z2

/-- The two azimuths about which the mirror calculations are performed. -/
def azimuth (opposite : Bool) : ℝ := if opposite then Real.pi / 2 else 0

/-- The real Fourier phase at a symmetry section has this integer sign. -/
def signAt (opposite : Bool) (m : ℤ) : ℤ :=
  if opposite then (if m % 2 = 0 then 1 else -1) else 1

private theorem cos_at (q : Bool) (x : ℝ) (m : ℤ) :
    Real.cos (x + 2 * (m : ℝ) * azimuth q) = (signAt q m : ℝ) * Real.cos x := by
  cases q
  · simp [azimuth, signAt]
  · simp only [azimuth, if_true]
    rw [show 2 * (m : ℝ) * (Real.pi / 2) = m * Real.pi by ring, Real.cos_add,
      Real.cos_int_mul_pi, Real.sin_int_mul_pi, neg_one_zpow_eq_ite]
    by_cases h : Even m
    · simp [signAt, h, Int.even_iff.mp h]
    · have hn : ¬ m % 2 = 0 := fun e => h (Int.even_iff.mpr e)
      simp only [h, if_false, signAt, if_true, hn, Int.cast_neg, Int.cast_one, mul_zero, sub_zero]
      ring

private theorem amp (o z : Bool) (b : ℕ) {m : ℤ} (hm : m ∈ Finset.Icc (-80 : ℤ) 80) :
    sliceAmplitude 128 96 80 (grid o z) 0 b m =
      ((weight o z m * (2*m)^b : ℤ) : ℝ) / 2^128 := by
  rw [sliceAmplitude_eq_numerator, ← column_eq_weight o z hm, ← slice_eq_column]
  congr 2
  simp [sliceNumerator, Finset.sum_mul]

/-- Unscaled signed frequency moment at one symmetry section. -/
def moment (o z q : Bool) (b : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc (-80 : ℤ) 80, weight o z m * (2*m)^b * signAt q m

/-- Evaluation holds for every toroidal derivative order. -/
theorem jet_at (o z q : Bool) (p b : ℕ) :
    gridJet 128 96 80 p (grid o z) 0 b 0 (azimuth q) =
    (moment o z q b : ℝ) / 2^128 * Real.cos (((b : ℝ)-p)*(Real.pi/2)) := by
  rw [gridJet_slice, moment, Int.cast_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [amp o z b hm, cos_at]
  push_cast
  ring

/-- The absolute moment bounds the jet uniformly, including between symmetry sections. -/
theorem jet_abs (o z : Bool) (p b : ℕ) (φ : ℝ) :
    |gridJet 128 96 80 p (grid o z) 0 b 0 φ| ≤
    ((∑ m ∈ Finset.Icc (-80 : ℤ) 80, |weight o z m * (2*m)^b| : ℤ) : ℝ) / 2^128 := by
  rw [gridJet_slice, Int.cast_sum, Finset.sum_div]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [amp o z b hm, abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^128), Int.cast_abs]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- Every zeroth-order section coordinate of either packed seed is 1/6-Lipschitz in azimuth. -/
theorem jet_displacement (o z : Bool) (p : ℕ) (a φ : ℝ) :
    |gridJet 128 96 80 p (grid o z) 0 0 0 φ - gridJet 128 96 80 p (grid o z) 0 0 0 a|
    ≤ (1/6) * |φ-a| := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (fun t _ => (gridJet_toroidal 128 96 80 p (grid o z) 0 0 0 t).hasDerivWithinAt)
    _ convex_univ (Set.mem_univ a) (Set.mem_univ φ)
  intro t _
  apply (jet_abs o z p 1 t).trans
  cases o <;> cases z <;> first
    | rw [absCdatU1]; norm_num
    | rw [absCdatZ1]; norm_num
    | rw [absAdatU1]; norm_num
    | rw [absAdatZ1]; norm_num

private theorem c_radius (φ : ℝ) : RofC u₀C 0 φ =
    29/32 + gridJet 128 96 80 0 (grid false false) 0 0 0 φ := by
  unfold RofC DommaschkKam.dkR0 Zof
  rw [eval_u₀C, KamTorusA.psi, sub_add_cancel]
  exact congrArg (fun x : ℝ => 29/32+x) (zeroJet _ _ _ _ _ _ _)

private theorem c_height (φ : ℝ) : Zof z₀C 0 φ =
    gridJet 128 96 80 1 (grid false true) 0 0 0 φ := by
  unfold Zof
  rw [eval_z₀C, KamTorusA.psi, sub_add_cancel]
  exact zeroJet _ _ _ _ _ _ _

/-- Radius read from the packed grid in geometric coordinates. -/
def seedRadius (o q : Bool) : ℝ := 29/32 + (moment o false q 0 : ℝ) / 2^128

private theorem seedRadii (q : Bool) :
    RofC u₀C 0 (azimuth q) = seedRadius false q ∧
    RofC DommaschkKamA.u₀A 0 (azimuth q) = seedRadius true q := by
  rw [c_radius, radius_seed_eq]
  change _ ∧ 29/32 + gridJet 128 96 80 0 (grid true false) 0 0 0 _ = _
  simp [jet_at, seedRadius]

private theorem seedHeights (q : Bool) :
    Zof z₀C 0 (azimuth q) = 0 ∧ Zof DommaschkKamA.z₀A 0 (azimuth q) = 0 := by
  rw [c_height, height_seed_eq]
  change _ ∧ gridJet 128 96 80 1 (grid true true) 0 0 0 _ = 0
  simp [jet_at]

/-- Linear interpolation of the two section coordinates used by the launch chart. -/
def blend (u c a : ℝ) : ℝ := (1-u)*c + u*a

private theorem blend_error {u c a C A e : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hc : |c-C| ≤ e) (ha : |a-A| ≤ e) : |blend u c a - blend u C A| ≤ e := by
  rw [show blend u c a - blend u C A = (1-u)*(c-C)+u*(a-A) by unfold blend; ring]
  calc
    _ ≤ |(1-u)*(c-C)| + |u*(a-A)| := abs_add_le ..
    _ = (1-u)*|c-C| + u*|a-A| := by
      simp [abs_mul, abs_of_nonneg hu.1, abs_of_nonneg (sub_nonneg.mpr hu.2)]
    _ ≤ (1-u)*e + u*e := by gcongr <;> linarith [hu.1, hu.2]
    _ = e := by ring

/-- Both true launch coordinates, for every interpolating radius on both sections.
The radius is within the KAM error of its checked Fourier moment. -/
theorem launch_error {uC zC uA zA : FA} {e : ℝ}
    (hc : Close (9/1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C e)
    (ha : Close (9/1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A e)
    (q : Bool) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    |blend u (RofC uC 0 (azimuth q)) (RofC uA 0 (azimuth q)) -
      blend u (seedRadius false q) (seedRadius true q)| ≤ e ∧
    |blend u (Zof zC 0 (azimuth q)) (Zof zA 0 (azimuth q))| ≤ e := by
  have hr : (0 : ℝ) < 9/1400 := by norm_num
  have cR := (DommaschkKamA.profileJetBound hr hc.du ana_u₀C DommaschkKam.dkR0).value 0 (azimuth q)
  have cZ := (DommaschkKamA.profileJetBound hr hc.dz ana_z₀C 0).value 0 (azimuth q)
  obtain ⟨aR,aZ⟩ := DommaschkKamA.profileJets_of_close ha
  obtain ⟨hC,hA⟩ := seedRadii q
  obtain ⟨z₁,z₂⟩ := seedHeights q
  constructor
  · rw [← hC, ← hA]
    exact blend_error hu cR (aR.value 0 _)
  · have h := blend_error hu (by simpa only [zero_add, z₁] using cZ)
                   (by simpa only [z₂] using aZ.value 0 (azimuth q))
    simpa [blend] using h

/-- The full deep strip at a symmetry section lies inside these candidate-specific
coordinate bounds, including the KAM uncertainty. -/
theorem section_box {uC zC uA zA : FA}
    (hc : Close (9/1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1/10^12))
    (ha : Close (9/1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A
      (1/10^12)) (q : Bool) {u : ℝ} (hu : u ∈ Set.Icc (11/25) (27/50)) :
    blend u (RofC uC 0 (azimuth q)) (RofC uA 0 (azimuth q)) ∈
      (if q then Set.Icc (89400/100000) (89548/100000)
       else Set.Icc (99517/100000) (99622/100000)) ∧
    |blend u (Zof zC 0 (azimuth q)) (Zof zA 0 (azimuth q))| ≤ 1/10^12 := by
  obtain ⟨hl,hh⟩ := hu
  obtain ⟨hr,hz⟩ := launch_error hc ha q (u := u) ⟨by linarith, by linarith⟩
  refine ⟨?_,hz⟩
  rw [abs_le] at hr
  cases q
  · simp only [seedRadius, moment, signAt, Bool.false_eq_true, ↓reduceIte,
      momentCRZero, momentARZero, blend] at hr
    change _ ∈ Set.Icc _ _
    unfold blend
    constructor <;> linarith
  · simp only [seedRadius, moment, signAt, if_true, momentCRPi, momentARPi, blend] at hr
    change _ ∈ Set.Icc _ _
    unfold blend
    constructor <;> linarith

/-- A joint bound for every birth in the closed phase sector. -/
theorem sector_box {uC zC uA zA : FA}
    (hc : Close (9/1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1/10^12))
    (ha : Close (9/1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A
      (1/10^12)) (q : Bool) {u φ : ℝ} (hu : u ∈ Set.Icc (11/25) (27/50))
    (hφ : |φ-azimuth q| ≤ 1/4096) :
    blend u (RofC uC 0 φ) (RofC uA 0 φ) ∈
      (if q then Set.Icc (8939/10000) (8956/10000) else Set.Icc (9951/10000) (9963/10000)) ∧
    |blend u (Zof zC 0 φ) (Zof zA 0 φ)| ≤ 1/24000 := by
  have hr : (0:ℝ) < 9/1400 := by norm_num
  have hu' : u ∈ Set.Icc 0 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have error {f s : ℝ → ℝ} (he : ∀ t, |f t - s t| ≤ 1/10^12)
      (moving : |s φ - s (azimuth q)| ≤ 1/6 * |φ-azimuth q|) :
      |f φ - f (azimuth q)| ≤ 1/24020 := by
    have left := abs_sub_le (f φ) (s φ) (f (azimuth q))
    have right := abs_sub_le (s φ) (s (azimuth q)) (f (azimuth q))
    rw [abs_sub_comm (s (azimuth q))] at right
    linarith [he φ, he (azimuth q)]
  have cR := (DommaschkKamA.profileJetBound hr hc.du ana_u₀C DommaschkKam.dkR0).value 0
  have cZ := (DommaschkKamA.profileJetBound hr hc.dz ana_z₀C 0).value 0
  obtain ⟨aR,aZ⟩ := DommaschkKamA.profileJets_of_close ha
  have r₁ := error (f := RofC uC 0) (s := RofC u₀C 0) cR (by
    simpa only [c_radius, add_sub_add_left_eq_sub] using jet_displacement false false 0 (azimuth q) φ)
  have r₂ := error (aR.value 0) (by
    simp only [radius_seed_eq, add_sub_add_left_eq_sub]
    exact jet_displacement true false 0 (azimuth q) φ)
  have z₁ := error (f := Zof zC 0) (s := Zof z₀C 0) (by simpa only [zero_add] using cZ) (by
    simpa only [c_height] using jet_displacement false true 1 (azimuth q) φ)
  have z₂ := error (aZ.value 0) (by
    simp only [height_seed_eq]
    exact jet_displacement true true 1 (azimuth q) φ)
  have δR := abs_le.mp (blend_error hu' r₁ r₂)
  have δz := abs_le.mp (blend_error hu' z₁ z₂)
  obtain ⟨hR,hz⟩ := section_box hc ha q hu
  constructor
  · cases q <;> change _ ∈ Set.Icc _ _ at hR ⊢ <;> constructor <;> linarith [hR.1,hR.2]
  · obtain ⟨zlo,zhi⟩ := abs_le.mp hz
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end PlasmaLean.Design.DommaschkMirrorLaunch
