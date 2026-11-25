/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFrameLaunch

/-! # Four physical entry balls for the continuous upper radial bracket -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialRibbonEntry
open Set DommaschkMirrorLaunch DommaschkBounceField DommaschkKamC KamNewton
open Theory.KAM WEll1Z2 Contract Forms Fields.VacuumBoozer
set_option linter.style.longLine false

def center (k : Fin 4) : ℝ := (471 + 2 * (k : ℝ)) / 1000
def tile (k : Fin 4) : Set ℝ := Icc (center k - 1 / 1000) (center k + 1 / 1000)

def radialCenter : Fin 4 → ℤ :=
  ![1203482259564462973386752,1203507549867741055811584,
    1203532840171019138236416,1203558130474297220661248]

def seed (k : Fin 4) : Certificates.PositionFrameSlabs.State :=
  { DommaschkPositionFramesFwd.start with point := ⟨radialCenter k, 0⟩, radius := 2^64 }

theorem covered {u : ℝ} (hu : u ∈ Icc (47 / 100) (239 / 500)) : ∃ k, u ∈ tile k := by
  by_cases h₁ : u ≤ 472 / 1000
  · exact ⟨0, by norm_num [tile, center]; constructor <;> linarith [hu.1]⟩
  by_cases h₂ : u ≤ 474 / 1000
  · exact ⟨1, by norm_num [tile, center]; constructor <;> linarith⟩
  by_cases h₃ : u ≤ 476 / 1000
  · exact ⟨2, by norm_num [tile, center]; constructor <;> linarith⟩
  exact ⟨3, by norm_num [tile, center]; constructor <;> linarith [hu.2]⟩

theorem nominal {k : Fin 4} {u : ℝ} (fit : u ∈ tile k) :
    |blend u (seedRadius false false) (seedRadius true false) - radialCenter k / (2 : ℝ)^80| ≤ 1 / 90000 := by
  obtain ⟨lo,hi⟩ := fit
  fin_cases k <;> simp only [seedRadius, moment, signAt, Bool.false_eq_true, ↓reduceIte,
    momentCRZero, momentARZero, blend] <;> norm_num [radialCenter,center] at lo hi ⊢ <;>
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The original birth reaches a radius-uniform Euclidean ball at the symmetry section.
From that same point the actual field has both outward solutions through 1/32 radian. -/
def Passage (uC zC uA zA : FA) (u φ : ℝ) (k : Fin 4) : Prop :=
  ∃ (sign : ℝ) (x : ℝ → State), |sign| = 1 ∧ φ + sign * |φ| = 0 ∧
    x 0 = birth uC zC uA zA u φ ∧
    (∀ t ∈ Icc 0 |φ|, HasDerivWithinAt x (physicalFlow φ sign t (x t)) (Icc 0 |φ|) t) ∧
    InStartBall (seed k) (x |φ|) ∧
    ∀ d : ℝ, |d| ≤ 1 → ∃ y : ℝ → State, y 0 = x |φ| ∧
      ∀ t ∈ Icc 0 (1 / 32 : ℝ),
        HasDerivWithinAt y (physicalFlow 0 d t (y t)) (Icc 0 (1 / 32)) t ∧
        y t ∈ Icc (tubeLo false) (tubeHi false)

theorem from_close {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A (1 / 10 ^ 12))
    {u φ : ℝ} {k : Fin 4} (hu : u ∈ Icc (47 / 100) (239 / 500)) (fit : u ∈ tile k)
    (small : |φ| ≤ 1 / 2 ^ 19) : Passage uC zC uA zA u φ k := by
  let sign : ℝ := if 0 ≤ φ then -1 else 1
  have hs : |sign| = 1 := by dsimp [sign]; split <;> norm_num
  have clock : φ + sign * |φ| = 0 := by
    by_cases h : 0 ≤ φ
    · simp [sign,h,abs_of_nonneg h]
    · simp [sign,h,abs_of_neg (lt_of_not_ge h)]
  have unit : u ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have strip : u ∈ Icc (11/25:ℝ) (27/50) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have near : |φ - azimuth false| ≤ 1 / 4096 := by
    simpa [azimuth] using small.trans (by norm_num : (1:ℝ)/2^19 ≤ 1/4096)
  obtain ⟨x,hx,trace⟩ := collar_of_close hc ha false u φ sign strip near hs.le
  have sub : Icc 0 |φ| ⊆ Icc 0 (1/64:ℝ) := Icc_subset_Icc_right (small.trans (by norm_num))
  obtain ⟨v,hv,eq⟩ := (trace |φ| (sub ⟨abs_nonneg _,le_rfl⟩)).2.2
  let B := birth uC zC uA zA u
  have motion (i : Fin 2) : |x |φ| i - B φ i| ≤ |φ| / 4 := by
    have c := congrFun eq i
    change x |φ| i = B φ i + |φ| * v i at c
    rw [c,add_sub_cancel_left,abs_mul,abs_abs]
    have bound : |v i| ≤ 1 / 4 := abs_le.mpr ⟨hv.1 i,hv.2 i⟩
    linarith only [mul_le_mul_of_nonneg_left bound (abs_nonneg φ)]
  obtain ⟨ar,az⟩ := launch_error hc ha false unit
  obtain ⟨mr,mz⟩ := launch_displacement hc ha false (φ := φ) unit
  change |B 0 0 - blend u (seedRadius false false) (seedRadius true false)| ≤ _ at ar
  change |B 0 1| ≤ _ at az
  change |B φ 0 - B 0 0| ≤ 2 / 10^12 + |φ - 0| / 6 at mr
  change |B φ 1 - B 0 1| ≤ 2 / 10^12 + |φ - 0| / 6 at mz
  rw [sub_zero] at mr mz
  have atR : |x |φ| 0 - radialCenter k / (2:ℝ)^80| ≤ 1 / 80000 := by
    linarith only [motion 0,mr,ar,nominal fit,small,
      abs_sub_le (x |φ| 0) (B φ 0) (radialCenter k / (2:ℝ)^80),
      abs_sub_le (B φ 0) (B 0 0) (radialCenter k / (2:ℝ)^80),
      abs_sub_le (B 0 0) (blend u (seedRadius false false) (seedRadius true false)) (radialCenter k / (2:ℝ)^80)]
  have atZ : |x |φ| 1| ≤ 1 / 1000000 := by
    have triangle (a b : ℝ) : |a| ≤ |a-b| + |b| := by simpa using abs_sub_le a b 0
    linarith only [motion 1,mz,az,small,triangle (x |φ| 1) (B φ 1),triangle (B φ 1) (B 0 1)]
  have ball : InStartBall (seed k) (x |φ|) := by
    have a := pow_le_pow_left₀ (abs_nonneg _) atR 2
    have b := pow_le_pow_left₀ (abs_nonneg _) atZ 2
    norm_num [InStartBall,seed,sq_abs] at a b ⊢
    linarith only [a,b]
  refine ⟨sign,x,hs,clock,hx,fun t ht => (trace t (sub ht)).1.mono sub,ball,?_⟩
  intro d hd
  have nearC : (995/1000:ℝ) ≤ radialCenter k / (2:ℝ)^80 ∧ radialCenter k / (2:ℝ)^80 ≤ 996/1000 := by
    fin_cases k <;> norm_num [radialCenter]
  obtain ⟨y,start,flow⟩ := exists_launch_step false 0 d (1/32) hd (by norm_num)
    (by norm_num [sectionPhase]) (x |φ|) (by change (99416:ℝ)/100000 ≤ _; linarith [(abs_le.mp atR).1,nearC.1])
    (by change _ ≤ (99723:ℝ)/100000; linarith [(abs_le.mp atR).2,nearC.2]) (atZ.trans (by norm_num))
  exact ⟨y,start,fun t ht => ⟨(flow t ht).1,(flow t ht).2.1⟩⟩

/-- All radii and all eight pre-existing endpoint certificates can use the same embedded tori. -/
theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      (∀ e φ, |φ - azimuth e.opposite| ≤ e.width → SectionEntry e uC zC uA zA φ) ∧
      ∀ u ∈ Icc (47/100:ℝ) (239/500), ∀ φ : ℝ, |φ| ≤ 1/2^19 → ∃ k, u ∈ tile k ∧ Passage uC zC uA zA u φ k := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),
    fun e _ h => transfer_to_start (by simpa using cC) (by simpa using cA) e h,?_⟩
  intro u hu φ small
  obtain ⟨k,fit⟩ := covered hu
  exact ⟨k,fit,from_close (by simpa using cC) (by simpa using cA) hu fit small⟩

end PlasmaLean.Design.DommaschkRadialRibbonEntry
