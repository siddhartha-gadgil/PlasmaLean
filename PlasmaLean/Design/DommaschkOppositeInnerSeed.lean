/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFrameLaunch

/-! # The original inner birth reaches the opposite-section singleton seed -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeInnerSeed

open Set DommaschkMirrorLaunch DommaschkBounceField DommaschkKamC KamNewton
open Theory.KAM WEll1Z2 Contract Forms Fields.VacuumBoozer

/-- The actual dyadic singleton seed in the opposite-section prefix packet. -/
def seed : Certificates.PositionFrameSlabs.State :=
  { DommaschkPositionFramesFwd.start with
    point := ⟨1081317837092435255099392,0⟩, radius := 7471231115882077 }

abbrev u : ℝ := 47 / 100
abbrev width : ℝ := 1 / 2 ^ 27
private abbrev allowance : ℝ := 1 / 250000000

theorem nominal : |blend u (seedRadius false true) (seedRadius true true) -
    seed.point.x / (2 : ℝ)^80| ≤ 1 / 10^12 := by
  simp only [seedRadius,moment,signAt,ite_true,momentCRPi,momentARPi,blend]
  norm_num [u,seed]

/-- Travel from the actual original birth to the common absolute section, ending in the
stored Euclidean seed ball for either of the physical signed traces. -/
def Entry (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  let t := |φ - azimuth true|
  ∃ (sign : ℝ) (x : ℝ → State),
    |sign| = 1 ∧ φ + sign * t = azimuth true ∧ x 0 = birth uC zC uA zA u φ ∧
    (∀ s ∈ Icc 0 t, HasDerivWithinAt x (physicalFlow φ sign s (x s)) (Icc 0 t) s) ∧
    InStartBall seed (x t)

theorem from_close {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A
      DommaschkKamA.z₀A (1 / 10 ^ 12)) {φ : ℝ}
    (hφ : |φ - azimuth true| ≤ width) : Entry uC zC uA zA φ := by
  let a := azimuth true
  let t := |φ - a|
  let sign : ℝ := if a ≤ φ then -1 else 1
  have hs : |sign| = 1 := by dsimp [sign]; split <;> norm_num
  have phase : φ + sign * t = a := by
    by_cases h : a ≤ φ
    · simp [sign, h, t, abs_of_nonneg (sub_nonneg.mpr h)]
    · simp [sign, h, t, abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
  have small : t ≤ (1 : ℝ) / 4096 := hφ.trans (by norm_num [width])
  have strip : u ∈ Icc (11 / 25 : ℝ) (27 / 50) := by
    norm_num [u]
  have unit : u ∈ Icc (0 : ℝ) 1 := by norm_num [u]
  obtain ⟨x, hx, trace⟩ := collar_of_close hc ha true u φ sign strip small hs.le
  have sub : Icc 0 t ⊆ Icc 0 (1 / 64 : ℝ) := Icc_subset_Icc_right (small.trans (by norm_num))
  obtain ⟨v, hv, xe⟩ := (trace t (sub ⟨abs_nonneg _, le_rfl⟩)).2.2
  let b := birth uC zC uA zA u
  have dv (i : Fin 2) : |(x t) i - b φ i| ≤ t / 4 := by
    have c := congrFun xe i
    change (x t) i = b φ i + t * v i at c
    rw [c, add_sub_cancel_left, abs_mul, abs_of_nonneg (abs_nonneg (φ - a))]
    have bound : |v i| ≤ 1 / 4 := abs_le.mpr ⟨hv.1 i, hv.2 i⟩
    linarith [mul_le_mul_of_nonneg_left bound (abs_nonneg (φ - a))]
  obtain ⟨motionR, motionZ⟩ := launch_displacement hc ha true (φ := φ) unit
  obtain ⟨anchorR, anchorZ⟩ := launch_error hc ha true unit
  have anchor (i : Fin 2) (center : ℝ)
      (motion : |b φ i - b a i| ≤ 2 / 10 ^ 12 + t / 6)
      (atCenter : |b a i - center| ≤ 2 / 10 ^ 12) :
      |(x t) i - center| ≤ allowance := by
    have d := abs_sub_le ((x t) i) (b φ i) center
    have f := abs_sub_le (b φ i) (b a i) center
    have ht : t ≤ width := hφ
    norm_num [width,allowance] at ht ⊢
    linarith only [d,f,atCenter,motion,dv i,ht]
  have hr : |b a 0 - seed.point.x / (2 : ℝ)^80| ≤ 2 / 10 ^ 12 := by
    let c := blend u (seedRadius false true) (seedRadius true true)
    have d := abs_sub_le (b a 0) c (seed.point.x / (2 : ℝ)^80)
    change |b a 0 - c| ≤ _ at anchorR
    have nom : |c - seed.point.x / (2 : ℝ)^80| ≤ 1 / 10 ^ 12 := nominal
    linarith
  have hz : |b a 1 - seed.point.y / (2 : ℝ)^80| ≤ 2 / 10 ^ 12 := by
    have z : seed.point.y = 0 := by rfl
    rw [z, Int.cast_zero, zero_div, sub_zero]
    exact anchorZ.trans (by norm_num)
  have squared {y : ℝ} (h : |y| ≤ allowance) : y^2 ≤ allowance^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have budget : 2 * allowance^2 ≤ (seed.radius / (2 : ℝ)^80)^2 := by
    norm_num [allowance,seed]
  refine ⟨sign, x, hs, phase, hx, fun s h => (trace s (sub h)).1.mono sub, ?_⟩
  unfold InStartBall
  linarith only [squared (anchor 0 _ motionR hr), squared (anchor 1 _ motionZ hz), budget]

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ, |φ - azimuth true| ≤ width → Entry uC zC uA zA φ := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),fun φ hφ =>
      from_close (by simpa using cC) (by simpa using cA) hφ⟩

end PlasmaLean.Design.DommaschkOppositeInnerSeed
