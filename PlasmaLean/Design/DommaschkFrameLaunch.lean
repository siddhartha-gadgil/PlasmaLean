/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorSectorFlow
public import PlasmaLean.Design.DommaschkPositionFramesBack
public import PlasmaLean.Design.DommaschkPositionFramesFwd

/-!
# Physical entry into the recorded position tube

At all eight N-60 endpoints the two directions share an initial ball. The Q-16
profile displacement and the physical velocity bound put the section point of
each birth in a small angular sector inside that Euclidean ball.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open DommaschkKamC KamNewton DommaschkBounceField Set
open PlasmaLean.Theory.KAM WEll1Z2
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer

namespace MirrorEndpoint

private def allowance (e : MirrorEndpoint) : ℝ :=
  if e.opposite then 4 / 10^7 else 8 / 10^7

private theorem nominal (e : MirrorEndpoint) :
    |blend e.radius (seedRadius false e.opposite) (seedRadius true e.opposite) -
      e.start.point.x / (2 : ℝ)^80| ≤ 1 / 10 ^ 12 := by
  cases e <;> simp only [radius, start, opposite, seedRadius, moment, signAt, blend,
    Bool.false_eq_true, ↓reduceIte, momentCRZero, momentARZero, momentCRPi, momentARPi] <;>
    norm_num

/-- The pilot has precisely this recorded initial state in both compiled directions. -/
theorem pilot_starts : start .q0r470 = DommaschkPositionFramesFwd.start ∧
    start .q0r470 = DommaschkPositionFramesBack.start := ⟨rfl, rfl⟩

end MirrorEndpoint

/-- Euclidean entry criterion in physical coordinates. -/
def InStartBall (s : Certificates.PositionFrameSlabs.State)
    (x : DommaschkBounceField.State) : Prop :=
  (x 0 - s.point.x / (2 : ℝ)^80)^2 + (x 1 - s.point.y / (2 : ℝ)^80)^2 ≤
    (s.radius / (2 : ℝ)^80)^2

/-- A field line travels from its birth to the common section of the two long traces. -/
def SectionEntry (e : MirrorEndpoint) (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  let t := |φ - azimuth e.opposite|
  ∃ (sign : ℝ) (x : ℝ → DommaschkBounceField.State),
    |sign| = 1 ∧ φ + sign * t = azimuth e.opposite ∧ x 0 = birth uC zC uA zA e.radius φ ∧
    (∀ s ∈ Icc 0 t, HasDerivWithinAt x (physicalFlow φ sign s (x s)) (Icc 0 t) s) ∧
    InStartBall e.start (x t)

/-- A physical birth within the stated half-width reaches the checked Euclidean ball. -/
theorem transfer_to_start {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A
      DommaschkKamA.z₀A (1 / 10 ^ 12)) (e : MirrorEndpoint) {φ : ℝ}
    (hφ : |φ - azimuth e.opposite| ≤ e.width) : SectionEntry e uC zC uA zA φ := by
  let a := azimuth e.opposite
  let t := |φ - a|
  let sign : ℝ := if a ≤ φ then -1 else 1
  have hs : |sign| = 1 := by dsimp [sign]; split <;> norm_num
  have phase : φ + sign * t = a := by
    by_cases h : a ≤ φ
    · simp [sign, h, t, abs_of_nonneg (sub_nonneg.mpr h)]
    · simp [sign, h, t, abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
  have small : t ≤ (1 : ℝ) / 4096 := hφ.trans (by
    unfold MirrorEndpoint.width; split <;> norm_num)
  have strip : e.radius ∈ Icc (11 / 25 : ℝ) (27 / 50) := by
    cases e <;> constructor <;> norm_num [MirrorEndpoint.radius]
  have unit : e.radius ∈ Icc (0 : ℝ) 1 := ⟨by linarith [strip.1], by linarith [strip.2]⟩
  obtain ⟨x, hx, trace⟩ := collar_of_close hc ha e.opposite e.radius φ sign strip small hs.le
  have sub : Icc 0 t ⊆ Icc 0 (1 / 64 : ℝ) := Icc_subset_Icc_right (small.trans (by norm_num))
  obtain ⟨v, hv, xe⟩ := (trace t (sub ⟨abs_nonneg _, le_rfl⟩)).2.2
  let b := birth uC zC uA zA e.radius
  have dv (i : Fin 2) : |(x t) i - b φ i| ≤ t / 4 := by
    have c := congrFun xe i
    change (x t) i = b φ i + t * v i at c
    rw [c, add_sub_cancel_left, abs_mul, abs_of_nonneg (abs_nonneg (φ - a))]
    have bound : |v i| ≤ 1 / 4 := abs_le.mpr ⟨hv.1 i, hv.2 i⟩
    linarith [mul_le_mul_of_nonneg_left bound (abs_nonneg (φ - a))]
  obtain ⟨motionR, motionZ⟩ := launch_displacement hc ha e.opposite (φ := φ) unit
  obtain ⟨anchorR, anchorZ⟩ := launch_error hc ha e.opposite unit
  have anchor (i : Fin 2) (center : ℝ)
      (motion : |b φ i - b a i| ≤ 2 / 10 ^ 12 + t / 6)
      (atCenter : |b a i - center| ≤ 2 / 10 ^ 12) :
      |(x t) i - center| ≤ e.allowance := by
    have d := abs_sub_le ((x t) i) (b φ i) center
    have f := abs_sub_le (b φ i) (b a i) center
    have w : 4 / 10 ^ 12 + e.width * (1 / 4 + 1 / 6) ≤ e.allowance := by
      unfold MirrorEndpoint.width MirrorEndpoint.allowance; split <;> norm_num
    have ht : t ≤ e.width := hφ
    linarith [dv i]
  have hr : |b a 0 - e.start.point.x / (2 : ℝ)^80| ≤ 2 / 10 ^ 12 := by
    let c := blend e.radius (seedRadius false e.opposite) (seedRadius true e.opposite)
    have d := abs_sub_le (b a 0) c (e.start.point.x / (2 : ℝ)^80)
    change |b a 0 - c| ≤ _ at anchorR
    have nom : |c - e.start.point.x / (2 : ℝ)^80| ≤ 1 / 10 ^ 12 := e.nominal
    linarith
  have hz : |b a 1 - e.start.point.y / (2 : ℝ)^80| ≤ 2 / 10 ^ 12 := by
    have z : e.start.point.y = 0 := by cases e <;> rfl
    rw [z, Int.cast_zero, zero_div, sub_zero]
    exact anchorZ.trans (by norm_num)
  have squared {y : ℝ} (h : |y| ≤ e.allowance) : y^2 ≤ e.allowance^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have budget : 2 * e.allowance^2 ≤ (e.start.radius / (2 : ℝ)^80)^2 := by
    cases e <;> norm_num [MirrorEndpoint.allowance, MirrorEndpoint.opposite, MirrorEndpoint.start]
  refine ⟨sign, x, hs, phase, hx, fun s h => (trace s (sub h)).1.mono sub, ?_⟩
  unfold InStartBall
  linarith only [squared (anchor 0 _ motionR hr), squared (anchor 1 _ motionZ hz), budget]

/-- One nested pair of Q-16 tori realizes the entry theorem at all eight certified endpoints. -/
theorem exists_nested_section_entry :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ (e : MirrorEndpoint) (φ : ℝ), |φ - azimuth e.opposite| ≤ e.width →
        SectionEntry e uC zC uA zA φ := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,_,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,fun e _ h =>
    transfer_to_start (by simpa using cC) (by simpa using cA) e h⟩

end PlasmaLean.Design.DommaschkMirrorLaunch
