/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorSectorFlow
public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Field strength on wide sectors of the original QA2R birth annulus -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkWideBirthBounds
open Set Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open DommaschkMirrorLaunch DommaschkFirstMirrorLaunchSign

def rLo (q : Bool) : ℝ := (if q then 89400 else 99517) / 100000 - 1 / 192 - 1 / 10 ^ 11
def rHi (q : Bool) : ℝ := (if q then 89548 else 99622) / 100000 + 1 / 192 + 1 / 10 ^ 11
def cosCentre (q : Bool) : ℝ := if q then -1 else 1

/-- The double-angle cosine varies quadratically around either symmetry
phase, whereas the sine changes by at most twice the angular displacement. -/
theorem angle_bounds (q : Bool) {φ : ℝ} (h : |φ - azimuth q| ≤ 1 / 32) :
    |Real.cos (2 * φ) - cosCentre q| ≤ 1 / 512 ∧ |Real.sin (2 * φ)| ≤ 1 / 16 := by
  let t := φ - azimuth q
  have ht : |t| ≤ 1 / 32 := h
  have hφ : 2 * φ = 2 * azimuth q + 2 * t := by unfold t; ring
  have hc : |Real.cos (2*t) - 1| ≤ 1 / 512 := by
    have bound : Real.sin t ^ 2 ≤ (1 / 32 : ℝ)^2 :=
      (Real.sin_sq_le_sq).trans (sq_le_sq.mpr (by simpa using ht))
    have low := sq_nonneg (Real.sin t)
    rw [Real.cos_two_mul, abs_le]
    constructor <;> nlinarith [Real.sin_sq_add_cos_sq t]
  have hs : |Real.sin (2*t)| ≤ 1 / 16 :=
    Real.abs_sin_le_abs.trans (by rw [abs_mul]; norm_num; linarith)
  rw [hφ, Real.cos_add, Real.sin_add]
  cases q
  · simpa [azimuth, cosCentre] using And.intro hc hs
  · simp only [azimuth, ite_true, show 2 * (Real.pi / 2) = Real.pi by ring,
      Real.cos_pi, Real.sin_pi, neg_one_mul, zero_mul, zero_add, sub_zero, cosCentre]
    exact ⟨by rwa [show -Real.cos (2*t) - -1 = -(Real.cos (2*t)-1) by ring, abs_neg],
      by simpa using hs⟩

/-- The polynomial certificate covers this explicit radial/vertical box with
its physical double-angle columns. -/
def Sector (q : Bool) : Prop :=
  ∀ R z φ : ℝ, R ∈ Icc (rLo q) (rHi q) → |z| ≤ 1 / 192 + 1 / 10 ^ 11 →
    |φ - azimuth q| ≤ 1 / 32 →
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖ < height false

theorem birth_in_box {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A
      (1 / 10 ^ 12)) (q : Bool) {u φ : ℝ} (hu : u ∈ Icc (11 / 25 : ℝ) (27 / 50))
    (small : |φ - azimuth q| ≤ 1 / 32) :
    let b := birth uC zC uA zA u φ
    b 0 ∈ Icc (rLo q) (rHi q) ∧ |b 1| ≤ 1 / 192 + 1 / 10 ^ 11 := by
  obtain ⟨hr, hz⟩ := section_box hc ha q hu
  obtain ⟨dr, dz⟩ := launch_displacement hc ha q (φ := φ) (u := u)
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  change _ ∈ Icc _ _ ∧ |blend _ _ _| ≤ _
  rw [abs_le] at dr dz hz ⊢
  constructor
  · change blend _ _ _ ∈ Icc _ _
    cases q <;> change _ ∈ Icc _ _ at hr <;> constructor <;>
      norm_num [rLo, rHi] <;> linarith [hr.1,hr.2,dr.1,dr.2]
  · constructor <;> linarith [hz.1, hz.2, dz.1, dz.2]

/-- Both wide angular sectors and the entire deep radial strip on a single
pair of original nested embedded invariant tori. -/
def CommonBirths : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC)
      DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA)
      DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ (q : Bool) (u φ : ℝ), u ∈ Icc (11 / 25 : ℝ) (27 / 50) → |φ - azimuth q| ≤ 1 / 32 →
      let b := birth uC zC uA zA u φ
      ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint (b 0) φ (b 1))‖ < height false

theorem from_sectors (sectors : ∀ q, Sector q) : CommonBirths := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),?_⟩
  intro q u φ hu hφ
  obtain ⟨h1,h2⟩ := birth_in_box (by simpa using cC) (by simpa using cA) q hu hφ
  exact sectors q _ _ _ h1 h2 hφ

end PlasmaLean.Design.DommaschkWideBirthBounds
