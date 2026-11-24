/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkLocalLittlejohnBirth
public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnWindow

/-! # One time interval for both signed QA2R birth populations -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCommonLittlejohnTime
open Set MeasureTheory Fields Contract Contract.TrappedBirthCoordinates
open Kinetic.VacuumLittlejohnWindow
open DommaschkCartesianAngleFlow DommaschkFirstMirrorWell DommaschkSignedObservable
open DommaschkSignedTraceDomain DommaschkSignedMirrorBand DommaschkFirstMirrorLaunchSign
open Certificates.PositionFrameSlabs (Plane State Step)
set_option maxRecDepth 12000

def signSet (negative : Bool) : Set GCBirth :=
  {p | if negative then p.2.1 < 0 else 0 < p.2.1}

theorem signSet_open (negative : Bool) : IsOpen (signSet negative) := by
  have cv : Continuous (fun p : GCBirth => p.2.1) := continuous_fst.comp continuous_snd
  cases negative
  · exact isOpen_lt continuous_const cv
  · exact isOpen_lt cv continuous_const

/-- Each sign can have its own support. Both signs use the same strictly positive horizon. -/
def UniformAt (x : Space) : Prop :=
  ∀ (m q e h d : ℝ), 0 < m → q ≠ 0 → 0 < e → h ∈ Icc (height false : ℝ) (height true) →
    0 < d → ∀ (S : Bool → Set GCBirth) (energies pitches : Set ℝ),
      (∀ neg, lift B m x e h neg ∈ interior (S neg)) →
      e ∈ interior energies → 1 / h ∈ interior pitches →
      ∃ T > 0, ∀ neg : Bool, ∃ W : Set GCBirth, IsOpen W ∧ lift B m x e h neg ∈ W ∧
        W ⊆ trappedReference B m (S neg) energies pitches ∩ signSet neg ∧
        ∀ b ∈ W, Control B m q T d b

theorem from_path {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {φ : ℝ} (p : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (band : Branches y) (small : |φ| < 316 / 64) : UniformAt (point y φ) := by
  intro m q e h d hm _hq he hh hd S energies pitches supp energy pitch
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have time : φ ∈ Icc (-(n : ℝ) / 64) (n / 64) :=
    ⟨by linarith [(abs_lt.mp small).1], by linarith [(abs_lt.mp small).2]⟩
  have cart := in_regular (region φ time) φ
  have strict := DommaschkTrappedBirthCoordinates.strict_at_birth band small hh
  have ref := DommaschkTrappedBirthCoordinates.from_path p reached region band small
  have each (neg : Bool) : ∃ T > 0, ∃ W : Set GCBirth, IsOpen W ∧
      lift B m (point y φ) e h neg ∈ W ∧
      W ⊆ trappedReference B m (S neg) energies pitches ∩ signSet neg ∧
      ∀ b ∈ W, Control B m q T d b := by
    obtain ⟨U, op, seed, T, pos, good⟩ := exists_control
      (DommaschkQA2R.field_vacuum _) m q (p := lift B m (point y φ) e h neg)
      (show point y φ ∈ DommaschkLocalLittlejohnBirth.vacuumRegion from
        ⟨cart.1, field_ne_zero cart⟩) hd
    refine ⟨T, pos, U ∩ interior (trappedReference B m (S neg) energies pitches) ∩ signSet neg,
      (op.inter isOpen_interior).inter (signSet_open neg),
      ⟨⟨seed, ref m e h hm he hh neg (S neg) energies pitches (supp neg) energy pitch⟩,
        (lift_values neg hm he strict).2.2.1⟩,
      fun _ hb => ⟨interior_subset hb.1.2, hb.2⟩, fun b hb => good b hb.1.1⟩
  choose T pos W op seed contained all using each
  refine ⟨min (T false) (T true), lt_min (pos false) (pos true), fun neg =>
    ⟨W neg, op neg, seed neg, contained neg, fun b hb => (all neg b hb).mono ?_⟩⟩
  cases neg
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- Both sign neighborhoods contribute to a single covered set in the predeclared reference. -/
def BandAt (x : Space) : Prop :=
  ∀ (m q e h d : ℝ), 0 < m → q ≠ 0 → 0 < e → h ∈ Icc (height false : ℝ) (height true) →
    0 < d → ∀ (S : Set GCBirth) (energies pitches : Set ℝ),
      (∀ neg, lift B m x e h neg ∈ interior S) → e ∈ interior energies →
      1 / h ∈ interior pitches → ∀ (ν : Measure GCBirth) [Measure.IsOpenPosMeasure ν],
      MeasurableSet (trappedReference B m S energies pitches) →
      ν (trappedReference B m S energies pitches) ≠ ⊤ →
      ∀ axis : Set Space, axis.Nonempty → IsCompact axis →
        ∃ T > 0, ∃ W : Set GCBirth, IsOpen W ∧ (∀ neg, lift B m x e h neg ∈ W) ∧
          (∀ neg, 0 < ν (W ∩ signSet neg)) ∧ GuidingCentreBand B m q axis ν S W energies pitches
            (ν.real W / ν.real (trappedReference B m S energies pitches)) d T

theorem UniformAt.band {x : Space} (u : UniformAt x) : BandAt x := by
  intro m q e h d hm hq he hh hd S energies pitches seed energy pitch ν _ meas finite axis ha comp
  obtain ⟨T, hT, subsets⟩ :=
    u m q e h d hm hq he hh hd (fun _ => S) energies pitches seed energy pitch
  choose W op occurs inside control using subsets
  let covered := W false ∪ W true
  have both (neg : Bool) : W neg ⊆ covered := by
    cases neg
    · exact subset_union_left
    · exact subset_union_right
  have openC : IsOpen covered := (op false).union (op true)
  have hit (neg : Bool) := both neg (occurs neg)
  refine ⟨T, hT, covered, openC, hit, fun neg => ?_, ?_⟩
  · exact (openC.inter (signSet_open neg)).measure_pos ν
      ⟨_, hit neg, (inside neg (occurs neg)).2⟩
  · apply guidingCentreBand ν hm hq ha comp hT hd openC ⟨_, hit false⟩ _ meas finite
    · exact fun b hb => hb.elim (control false b) (control true b)
    · exact union_subset (fun _ hb => (inside false hb).1) (fun _ hb => (inside true hb).1)

end PlasmaLean.Design.DommaschkCommonLittlejohnTime
