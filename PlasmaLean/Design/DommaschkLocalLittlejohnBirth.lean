/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkTrappedBirthCoordinates
public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnLocal

/-! # Genuine local QA2R guiding-centre orbits on open sets of trapped reference births -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkLocalLittlejohnBirth
open Set Fields Contract Contract.TrappedBirthCoordinates Kinetic.GCLittlejohn
open DommaschkCartesianAngleFlow DommaschkFirstMirrorWell DommaschkSignedObservable
open DommaschkSignedTraceDomain DommaschkSignedMirrorBand DommaschkFirstMirrorLaunchSign
open Certificates.PositionFrameSlabs (Plane State Step)
set_option maxRecDepth 12000

abbrev vacuumRegion := Kinetic.VacuumLittlejohnLocal.regular B CylAlgebra.domain

theorem parallel (m q v : ℝ) {x : Space} (hx : x ∈ vacuumRegion) :
    BstarPar m q B v x = ‖B x‖ :=
  Kinetic.VacuumLittlejohnLocal.vacuum_parallel (DommaschkQA2R.field_vacuum _) hx m q v

/-- The reference birth admits a physical Littlejohn orbit with regular denominators
throughout some positive time interval. The residence time may depend on the birth. -/
def localBirths (m q : ℝ) (S : Set GCBirth) (energies pitches : Set ℝ) : Set GCBirth :=
  {b | b ∈ trappedReference B m S energies pitches ∧ 0 < m ∧ q ≠ 0 ∧
    ∃ T > 0, ∃ y, GCBirthOrbitOn B m q b y T ∧ ∀ t ∈ Icc 0 T,
      (y t).1 ∈ vacuumRegion ∧ BstarPar m q B (y t).2 (y t).1 = ‖B (y t).1‖ ∧
        0 < BstarPar m q B (y t).2 (y t).1}

theorem interior_of_reference {m q : ℝ} {S : Set GCBirth} {energies pitches : Set ℝ}
    {p : GCBirth} (hm : 0 < m) (hq : q ≠ 0) (hx : p.1 ∈ vacuumRegion)
    (here : p ∈ interior (trappedReference B m S energies pitches)) :
    p ∈ interior (localBirths m q S energies pitches) := by
  let W := interior (trappedReference B m S energies pitches) ∩
    (fun z : GCBirth => z.1) ⁻¹' vacuumRegion
  have op : IsOpen W := isOpen_interior.inter
    ((Kinetic.VacuumLittlejohnLocal.isOpen_regular (DommaschkQA2R.field_vacuum _)).preimage
      continuous_fst)
  apply interior_maximal _ op ⟨here, hx⟩
  intro b hb
  obtain ⟨T, pos, y, ode, stays⟩ := Kinetic.VacuumLittlejohnLocal.exists_orbit
    (DommaschkQA2R.field_vacuum _) m q b hb.2
  exact ⟨interior_subset hb.1, hm, hq, T, pos, y, ode, fun t ht =>
    ⟨(stays t ht).1, parallel m q _ (stays t ht).1, (stays t ht).2⟩⟩

def BothSigns (x : Space) : Prop :=
  ∀ (m q e h : ℝ), 0 < m → q ≠ 0 → 0 < e → h ∈ Icc (height false : ℝ) (height true) →
    ∀ (negative : Bool) (S : Set GCBirth) (energies pitches : Set ℝ),
      lift B m x e h negative ∈ interior S → e ∈ interior energies → 1 / h ∈ interior pitches →
        lift B m x e h negative ∈ interior (localBirths m q S energies pitches)

theorem from_path {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {φ : ℝ} (p : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (band : Branches y) (small : |φ| < 316 / 64) : BothSigns (point y φ) := by
  intro m q e h hm hq he hh neg S energies pitches supp energy pitch
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have time : φ ∈ Icc (-(n : ℝ) / 64) (n / 64) :=
    ⟨by linarith [(abs_lt.mp small).1], by linarith [(abs_lt.mp small).2]⟩
  have regular := in_regular (region φ time) φ
  apply interior_of_reference hm hq ⟨regular.1, field_ne_zero regular⟩
  exact DommaschkTrappedBirthCoordinates.from_path p reached region band small
    m e h hm he hh neg S energies pitches supp energy pitch

end PlasmaLean.Design.DommaschkLocalLittlejohnBirth
