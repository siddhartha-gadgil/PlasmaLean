/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBirthVariationBounds
public import PlasmaLean.Design.DommaschkEndpointTraceFamily

/-! # First radial derivatives at the actual pilot birth on common Q-16 tori -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBirthVariation

open DommaschkMirrorLaunch DommaschkKamC KamNewton Theory.KAM WEll1Z2
open DommaschkPhysicalActionPanel DommaschkEndpointTraceFamily
open Contract Forms Fields.VacuumBoozer
open DommaschkEndpointSignedTrace Certificates.PositionFrameSlabs

/-- At the exact pilot section the approach duration is zero, so the joined physical
trajectory starts at the very birth whose radial derivative is enclosed below. -/
def PilotLine (c : Checkpoint) (uC zC uA zA : FA) : Prop :=
  Joined 0 ((c.length : ℝ) / 64)
    (coordinates.symm (birth uC zC uA zA (47/100) 0)) (stateSet c.forwardExit)
    (stateSet c.backwardExit) (physicalSlabs (MirrorEndpoint.start .q0r470) 0 c.forwardRows)
    (physicalSlabs (MirrorEndpoint.start .q0r470) 0 c.backwardRows)

theorem line_of_section {c : Checkpoint} {uC zC uA zA : FA}
    (h : c.Passage .q0r470 uC zC uA zA 0) : PilotLine c uC zC uA zA := by
  obtain ⟨s,a,_,_,start,_,line⟩ := h
  simpa only [MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ↓reduceIte, sub_zero,
    abs_zero, start, MirrorEndpoint.radius, show (470/1000 : ℝ) = 47/100 by norm_num,
    PilotLine] using line

/-- The two-dimensional tangent and both observable derivatives are at the same physical birth. -/
def Pilot (uC zC uA zA : FA) : Prop :=
  let x := fun u => birth uC zC uA zA u 0
  let v := tangent uC zC uA zA 0
  let f := fun u => fieldStrength (x u 0) 0 (x u 1)
  let w := fun u => arcDensity (x u 0) 0 (x u 1)
  let u : ℝ := 47/100
  HasDerivAt x v u ∧ v 0 ∈ Set.Icc (1045982 / 10 ^ 8) (1045983 / 10 ^ 8) ∧
    |v 1| ≤ 2 / 10 ^ 12 ∧ ∃ df dw, HasDerivAt f df u ∧ HasDerivAt w dw u ∧
      df ≤ -(1/144) ∧ 0 < dw ∧ -(w u/32) ≤ dw

theorem pilot_of_close {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A
      DommaschkKamA.z₀A (1 / 10 ^ 12)) : Pilot uC zC uA zA := by
  obtain ⟨hr,hz,vr,vz⟩ := geometry hc ha
  have velocity := birth_derivative uC zC uA zA 0 (47/100)
  obtain ⟨sf,sw,target⟩ := observable_slopes (φ := 0)
    (hasDerivAt_pi.mp velocity 0) (hasDerivAt_pi.mp velocity 1)
    (by linarith only [hr.1]) (by linarith only [hr.2]) (pilot_numerators hr hz vr vz)
  exact ⟨velocity, vr, vz, _, _, (differentiableAt_of_deriv_ne_zero
    (lt_of_le_of_lt sf (by norm_num)).ne).hasDerivAt,
    (differentiableAt_of_deriv_ne_zero sw.ne').hasDerivAt, sf, sw, target⟩

/-- A single pair of physical tori supplies the radial launch data and every prescribed
two-sided checkpoint at every admitted sector birth. -/
def CommonPilot (c : MirrorEndpoint → Checkpoint) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    Pilot uC zC uA zA ∧
    PilotLine (c .q0r470) uC zC uA zA ∧
    ∀ (e : MirrorEndpoint) (φ : ℝ), |φ - azimuth e.opposite| ≤ e.width →
      (c e).Passage e uC zC uA zA φ

theorem common_pilot (c : MirrorEndpoint → Checkpoint)
    (each : ∀ (e : MirrorEndpoint) {uC zC uA zA : FA} {φ : ℝ},
      SectionEntry e uC zC uA zA φ → (c e).Passage e uC zC uA zA φ) : CommonPilot c := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  have paths (e : MirrorEndpoint) (φ : ℝ) (h : |φ - azimuth e.opposite| ≤ e.width) :=
    each e (transfer_to_start (by simpa using cC) (by simpa using cA) e h)
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),pilot_of_close (by simpa using cC)
      (by simpa using cA), line_of_section (paths .q0r470 0 (by norm_num [MirrorEndpoint.width,
        MirrorEndpoint.opposite, azimuth])), paths⟩

end PlasmaLean.Design.DommaschkBirthVariation
