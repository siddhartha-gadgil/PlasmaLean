/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorFramePath

/-! # The first physical slab from each Dommaschk section entry -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkEndpointFirstSlab

open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkBounceField
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- A single accepted row gives the chain needed by the physical entry theorem. -/
theorem singleton {e : MirrorEndpoint} {r : Step} {lim : Limits}
    (h : test lim e.start r = true) : Chain lim e.start [[r]] 1 (next r) := by
  apply Chain.cons (m := next r) (n := 0)
  · simp [run, h]
  · exact .nil _

/-- Each birth that reaches the archived section state follows its first physical row. -/
theorem from_entry {e : MirrorEndpoint} {uC zC uA zA : FA} {φ sign : ℝ}
    {lim : Limits} {r : Step} (entry : SectionEntry e uC zC uA zA φ)
    (h : test lim e.start r = true)
    (bounds : FieldBounds e.start r 0 (DommaschkJacobian.euclideanFlow (azimuth e.opposite) sign)
      (DommaschkJacobian.velocityJacobian (azimuth e.opposite) sign) ballDomain) :
    FollowsFrames e uC zC uA zA φ sign 1 (next r) [r] :=
  followsFrames_of_bounds entry (singleton h) ⟨bounds, trivial⟩

/-- One common pair of physical surfaces supplies all angular sectors in a family of first rows. -/
def CommonBirths (row : MirrorEndpoint → Step) (sign : ℝ) : Prop :=
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ (e : MirrorEndpoint) (φ : ℝ), |φ - azimuth e.opposite| ≤ e.width →
        FollowsFrames e uC zC uA zA φ sign 1 (next (row e)) [row e]

/-- A family of first-row certificates lies on field lines launched from one common pair
of nested physical tori, for every angular birth in every specified endpoint sector. -/
theorem common_births (row : MirrorEndpoint → Step) (lim : MirrorEndpoint → Limits) (sign : ℝ)
    (accepted : ∀ e, test (lim e) e.start (row e) = true)
    (bounds : ∀ e, FieldBounds e.start (row e) 0
      (DommaschkJacobian.euclideanFlow (azimuth e.opposite) sign)
      (DommaschkJacobian.velocityJacobian (azimuth e.opposite) sign) ballDomain) :
    CommonBirths row sign := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, entries⟩ :=
    exists_nested_section_entry
  exact ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, fun e φ hp =>
    from_entry (entries e φ hp) (accepted e) (bounds e)⟩

end PlasmaLean.Design.DommaschkEndpointFirstSlab
