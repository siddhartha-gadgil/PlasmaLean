/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameChain
public import PlasmaLean.Theory.Fields.HilbertRetraction

/-! # Position validation on the closed Euclidean trial ball

The spatial derivative, Jacobian continuity and logarithmic norm may all be
checked on the same trial ball. This permits direct use of one physical tube
enclosure for both the regularity and the numerical steps of the argument.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameSlabs

/-- The quantitative Euclidean trial ball also provides the compact
regularity domain via its radial nonexpansive retraction. -/
def ballDomain : RegularityDomain where
  region := Metric.closedBall 0
  facts := fun {T} hT => ⟨isCompact_closedBall _ _, convex_closedBall _ _, Set.Subset.rfl,
    Fields.HilbertRetraction.radial T, Fields.HilbertRetraction.radial_retraction hT⟩

/-- One true ODE step requiring all field regularity only on the saved Euclidean
trial ball. The identical domain parameter works for `Chain.cartesian_trajectory`. -/
theorem physical_step_ball {lim : Limits} {s : State} {r : Step} {a : ℝ} {F : ℝ → Plane → Plane}
    {J : ℝ → Plane → Plane →L[ℝ] Plane} (ok : test lim s r = true)
    (bounds : FieldBounds s r a F J ballDomain) :
    Fields.TrajectorySlabs.Step F (physicalSlab s r a) (stateSet s) (stateSet (next r)) :=
  physical_step_on ok bounds

end PlasmaLean.Certificates.PositionFrameSlabs
