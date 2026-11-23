/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkInterfaceArcOrientation

/-!
# An embedded exact torus A with a point obstructing the pressure-step sign

The established Q-16 existence and embeddedness certificates provide the same
analytic surface whose cylindrical metric and curvature rows occur here.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkInterfaceArcWitness

open PlasmaLean.Theory.KAM WEll1Z2 PlasmaLean.Forms
open PlasmaLean.Stability.InterfacePrincipalDirection
open KamNewton DommaschkInterfaceArcGeometry DommaschkInterfaceArcProfiles
open DommaschkInterfaceArcOrientation
open scoped RealInnerProductSpace

/-- There is an embedded exact torus A and a point of its θ = 0 arc where every
positive metric pairing has positive mixed curvature in the stated normal convention. -/
theorem exists_embedded_torus_obstruction :
    ∃ u z : FA, DommaschkKamA.ExactTorusA u z ∧ EmbeddedTorus (DommaschkKamC.RofC u) (Zof z) ∧
      ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ v,
        0 < pair (metricRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v →
        0 < pair (curvatureRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v := by
  obtain ⟨u, z, h⟩ := DommaschkKamA.exists_exactTorusA
  exact ⟨u, z, h, DommaschkKamEmbedded.torusA_embedded h,
    DommaschkInterfaceArcBounds.exactTorusA_obstruction h⟩

/-- On the same embedded exact torus and at the same obstructing point, the chosen
Euclidean chart normal has positive pairing with the ray from the certified polar centre. -/
theorem exists_embedded_oriented_torus_obstruction :
    ∃ u z : FA, DommaschkKamA.ExactTorusA u z ∧ EmbeddedTorus (DommaschkKamC.RofC u) (Zof z) ∧
      ∃ φ ∈ Set.Icc 0 (1 / 5),
        0 < ⟪chartNormal (DommaschkKamC.RofC u) (Zof z) 0 φ,
          polarRay (DommaschkKamC.RofC u) (Zof z) 0 φ⟫ ∧
        ∀ v, 0 < pair (metricRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v →
          0 < pair (curvatureRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v := by
  obtain ⟨u, z, h, he, φ, hφ, ho⟩ := exists_embedded_torus_obstruction
  exact ⟨u, z, h, he, φ, hφ, normal_dot_polarRay_positive h hφ, ho⟩

end PlasmaLean.Design.DommaschkInterfaceArcWitness
