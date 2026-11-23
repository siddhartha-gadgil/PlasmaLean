# Embeddedness from irrational section dynamics

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-52` |
| Title | Embeddedness from irrational section dynamics |
| Kind | Method and proof for N-48 |
| Addresses | Q-36, G-1, G-11 |
| Depends on | N-48, N-33, N-34 |
| Dependency requirement | A field torus with a winding-one polar lift, irrational transform, jointly C² profiles and a magnetic field locally C¹ at each image point. |
| Produces | Embedded C1 on the exact rational stellarator torus and the Dommaschk pair, including the Q-16 witnesses. |
| Difficulty | The section proof uses density and winding. The dynamical step uses a Grönwall estimate on the torus image. |
| Status | Proved in Lean for every Q-36 example. |
| Lean evidence | `FieldTorus.embeddedTorus_of_irrational`, `CurrentFreeTransform.embedded_of_irrational` and the applications below. |
| Audit evidence | AF-1 concerns the bare predicates. The new proof has compiled examples and counterexamples. It postdates the audit at `6ceca0e`. |
| Last updated | 23 November 2026 |

## Reusable result

Fix a geometric toroidal angle φ and write k(θ) = (R(θ,φ), z(θ,φ)). Suppose an equality k(x) = k(y) propagates after adding 2πι to both arguments, and a vanishing section tangent propagates under the same shift. If ι is irrational, the section is C¹ and its polar angle about an avoided point winds once, then k is injective modulo 2π and its derivative is everywhere nonzero. The two propagation assumptions enter the injectivity and immersion proofs separately. [Section lemmas](../../PlasmaLean/Theory/Contract/IrrationalSection.lean)

- If k(x) = k(x+d), the closed condition k(y) = k(y+d) holds along the forward orbit of x and hence at every y. For a lift Θ of the polar angle, Θ(y+d)−Θ(y) is then continuous with values in 2πℤ, hence constant. The periodic function Θ(y)−y attains a maximum. The translated function has the same maximum. Its constant difference from the original function must therefore be zero, so the polar-angle increment equals d. Thus d belongs to 2πℤ. The Lean declarations are `periodic_mem_closed_of_irrational_return`, `PoloidalAngle.section_period` and `PoloidalAngle.sections_injective_of_irrational_return`. [Section proof](../../PlasmaLean/Theory/Contract/IrrationalSection.lean) · [Mathlib's irrational rotation density](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/AddCircle/DenseSubgroup.html)
- If k′ vanishes at x, continuity and the same dense forward orbit force k′ to vanish everywhere. A constant section would have every d as a period, contradicting the preceding period calculation. This proves `PoloidalAngle.sections_immersed_of_irrational_return`. [Immersion proof](../../PlasmaLean/Theory/Contract/IrrationalSection.lean)

For a `FieldTorus`, the toroidal component is nonzero. Normalize the field so time equals geometric toroidal angle. Local C¹ regularity at the compact image gives a Lipschitz bound there. Grönwall bounds the distance between the endpoints of any two field-line segments after a full turn by a constant times their initial distance. This propagates coincident points, and applying the bound to difference quotients propagates a zero tangent. The estimates are `FieldTorus.section_return_chord` and `FieldTorus.section_return`. [Flow proof](../../PlasmaLean/Theory/Contract/SectionFlow.lean)

With jointly C² profiles and a winding-one `PoloidalAngle`, `FieldTorus.embeddedTorus_of_irrational` concludes `EmbeddedTorus R z` for the specified parametrization. The family version `CurrentFreeTransform.embedded_of_irrational` preserves the surface set and its current and transform bounds. [Torus and family theorems](../../PlasmaLean/Theory/Contract/IrrationalTorus.lean)

## Certified examples

| Example | Lean result and scope |
| --- | --- |
| Rational stellarator torus A | `ExactTorus.embeddedCurrentFreeTransform` gives embedded C1 on each exact witness. `rationalStellarator_embeddedCurrentFreeTransform` supplies such a witness at zero current and positive irrational transform. [Proof](../../PlasmaLean/Design/RationalStellaratorEmbedded.lean) |
| Dommaschk tori C and A | `torusC_embedded` and `torusA_embedded` apply to the exact KAM profiles. `dommaschkC_embedded_C1` and `dommaschkA_embedded_C1` are the individual C1 certificates. [Proof](../../PlasmaLean/Design/DommaschkKamEmbedded.lean) |
| Nested pair and Q-16 | `dommaschk_nested_embedded_C1` gives zero current and common transform bound 1193/5000 on the same ray-ordered pair. `dommaschk_Q16_embedded` retains both Boozer hypotheses, strip distances and off-QA defect bounds of 0.0063 and 0.009 times the respective absolute transforms. `dommaschk_Q16_strong_embedded` gives the uniform one-percent bound on that pair. [Proof](../../PlasmaLean/Design/DommaschkKamEmbedded.lean) |

The loop-current consistency checks also use these embedded witnesses. `rationalStellarator_embedded_fixture` and `rationalStellarator_embedded_ball_fixture` recover zero current on the rational torus. `dommaschk_nested_embedded_current_eq_zero` recovers zero current on the ordered Dommaschk pair by Stokes in the meridian half-space. [Rational fixtures](../../PlasmaLean/Sanity/ContractLoopCurrentFixture.lean) · [Dommaschk fixture](../../PlasmaLean/Design/DommaschkKamEmbedded.lean)

## Boundary case and checks

At rational transform ι = 0, take the toroidal wire field and a circular section about (1,0) of radius 0 < a < 1. Reparametrize its polar angle by θ−sin θ. The lift still winds once and the profiles are C², but both section derivatives vanish at θ = 0. Lean proves `stationary_periodicC2Torus`, `stationary_iotaOnTorus` and `stationary_not_embeddedTorus`. The failure is in the parametrization, even though its geometric image is a circular torus. This explains why the bare contract predicates still require a separate embeddedness argument. [Sanity fixture](../../PlasmaLean/Sanity/EmbeddedSurfaces.lean)

The workstation default build includes the section, flow, torus, rational stellarator and sanity modules. Its axiom audit checked 53,360 project declarations. A separate build and axiom audit of the on-demand targets covered 59,706 declarations, including the Dommaschk applications. Both passed with only `propext`, `Classical.choice` and `Quot.sound`. The earlier domain audit records the limitation of the bare predicates at its pinned revision. [Audit](../audit/2026-11-23-refresh-audit.md)
