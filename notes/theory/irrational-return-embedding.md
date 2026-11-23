# Embeddedness from irrational section dynamics

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-52` |
| Title | Embeddedness from irrational section dynamics |
| Kind | Method and proof for N-48 |
| Addresses | Q-36, G-1, G-11 |
| Depends on | N-48, N-33, N-34 |
| Dependency requirement | A smooth section profile, single-valued differentiable return dynamics near its image, irrational transform and winding one about a point off the section. |
| Produces | Embedded C1 on the rational stellarator and the Dommaschk pair, with the existing witnesses. |
| Difficulty | Moderate for the circle argument. The smooth-flow bridge is the main implementation task. |
| Status | Proof on paper. Candidate applications pending. |
| Lean evidence | The default library supplies CurrentFreeTransform.embedded_of_sections. |
| Audit evidence | AF-1 for the previous surface specification. This development has no separate domain audit. |
| Last updated | 23 November 2026 |

## Reusable result

**Complete mathematical proof.** Let k be a C¹ closed plane curve avoiding a point about which its winding number is one. Suppose P is differentiable near its image and P(k(x)) = k(x+α), with α irrational in turns. If k(x)=k(x+d), iteration and density give k(y)=k(y+d) for every y. For a lift Θ of its polar angle in turns, Θ(y+d)−Θ(y) is then a continuous integer, hence a constant m. Iteration and boundedness of the periodic function Θ(y)−y give d=m. Thus k is injective modulo one. Similarly k′(x)=0 propagates by the chain rule to a dense set. Its derivative would vanish everywhere, contradicting the winding. A C² section family in geometric toroidal angle consequently satisfies the section criterion for a C² embedded torus.

The argument comes from the project review of 23 November. [Density of irrational multiples](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/AddCircle/DenseSubgroup.html)

## Application

Apply the section criterion to the rational stellarator and separately to Dommaschk C and A. Carry the same surfaces through the nested pair and the Q-16 defect statement. Their existing strict ray order already gives disjointness and a radial-segment statement. Identify the smooth normalised field-line equation on an open neighbourhood where the toroidal field is nonzero. Uniqueness propagates coincidence, and differentiability of the flow or its variational equation propagates a zero tangent. A derivative bound proving strict angular monotonicity is an alternative where easier. A Poincaré map need only exist locally around each trajectory used. Periodicity and Diophantine irrationality alone do not supply regularity of the profiles.
