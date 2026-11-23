# A positive principal direction obstructs the torus-A pressure-step test

## Metadata

| Field | Value |
| --- | --- |
| ID | N-55 |
| Kind | Proof and candidate obstruction, method for N-44 |
| Addresses | Q-31, G-4, Q-14, Q-20 |
| Depends on | N-33 for the exact Dommaschk tori, N-44 for the pressure-step criterion, N-52 for embeddedness |
| Dependency requirement | A tangent field of known direction, the oriented metric and curvature rows on a regular surface arc, and bounds on the true surface derivatives through order two. |
| Produces | A coordinate-independent obstruction and a verified single-point witness on the exact outer torus. |
| Difficulty | The determinant and its sign argument are elementary. Transferring signed second derivatives from a Fourier profile to the KAM torus requires cancellations in the packed coefficients. |
| Status | Reusable obstruction verified. Torus A verified on demand. Independent external interval calculation for torus C. |
| Lean evidence | `exists_obstruction_of_sign_change`, `gridJet_error`, `obstruction_of_close`, `exists_embedded_oriented_torus_obstruction`, `exactTorusA_field_normalDerivative_obstruction`. |
| Audit evidence | Bounded kernel checks on the full seed and an independent high-degree enclosure. The on-demand axiom audit checked 60,332 project declarations. |
| Last updated | 23 November 2026 |

## What the sufficient condition asks

For a selected family of exterior KAM graphs at a passive, fixed-flux interface, source §7 asks for a tangent variation Z with g(Y,Z) > 0 and II(Y,Z) < 0 everywhere. Here Y is the tangent vacuum field. With the source's orientation, the second fundamental form is IIᵢⱼ = −n·Xᵢⱼ for the unit normal n pointing out of the core. The sign condition would give positive pressure and a positive interface contribution for small steps. [Source, §§6–7](../../sources/fusion_complex_geometry_reproducibility/continuation_stability.tex) · [Original test, N-44](cylinder-interface-stability.md)

## A criterion for ruling out every variation

Let V be the field direction along a continuous surface arc. In a tangent basis form the two rows a = g(V,·) and b = H(V,·), where H uses any positive multiple of the chosen unit normal. Suppose det(a,b) has opposite signs at the ends, and a(V) and b(V) stay strictly positive on the arc. There is a point where b = λa with λ = b(V)/a(V) > 0. At that point every Z with g(V,Z) > 0 has H(V,Z) > 0. This conclusion also holds for any nonzero scalar multiple Y of V. It rules out the whole one-parameter family of source covectors, including after a change of angular coordinates. [General theorem](../../PlasmaLean/Theory/Stability/InterfacePrincipalDirection.lean)

## The Dommaschk calculation

Take θ = 0, geometric toroidal angle 0 ≤ φ ≤ 1/5 radians, V = (ι,1) and N = Xφ × Xθ for the positively wound meridian. Use Hᵢⱼ = −N·Xᵢⱼ. Evaluating the determinant needs all cylindrical moving-frame derivatives, including the radius contribution to Xφφ. The oracle angle in the seed is 2φ. Each geometric toroidal derivative therefore carries a factor of two. [Cartesian forms](../../PlasmaLean/Design/DommaschkInterfaceFundamentalForms.lean) · [Geometric profile errors](../../PlasmaLean/Design/DommaschkInterfaceJets.lean)

The following conservative bounds are rounded outward from a degree-four, one-cell external computation. The maximum in the second column is negative and the minimum in the third is positive.

| Torus | det at φ=0, upper bound | det at φ=1/5, lower bound | inf H(V,V), lower bound | inf g(V,V), lower bound |
| --- | ---: | ---: | ---: | ---: |
| A | −0.00002518 | 0.00003163 | 0.02269 | 1.00415 |
| C | −0.00004515 | 0.00000193 | 0.01717 | 0.98388 |

For A, Lean independently checks the necessary signs. It reconstructs the full packed Fourier sums through 161 toroidal frequencies, bounds a fourth-degree Taylor polynomial and its absolute fifth-order remainder, then adds the strip error of the true profile to all eleven physical jets. The row obstruction follows from the closeness retained in the public Q-16 result, so it applies to the outer profile returned there. The embedded existence theorem uses the very same surface as its arc witness. Lean also identifies Y with the physical field and proves positivity of its inner product with the directional derivative of the normalized normal. Throughout the arc, the chosen chart normal has positive dot product with the ray from the certified polar centre. Identifying that convention with the boundary orientation of a separately modelled plasma domain would require a domain and its orientation in Lean. For C the external calculation reads its own packed seed, uses its own rotation number and includes the certified profile error. Running the default degree-24 check also gives strict signs for both tori. [Compiled A certificate](../../PlasmaLean/Design/DommaschkInterfaceArcBounds.lean) · [Embedded witness](../../PlasmaLean/Design/DommaschkInterfaceArcWitness.lean) · [Reproducible script for A and C](../../scripts/dommaschk_kam/interface_arc.py)

## Decision for the pressure programme

Retire this strict first-order test for A. C shows the same obstruction in the independent enclosure. Seeking an exterior covector or refining the sheet current for this construction on those surfaces cannot remove the local sign conflict. A different interface or a stability argument controlling the *total* quadratic energy could still allow a pressure step. The Q-30 cylinder benchmark illustrates the second possibility under explicit multiplier and wall assumptions. Finite-pressure force balance, net current, transform and MHD stability for a single stellarator remain open. [Cylinder benchmark](cylinder-interface-stability.md)
