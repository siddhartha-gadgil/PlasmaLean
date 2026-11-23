# Boundary variation of a harmonic field and the Euclidean realization of quasisymmetry

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-50` |
| Title | Physical boundary deformations of a vacuum seed |
| Kind | Method for N-32 and N-34 |
| Addresses | Q-34, Q-32, Q-24, G-1, G-10 |
| Depends on | N-34 and N-33 for the Dommaschk field and boundary candidates, N-32 for the fixed-field QS obstruction |
| Dependency requirement | Match the marked smooth solid torus and normalized tangent harmonic field to the hypotheses of the shape theorem. The exact-QS investigation additionally uses the local handoff's free-periodic ansatz. |
| Produces | A test of Roussel's curvature condition and a separate infinitesimal test of the prescribed-domain QS ansatz |
| Difficulty | Research. Boundary regularity, gauge freedom and uniform curvature bounds determine the first test. Euclidean development adds global constraints to the second. |
| Status | Exploratory. Applicability to a Dommaschk torus is open. |
| Lean evidence | None for shape differentiation or the Euclidean deformation problem |
| Audit evidence | Not audited |
| Last updated | 23 November 2026. Proposed following the discussion of geometric alternatives to coefficient search. |

## Purpose and scope

For a smooth Euclidean solid torus, fixing a longitudinal circulation selects the unique curl-free, divergence-free field tangent to the boundary with that period. This follows from the one-dimensional space of harmonic Neumann fields on the solid torus. Two design questions follow. If the boundary can move, which variations change a physical field-line observable? If the embedded domain is prescribed, which quasisymmetry ansatz can realize its already determined harmonic field? Normalize the boundary angles in turns and take round-trip rotation numbers in turns per toroidal transit. [Roussel, §1](https://arxiv.org/html/2406.08178v1)

## Sources, dependencies and evidence

**Sourced theorem.** Roussel differentiates the marked boundary return map with respect to the embedding. For the standard round axisymmetric embedding of Theorem 3.1, every first variation vanishes. Theorem 4.1 assumes an admissible smooth embedding, a straight boundary field $B=χ(∂_φ+ω∂_θ)$ with Diophantine $ω$, and $\mathrm{II}(B,B^\perp)$ nowhere zero. Here $B^\perp$ is the positive quarter-turn in the oriented boundary tangent plane. Every smooth first variation of the circle map can then be obtained. Tangential relabellings already generate the zero-mean variations in straight coordinates. The normal deformation with nonzero mean is the physically interesting part. [Roussel, Theorems 3.1 and 4.1, Remark 4.2 and Proposition 4.3](https://arxiv.org/html/2406.08178v1)

**Compiled Lean theorem.** On demand, `dommaschk_Q16_vacuum` gives two nested invariant tori of one vacuum field with bounds on transform and per-torus QA defect. Applying the shape theorem needs a separate identification of the enclosed smooth marked domain, its normalized harmonic field and its admissible embedding. [Q-16 theorem](../../PlasmaLean/Design/DommaschkKamQ16.lean)

## Theory development and readiness

**Q-34, proposed test.** Choose C or A, fix the oriented section and the circulation, and translate the certified transform into the paper's coordinate convention. Check smooth embedding and transverse flow in those coordinates. Screen the mixed second fundamental form over the whole boundary. A strict uniform bound away from zero would discharge the curvature hypothesis. A certified sign change on the connected torus, or a certified zero, would rule out this sufficient condition for the seed. A near-zero grid value calls for refinement. The same surface derivatives can serve N-44's distinct interface test.

If the hypotheses hold, construct one normal boundary displacement with nonzero mean return-map response. Compare the response to a nearby harmonic-field solve and estimate a nonlinear remainder before making any finite-displacement claim. Follow any predicted improvement in particle drift inside the domain with its own calculation. If the sufficient condition fails, the general shape derivative still gives a way to test selected physical deformations. Use the round torus and a pure change of boundary coordinates as controls.

**Q-24, exploratory test on a fixed domain.** In the free-periodic sector of the complex-geometry handoff, linearize the metric flatness equation at an explicit Euclidean seed. Fix the circulation and marking, impose boundary matching and infinitesimal rotational and translational holonomy constraints, and quotient out reparametrizations. Identify a genuinely distinct infinitesimal QS solution or prove a rigidity statement under this ansatz. A surviving mode still needs nonlinear continuation, an injective developing map and a nonzero transform to give a new stellarator example. The fixed-domain uniqueness statement makes it important to specify whether the mode changes the generator, coordinates or domain. [Handoff, §§2–3 and 8–10](../../sources/complex_geometry_handoff.pdf) · [N-32](holomorphic-qs-brief.md)

## Outputs and next dependencies

Prioritize the boundary hypothesis test independently of N-49's particle calculation. A nonzero physical shape response provides a candidate direction for Q-32. A rigidity result in the fixed-domain problem would delimit Q-24. Neither calculation alone supplies the interior particle or finite-pressure estimates. Carry comparisons of candidate fields forward only with their region, perturbation size and observable specified.
