# Stellarator conditions after the first-well sector proof

**25 November 2026.** The Dommaschk QA2R vacuum field satisfies C1 on two nested embedded tori. The new C2 evidence gives a connected family of genuine magnetic wells on these same tori's interpolated birth chart. Extending that result to thermal confinement requires a quantitative dynamical estimate on particles that drift between field lines. [Physical sector theorem and kernel receipts](completed-original-radial-sector.md) · [Earlier assessment and geometric questions](stellarator-conditions-and-geometric-questions.md)

| Condition | What Lean establishes | What the application still needs |
| --- | --- | --- |
| C1 · current-free rotational transform | The two Dommaschk tori have zero net toroidal current and absolute transform at least 0.2386. The rational vacuum stellarator also has an embedded torus satisfying C1. | Retain the transform and current bounds in a finite-pressure candidate. [Dommaschk](../../PlasmaLean/Design/DommaschkKamEmbedded.lean) · [Rational stellarator](../../PlasmaLean/Design/RationalStellaratorEmbedded.lean) |
| C2 · thermal-particle confinement | Field-line statements only (prerequisites for C2; no guiding-centre or particle statement): for every phase within \(2^{-19}\) of zero and interpolation label \(0.470\le u\le0.478\), an actual field line has two transverse first mirrors around its birth throughout a common height band. At a fixed certified height a compact connected set realizes the target action across the whole phase sector. A separate, short signed field-line interval stays below mirror strength at every phase for \(0.44\le u\le0.54\). | Establish the required phase coverage of complete wells, control the change of action for physical guiding centres, and bound the fraction of a specified thermal population that remains within an allowed excursion for a specified time. [Connected levels](completed-original-radial-sector.md) · [Full-period short interval](periodic-original-fieldline-collar.md) |
| C3 · finite-pressure MHD stability | A sufficient pointwise curvature criterion for a pressure interface fails on part of torus A. The energy estimate on a cylinder supplies a benchmark. | Establish an energy bound for an actual finite-pressure toroidal equilibrium, or find an unstable displacement there. [Curvature obstruction](dommaschk-interface-obstruction.md) · [Cylinder theorem](cylinder-interface-stability.md) |
| C4 · equilibrium and nested surfaces | The smooth vacuum field satisfies force balance and carries the two certified invariant tori. | Establish the desired volume-filling family and a compatible finite-pressure equilibrium. [Candidate results](../../README.md) |
| C5 · thermal performance | Transport and power-balance benchmarks are available on other models. | Link losses for the same stellarator to a thermal operating window. The physical scales, time and population targets remain open by choice. [Original contract and benchmark results](stellarator-conditions-and-geometric-questions.md) |

## What the new C2 result changes

The certificate joins **2,656 signed ODE slabs** into four parameter-dependent trajectories on \([-331/64,331/64]\). At height \(h_U\), the exact-action result permits every continuous phase-dependent prescription between \(J_*-0.0021\) and \(J_*+0.0019\). For any positive action tolerance, the admissible radial labels have a uniformly positive length over the sector. Translating this sampling statement into a thermal population fraction requires a birth distribution and its relation to the launch labels. [Precise quantifiers, variable-height extension and receipts](completed-original-radial-sector.md)

The two radial faces give a concrete target for dynamics. For heights between \(h_U-0.000002\) and \(h_U\), a sufficient dimensionless budget is
\[
 |J(0)-J_*|+\sup_{t\le T}|J(t)-J(0)|\le0.000996 .
\]
The path starts inside the strip. At a possible first exit the phase and height must lie in the certified window, and the observed action must come from the first well through the actual birth on that face. Under those hypotheses the radius stays inside through \(T\). Deriving the drift term for a physical guiding centre is the main conceptual step. More ODE certificates can test the two-face inequalities on other phases and improve their margins. [First-exit theorem and exact bounds](varying-height-first-exit.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-210 |
| Kind | Dated assessment and patch to N-69 |
| Addresses | G-8, G-10, Q-20, Q-31, Q-35 |
| Depends on | N-69, N-198, N-199, N-201, N-202, N-203, N-205, N-206 |
| Dependency requirement | The C1, physical first-well and two-face conclusions refer to the common QA2R construction. |
| Produces | Updated status of C1–C5 and a precise action-drift target for C2. |
| Difficulty | The local certificate is complete. Phase coverage is an ongoing verified computation. The thermal drift and population estimates are research questions. |
| Status | Assessment of verified results and their outstanding physical hypotheses. |
| Lean evidence | `DommaschkCertifiedRadialSector.on_nested_tori`, `DommaschkPeriodicOriginalCollar.cartesian_field_line`, `DommaschkHeightBandActionExit.stays_inside` and the C1 declarations linked above. |
| Audit evidence | Workstation receipts of generated modules. `on_nested_tori` and `cartesian_field_line` are generated by `scripts/dommaschk_kam/` and are not in the repository, its build or `scripts/check_axioms_heavy.lean`. `cartesian_field_line` takes closeness hypotheses; the unconditional collar on the certified tori is the generated `DommaschkPeriodicOriginalCollar.original_collar`. `stays_inside` assumes `faces` (discharged only in generated modules), `Observes` (phase within 2⁻¹⁹ and height within 2·10⁻⁶ of `h_U` at every possible exit) and `drift`, none established for a particle. [Audit of 25 November 2026](../audit/2026-11-25-refresh-audit.md) (AW-H1, AW-M9) |
| Patches | N-69, C2 progress and next research steps. |
| Last updated | 25 November 2026 |
| Patched by / Alternatives | [N-214](label-drift-and-sector-scales.md): first quantitative drift statement and the scales that the local sector cannot meet for thermal particles |
