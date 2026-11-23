# Testing a Hamiltonian bounce band on the physical field

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-53` |
| Title | Testing a Hamiltonian bounce band on the physical field |
| Kind | Method for N-49 and N-51 |
| Addresses | G-6, G-10, Q-1, Q-35, Q-22 |
| Depends on | N-49, N-51, N-44 for the independent pressure test |
| Dependency requirement | Identify one regular family of two-turning-point bounces and the correct reduced measure and time for the chosen physical field. |
| Produces | A reproducible band selection, physical radial and time bounds, and a decision on a C2 certificate. |
| Difficulty | Research. Turning points, the reduction and the error bound must hold throughout the proposed population. |
| Status | Proposed physical test. |
| Lean evidence | VolumeChart.exists_inverse_square_orbits covers the periodic coordinate model. |
| Audit evidence | Physical reduction open. |
| Last updated | 23 November 2026 |

## What the first experiment measures

**Sourced theorem and conditional inference.** Burby, MacKay and Naik describe regular guiding-centre bounce dynamics at fixed longitudinal action with a reduced Hamiltonian and magnetic flux form. If the field W, density σ and time convention used in N-51 give ι_Wσ = ±dH for a globally single-valued H on the annulus, the signed period vanishes by integration. Verify the identity on the chosen physical reduction first. In that case use the computed period as a consistency check and search for two regular winding levels. Measure their excursions in physical radius, minimum distance from a separatrix, and the birth population they enclose. Otherwise the signed period can still obstruct a winding-one level. [Isodrastic magnetic fields, §1](https://arxiv.org/html/2211.13367)

## Acceptance and competing tests

Fix thermal ion and electron parameters, nonempty trapped populations and their coverage, a physical radial tolerance, and the required time in seconds before selecting the best band. Alphas can be reported separately. Identify the physical ε, timescale, common volume, margin and corrector bounds. Include model reduction and higher-order residuals in the time budget. To use the result for C5, bound the loss carried by the complement and connect these estimates to a heat budget. Compare the resulting time to the direct first-order drift bound on the same population.

Run the Q-31 interface sign screen alongside this work. A uniform sign margin at vacuum gives a reason to test the exterior construction, sheet current, transform and remainder after a nonzero pressure step. A certified obstruction rejects this sufficient criterion. Field-specific equilibrium and stability remain independent proof obligations.
