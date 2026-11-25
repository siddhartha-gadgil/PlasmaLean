# The full radial birth family through 240 slabs in both directions

For every original launch in the phase-zero rectangle, one signed QA2R field line through its actual birth now obeys the ordinary ODE on \([-239/64,239/64]\). This covers all phases \(|\phi|\le2^{-19}\), all radius labels \(0.470\le u\le0.478\), and all four section seed balls on one pair of nested embedded tori. The field strength stays strictly below \(132/125\) throughout \([-237/64,237/64]\). The normalized parallel speed exceeds \(1/12\) throughout that segment for all heights at or above the lower archived value. [Passing-speed proof](radial-passing-speed-core.md)

In the closed archived height band, the normalized travel time measured from the original birth is continuous and strictly increasing in the field-line angle. Its increments lie between one half and fifteen times the angular increment. Every signed time with \(|\tau|\le1941503/1048576\), about 1.852, is attained at a unique position on the segment. This describes the parallel motion along the certified field line. A particle drift bound is still required for thermal radial confinement. [Physical clock](original-radial-passing-time.md)

The recorded join uses 1,920 independently signed ODE slabs. The stronger field threshold uses 1,896 signed row bounds, joined on the true trajectories. The physical, field and clock keys respectively are `048b12662bd01daa529f8b819c5cd7b70e61c9ac11052e4bac118a5a1947642b`, `bde381a7e8859cf276138837a0cd6b2ebfb128e14c12db163dbf0eea81717fbd` and `7fe7d4729a2953fcc156d01aa871845c00f150c24c08b37fe53bdbaff15773cf`. Each receipt passed the standard axiom audit. The 332-row campaign continues toward the mirror caps. [Four-tile trajectory join](../../scripts/dommaschk_kam/verify_ribbon_through_chains.py)

## Replay

Run the [passing-core](radial-passing-speed-core.md) and [travel-time](original-radial-passing-time.md) commands with `--count 240`, passing the resulting through, core and clock receipts in that order. The accepted declarations are `DommaschkRadialRibbonThrough240.from_seed`, `DommaschkRadialPassing240Core237.from_nested_tori` and `DommaschkRadialPassingTime240Core237.from_nested_tori`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-200 |
| Kind | Unconditional physical continuation and normalized flight-time checkpoint |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-175, N-191, N-194, N-197 |
| Dependency requirement | The first 240 joined signed ODE slabs on all four tiles and the physical field gap through row 237. |
| Produces | A field-line ODE through ±239/64, positive-speed core through ±237/64 and a common two-sided travel time. |
| Status | Lean verified at the stated widths on all original births in the small sector. |
| Last updated | 25 November 2026 |
