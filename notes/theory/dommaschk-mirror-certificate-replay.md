# Lean replay of the Dommaschk mirror certificates

## Metadata

| Field | Value |
| --- | --- |
| ID | N-61 |
| Kind | Certificate and implementation record |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-52, N-56–N-60 |
| Dependency requirement | The launch uses the nested Q-16 witnesses. The action and radial covers must describe the same signed physical trace. |
| Produces | Two physical launch sectors, directed quadrature packets, and exact radial replay. |
| Difficulty | The moving-frame trajectory and its first variation must stay within their certified bounds for a complete mirror passage. |
| Status | The short physical collar and finite arithmetic have Lean proofs. The physical long-trace identification remains open. |
| Lean evidence | `DommaschkMirrorLaunch.exists_nested_collar`, `MirrorActionQuadrature.Packet.sound`, `RadialSlabs.Chain.sound`, `RadialTile.Cover.action_secant` |
| Audit evidence | Kernel-checked packed arithmetic with rational and integer witnesses. The coverage counts and physical hypotheses are listed below. |
| Patches | N-57, N-59 and N-60, certificate verification status |
| Last updated | 24 November 2026 |

## Physical launch theorem

**Compiled Lean theorem, on demand.** A single pair of nested Dommaschk field-line tori has the following property. Choose either symmetry azimuth, a birth phase within 1/4096 radian of it, and any interpolation coordinate in [0.44, 0.54]. From the resulting point there is a solution of the physical field-line ODE for 1/64 radian in either angular direction. Each cylindrical coordinate moves by at most one quarter of the angular distance. The proof uses all signed Fourier columns of both packed KAM seeds, the strip-closeness bound on the same witnesses, and interval evaluation of the actual candidate field. [Physical theorem](../../PlasmaLean/Design/DommaschkMirrorSectorFlow.lean) · [Launch coordinates](../../PlasmaLean/Design/DommaschkMirrorLaunch.lean)

## Arithmetic and action

| Source | Cases | Quantity checked |
| --- | ---: | --- |
| N-57 | 4 | Both heights on the birth clock and the common-section clock |
| N-59 | 16 | Twelve symmetry and intermediate phase face comparisons and four wider core/cap comparisons |
| N-60 | 8 | Left and right endpoint signs for four root brackets across two sectors |
| N-60 radial variation | 16 tiles × 2 directions × 391 slabs | Tangent-error recurrence, adjacent radii, observable ranges and crossing bounds |

**Compiled Lean theorem.** For a continuous field-strength and nonnegative arclength density satisfying a packet's directed panel bounds, `Packet.sound` proves the signed comparison of the continuous single-passage action with its rational target. Python generates integer square-root witnesses and weighted sums. Lean checks them and applies the interval integral inequalities. Across the 28 packets, 355,696 input panel bounds cover 879,936 uniform integration subintervals. The N-60 endpoints account for 250,848 of them. The sixfold subdivision of a coarser input panel uses the same enclosure on each subinterval. [Quadrature proof](../../PlasmaLean/Certificates/MirrorActionQuadrature.lean) · [Candidate packets](../../PlasmaLean/Design/DommaschkActionQuadrature.lean)

**Compiled Lean theorem.** On each of the four radial brackets the finite cover gives a lower secant bound on the two-sided action, provided the true observables and their first variations satisfy the stated bounds. The mirror-pair lemma identifies the clipped integral with the integral between the two first mirror points. Each directed radial chain checks its 391 successive records against the matching tile. [Radial cover](../../PlasmaLean/Design/DommaschkRadialTiles.lean) · [First mirrors and action](../../PlasmaLean/Certificates/RadialTile.lean) · [Slab recurrence](../../PlasmaLean/Certificates/RadialSlabs.lean)

## Remaining physical identification

**Compiled Lean theorem, on demand.** For either sector, `DommaschkLocalMirrorGraphs.sector_graphs` combines its four endpoint packets and both radial covers. The higher-height root lies inward of the lower-height root by more than 9/200 in the launch interpolation coordinate. Each root is continuous in phase and unique in its recorded bracket. The input `TraceBounds` specifies bounds on the same field strength and arclength density for both heights. [Graph assembly](../../PlasmaLean/Design/DommaschkLocalMirrorGraphs.lean)

The longest required radial trace extends 6.1 geometric radians in each direction. The packet proofs take enclosures of field strength and arclength as inputs. The radial proofs also take enclosures for their derivatives with respect to the launch radius. To obtain a candidate-specific graph theorem these inputs must come from the same physical trajectory and the same radial variation throughout the passage. This requires the transferred initial point, every polynomial defect and frame change, and the observable evaluation over each time interval. A full-period winding graph and a thermal-particle C2 bound require further arguments. Physical operating targets remain open.
