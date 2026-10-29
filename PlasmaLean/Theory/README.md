# Theory/

Reusable proved mathematics above the kernel. Model laws enter as hypotheses or typeclass
arguments; results are general, not tied to one candidate. All modules are in the default build.

| Folder | Modules | Content |
| --- | --- | --- |
| [`Fields/`](Fields/) | 22 | Biot–Savart and filament fields (smoothness, complex extensions), Maxwell identities, Bochner and the vacuum maximum principle (`Subharmonic`), curvature obstruction, first integrals, invariant barriers and torus trapping, defect confinement, field-line existence, Lie-derivative/gradient commutator, magnetic 2-form on flux surfaces |
| [`KAM/`](KAM/) | 24 | Explicit-constant KAM: Diophantine estimates, cohomological equation, strip algebras and Paley–Wiener bounds, analytic composition, Cauchy estimates, weighted ℓ¹(ℤ²), the KAM sequence, parameter interpolation, polynomial expression majorants |
| [`Kinetic/`](Kinetic/) | 17 | Full orbits and canonical momentum, guiding centres (finite-time error, Littlejohn and Boozer models supplied), gyro-Noether, averaging, approximate invariants, bounce orbits and integrals, trapped orbits, available energy |
| [`Stability/`](Stability/) | 17 | Abstract energy, Suydam, Newcomb, Mercier (general index supplied), ballooning (Barta certificate, infinite line, surfaces, secular part), Sturm necessity, Elsässer identities, Riccati comparison (conditional) |
| [`Transport/`](Transport/) | 6 | Comparison principles for the radial transport operator, barrier checks, flux geometry, power balance, confinement scalings (IPB98, ISS04), fine Bosch–Hale windows |
| [`Equilibrium/`](Equilibrium/) | 2 | Slab and screw-pinch equilibria |
| [`Geometry/`](Geometry/) | 5 | Coil geometry: circular coils, coil tubes, placed circles, parametric bounds, surface covers |
| [`Engineering/`](Engineering/) | 1 | Slab heat conduction |

Name restricted results by their scope (finite subspace, finite time, supplied reduction). Before
adding infrastructure, search Mathlib (`rg` in `.lake/packages/mathlib`).
