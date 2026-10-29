# Sanity/

Sanity checks for the kernel and for key definitions: degenerate cases, concrete instances (so
that laws are not vacuous), counterexamples (so that laws have content) and regression theorems.
All modules are in the default build.

| Module | Checks |
| --- | --- |
| [`Equilibrium`](Equilibrium.lean) | Nonvacuity and limiting cases of `ForceBalance` |
| [`NeutralMode`](NeutralMode.lean) | A neutral mode does not control displacement (energy nonnegativity is not stability) |
| [`ProbeEscape`](ProbeEscape.lean) | A positive axial probe field is not confinement |
| [`Vacuum`](Vacuum.lean), [`FilamentVacuum`](FilamentVacuum.lean) | Vacuum-field checks; closed filament fields are vacuum fields away from the source |
| [`CurvatureObstruction`](CurvatureObstruction.lean) | Witnesses for the curvature obstruction (no transverse min-B along a closed vacuum field line) |
| [`Transport`](Transport.lean) | Constant steady states, the classical heat equation for uniform coefficients, sign of the rate at a maximum (interior, regular and degenerate axis), a uniformly parabolic instance |
| [`Fusion`](Fusion.lean) | Zero density gives zero power, nonnegativity, monotonicity of `P_α` in `T` and in the fuel fraction, rejection of an out-of-window reactivity value |
| [`BoschHaleInstance`](BoschHaleInstance.lean), [`BoschHaleFineInstance`](BoschHaleFineInstance.lean) | Concrete instances of the Bosch–Hale reactivity classes (certificates `windows_cert`, `qwindows_cert`) |
| [`QuasisymmetryNotSymmetry`](QuasisymmetryNotSymmetry.lean) | Quasisymmetry is not a PDE symmetry: a local counterexample (`quasisymmetry_not_pde_symmetry`, gate E1) |

Every new kernel law needs a degenerate case, a concrete instance and a counterexample, plus at
least one check aimed at its real hazards (singularities, boundary behaviour, scaling, parameter
endpoints, quantifier order); every defect found in an audit gets a regression theorem here.
