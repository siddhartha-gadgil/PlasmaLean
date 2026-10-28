# Sanity/

Checks that kernel definitions and laws mean what they should: for every law a **degenerate
case**, a **concrete instance** (the law is satisfiable, so theorems about it are not vacuous) and
a **counterexample** (the law excludes something).

- [`Example.lean`](Example.lean): for `Kernel/Example`, the free particle
  (`free_velocity_const`), the instance `cos`/`-sin` (`instOscillatorLawCos`, `cos_energy`) and
  the non-instance `exp` (`exp_energy_not_conserved`, `not_oscillatorLaw_exp`).
- [`QuasisymmetryNotSymmetry.lean`](QuasisymmetryNotSymmetry.lean): a local counterexample showing
  that a symmetry of a scalar field need not be a symmetry of the vector-field equations built
  from it (uses `Theory/Fields/LieGradient`).
