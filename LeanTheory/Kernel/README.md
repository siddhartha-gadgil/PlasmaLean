# Kernel/

The domain model. A kernel file defines the objects of the domain and states each law as a
**typeclass** (a hypothesis that an object satisfies), never as an `axiom`. Theorems take the law
as an instance argument, so they hold for every object satisfying it.

- [`Example.lean`](Example.lean): the one-dimensional harmonic oscillator. `OscParams` (mass,
  stiffness), `energy`, the law `OscillatorLaw p x v` (`x' = v`, `m v' = -k x`),
  `energy_conserved`, `potential_le_energy`.

Keep the kernel small, state in each module docstring that it is a kernel file, and give every
law its sanity triad in `Sanity/`. See `notes/domain-libraries.md`.
