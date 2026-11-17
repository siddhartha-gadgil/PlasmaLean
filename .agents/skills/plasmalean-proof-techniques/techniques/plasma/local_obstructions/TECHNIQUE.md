# Skill: Local Obstructions and Necessity

**Pre-condition:** The claim is an impossibility (no field or configuration has properties
P₁, …, Pₖ), a necessary condition for stability or confinement, or a check that a proposed
hypothesis cannot be dropped. Use it when sufficient-condition attempts keep failing, or to test a
design target before spending effort on it.

**Goal:** Derive a contradiction or a necessary condition from local information (values,
derivatives, Taylor coefficients at a point or along a curve), or exhibit an explicit witness
violating the claimed implication.

**Instructions:**
1. **Localize.** Find the point or curve where the properties interact: a critical point or
   extremum of `|B|`, the magnetic axis, a closed field line, a resonant surface, a conjugate point.
2. **Expand.** Write the first and second derivatives (the jet) of the relevant quantities at
   that point, using the field equations (`∇ × B = 0`, `∇ · B = 0`, force balance) to relate them.
3. **Extract the identity.** Typical identities: the curvature identity `∇⊥|B| = |B| κ` in vacuum;
   the Bochner identity `Δ|B|² = 2 ∑ (∂ⱼ Bᵢ)² ≥ 0` for a vacuum field (subharmonicity); at a local maximum
   the Laplacian is nonpositive; the Lie-bracket/gradient commutator with its strain term.
4. **Contradict or conclude.** Combine the identity with the local extremum or symmetry property
   to force a quantity to vanish (curvature zero), then contradict a global fact (a closed curve
   cannot have zero curvature everywhere).
5. **Necessity by a witness.** For a necessary condition, build the destabilizing or violating
   object from the failure of the condition: a Jacobi field vanishing at a conjugate point gives a
   test function with nonpositive energy (Sturm); an explicit polynomial field gives a local
   counterexample. Check every hypothesis of the original claim on the witness exactly.
6. **State the scope:** local versus global, vacuum versus finite pressure, exact versus
   approximate symmetry.

**Lean:** `PlasmaLean/Theory/Fields/CurvatureObstruction.lean`, `Subharmonic.lean`,
`LieGradient.lean`; `PlasmaLean/Theory/Stability/SturmNecessity.lean`;
`PlasmaLean/Sanity/CurvatureObstruction.lean`, `QuasisymmetryNotSymmetry.lean`. Witnesses are
designed with `plasmalean-examples-counterexamples`.
