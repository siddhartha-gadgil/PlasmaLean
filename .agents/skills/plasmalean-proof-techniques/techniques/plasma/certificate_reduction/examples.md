# Examples: Reduction to a Finite Certificate

## Example 1: Existence near an approximate solution (radii polynomial)

**Problem shape:** A numerical solver returns an approximate equilibrium `ubar`. Prove a true
solution exists nearby.

**Use of technique:**
1. Write the problem as a fixed point `T u = u` (for `F = 0`, `T = id − A ∘ F` with an injective
   approximate inverse `A`).
2. Bound the defect `‖T ubar − ubar‖ ≤ Y₀` and the Lipschitz constant
   `(Z₀ + Z₂ r)` on the ball of radius `r`.
3. If `radiiPoly Y₀ Z₀ Z₂ r < 0`, then `radii_polynomial_fixedPoint` gives a unique fixed point in
   `closedBall ubar r` (`PlasmaLean/Certificates/RadiiPolynomial.lean`).
4. Finite part: `Y₀`, `Z₀`, `Z₂`, `r` are exact rationals checked by the kernel.
5. Rejected fixtures: `radii_polynomial_rejects_small` (a radius below the defect never passes),
   `zero_inverse_counterexample` in `Contraction.lean` (a fixed point of `id − 0 ∘ F` says nothing
   about `F`, so injectivity of `A` is required).

## Example 2: A Boolean checker over cells

**Problem shape:** Prove an inequality at every point of a parameter box.

**Use of technique:**
1. Analytic part: the box is covered by the cells, and on each cell the function is within a
   proved remainder of its value at the centre.
2. Finite part: a checker `check cells = true` comparing, per cell, the centre value with the
   remainder.
3. Soundness by induction over the cell list; instances closed by `bool_cert`
   (`PlasmaLean/Certificates/BoolCert.lean`), which builds an explicit proof term with one
   subtree per cell.

## Example 3: Ballooning stability of a concrete equilibrium

**Problem shape:** Show a Solov'ev equilibrium is ballooning-stable on a field-line segment.

**Use of technique:**
1. Analytic part: `BartaCertificate.lower_bound` (see `energy_coercivity`) reduces stability to a
   pointwise inequality for a test function.
2. Finite part: the test function and the inequality on cells, checked by the domain macro
   `bl_cert` in `PlasmaLean/Design/SolovevBallooningEvalCert`.
3. The generator validates every emitted bound in exact arithmetic before writing Lean.
