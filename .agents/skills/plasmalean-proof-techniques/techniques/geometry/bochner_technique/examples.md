# Examples: Bochner Technique

## Example 1: Vanishing Of Harmonic One-Forms

**Problem shape:** Show a closed Riemannian manifold with positive Ricci curvature has no nonzero harmonic one-forms.

**Use of technique:**
1. Let `omega` be a harmonic one-form.
2. Apply the Bochner formula for `|omega|^2`.
3. Integrate over the closed manifold.
4. Positivity forces `omega` to vanish.

## Example 2: Parallel Sections From Nonnegative Curvature

**Problem shape:** Show a harmonic form is parallel under a nonnegative curvature hypothesis.

**Use of technique:**
1. Apply the Weitzenbock identity.
2. Integrate the sum of nonnegative terms.
3. Since the integral is zero, each nonnegative term vanishes.
4. Conclude the covariant derivative of the form is zero.

## Example 3: Rigidity Of Killing Fields

**Problem shape:** Derive a vanishing or rigidity result for Killing fields under curvature assumptions.

**Use of technique:**
1. Insert the Killing field into the relevant Bochner identity.
2. Use the curvature sign to control the integral terms.
3. Show the field is parallel or zero.
4. Translate this into the desired geometric rigidity statement.

## Fully Explicit Goal Reduction: Positive Ricci Kills Harmonic One-Forms

**Statement:** Let `M` be a closed Riemannian manifold with positive Ricci curvature. Prove every harmonic one-form on `M` is zero.

**Goal:** For harmonic `omega`, prove `omega = 0`.

**Reduction by Bochner technique:**
1. Apply the Bochner identity for harmonic one-forms:
   `0 = integral_M (|nabla omega|^2 + Ric(omega, omega))`.
2. Nonnegativity subgoal: prove both terms are pointwise nonnegative.
3. Positivity subgoal: positive Ricci implies `Ric(omega, omega) > 0` wherever `omega != 0`.
4. Since the integral of a nonnegative function is zero, reduce to `|nabla omega|^2 = 0` and `Ric(omega, omega) = 0` everywhere.
5. Use positivity to conclude `omega = 0` everywhere.
