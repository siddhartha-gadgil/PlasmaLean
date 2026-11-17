# Examples: Epsilon-Delta Proofs

## Example 1: Continuity Of A Linear Function

**Problem shape:** Prove `f(x) = ax + b` is continuous at `c`.

**Use of technique:**
1. Let `epsilon > 0`.
2. If `a = 0`, choose any positive `delta`.
3. If `a != 0`, choose `delta = epsilon / |a|`.
4. From `|x - c| < delta`, derive `|f(x) - f(c)| = |a| |x - c| < epsilon`.

## Example 2: Limit Of A Sum

**Problem shape:** If `f -> L` and `g -> M`, prove `f + g -> L + M`.

**Use of technique:**
1. Let `epsilon > 0`.
2. Use convergence of `f` with `epsilon / 2`.
3. Use convergence of `g` with `epsilon / 2`.
4. Combine the two estimates by the triangle inequality.

## Example 3: Sequential Convergence In A Metric Space

**Problem shape:** Prove `x_n -> x` from an explicit distance bound.

**Use of technique:**
1. Let `epsilon > 0`.
2. Choose `N` so the bound is less than `epsilon` for all `n >= N`.
3. Apply the distance bound.
4. Conclude the sequence convergence definition.

## Fully Explicit Goal Reduction: Continuity Of `x |-> 3x + 2`

**Statement:** Prove the function `f : R -> R`, `f(x) = 3x + 2`, is continuous at an arbitrary point `c`.

**Goal:** Prove `forall epsilon > 0, exists delta > 0, forall x, |x - c| < delta -> |f(x) - f(c)| < epsilon`.

**Reduction by epsilon-delta:**
1. Let `epsilon > 0` be arbitrary.
2. Choose `delta = epsilon / 3`.
3. Positivity subgoal: prove `delta > 0` from `epsilon > 0`.
4. Verification subgoal: assume `|x - c| < delta`.
5. Compute `|f(x) - f(c)| = |(3x + 2) - (3c + 2)| = 3 |x - c|`.
6. Use `|x - c| < epsilon / 3` to conclude `3 |x - c| < epsilon`.
