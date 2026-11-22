# Examples: Induction, Minimal Counterexample, and Descent

## Example 1: Ordinary Induction

**Problem shape:** Prove `1 + ... + n = n(n+1)/2`.

**Use of technique:**
1. Base case: verify `n = 0` or `n = 1`.
2. Induction hypothesis: assume the formula for `n`.
3. Add `n + 1` to both sides.
4. Simplify to get the formula for `n + 1`.

## Example 2: Strong Induction

**Problem shape:** Every integer `n >= 2` factors into primes.

**Use of technique:**
1. Assume the statement for all `k < n`.
2. If `n` is prime, stop.
3. If `n = ab` with `2 <= a,b < n`, apply the induction hypothesis to `a` and `b`.
4. Combine the prime factorizations.

## Example 3: Infinite Descent

**Problem shape:** Prove `sqrt(2)` is irrational.

**Use of technique:**
1. Assume a smallest positive denominator representation `sqrt(2) = a/b`.
2. Derive that `a` and `b` are both even.
3. Divide by `2` to get a smaller positive denominator representation.
4. Contradict minimality.

## Fully Explicit Goal Reduction: Sum Of First `n` Naturals

**Statement:** For every natural number `n`, prove `sum_{i=0}^n i = n(n+1)/2`.

**Goal:** Prove `P(n)` for all `n`, where `P(n)` is the displayed formula.

**Reduction by induction:**
1. Base subgoal `P(0)`: both sides are `0`.
2. Induction step subgoal: assume `P(n)`, prove `P(n+1)`.
3. Rewrite `sum_{i=0}^{n+1} i = (sum_{i=0}^n i) + (n+1)`.
4. Use the induction hypothesis to replace the partial sum by `n(n+1)/2`.
5. Algebra subgoal: prove `n(n+1)/2 + (n+1) = (n+1)(n+2)/2`.
6. Conclude `forall n, P(n)`.
