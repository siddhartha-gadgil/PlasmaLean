# Examples: Direct, Contrapositive, and Contradiction Proofs

## Example 1: Direct Proof

**Problem shape:** If `n` is even, prove `n^2` is even.

**Use of technique:**
1. Assume `n` is even.
2. Write `n = 2k`.
3. Compute `n^2 = 4k^2 = 2(2k^2)`.
4. Conclude `n^2` is even.

## Example 2: Contrapositive

**Problem shape:** If `n^2` is even, prove `n` is even.

**Use of technique:**
1. Prove the contrapositive: if `n` is odd, then `n^2` is odd.
2. Write `n = 2k + 1`.
3. Compute `n^2 = 2(2k^2 + 2k) + 1`.
4. Conclude `n^2` is odd, so the original implication holds.

## Example 3: Contradiction

**Problem shape:** Prove there are infinitely many primes.

**Use of technique:**
1. Assume finitely many primes `p_1, ..., p_n`.
2. Form `N = p_1 ... p_n + 1`.
3. Show no listed prime divides `N`.
4. Contradict existence of a prime divisor of `N`.

## Fully Explicit Goal Reduction: Even Square Implies Even

**Statement:** For every integer `n`, if `n^2` is even, then `n` is even.

**Goal:** Prove `n^2 even -> n even`.

**Reduction by contrapositive:**
1. Replace the goal by the contrapositive: prove `n not even -> n^2 not even`.
2. Over integers, reduce `n not even` to `n` odd.
3. Write `n = 2k + 1`.
4. Compute `n^2 = (2k + 1)^2 = 2(2k^2 + 2k) + 1`.
5. Conclude `n^2` is odd, hence not even.
6. By contrapositive, conclude the original implication.
