# Examples: Bounding, Monotonicity, and Extremal Objects

## Example 1: Squeeze Theorem

**Problem shape:** Prove `b_n -> L` from `a_n <= b_n <= c_n`.

**Use of technique:**
1. Prove `a_n -> L`.
2. Prove `c_n -> L`.
3. Use the two inequalities for all sufficiently large `n`.
4. Conclude `b_n -> L`.

## Example 2: Maximal Linearly Independent Set

**Problem shape:** Prove a maximal linearly independent set spans a vector space.

**Use of technique:**
1. Choose a maximal linearly independent set.
2. Suppose it does not span.
3. Add a vector outside its span, preserving linear independence.
4. Contradict maximality.

## Example 3: Shortest Counterexample

**Problem shape:** Prove every connected graph has a spanning tree.

**Use of technique:**
1. Choose a connected spanning subgraph with the fewest edges.
2. If it contains a cycle, remove an edge from the cycle.
3. Connectivity is preserved, but the edge count decreases.
4. Contradict minimality, so the subgraph is a tree.

## Fully Explicit Goal Reduction: Squeeze For A Sequence

**Statement:** Suppose real sequences `a_n`, `b_n`, and `c_n` satisfy `a_n <= b_n <= c_n` for all sufficiently large `n`, and `a_n -> L`, `c_n -> L`. Prove `b_n -> L`.

**Goal:** Prove `forall epsilon > 0, exists N, forall n >= N, |b_n - L| < epsilon`.

**Reduction by bounding:**
1. Let `epsilon > 0`.
2. From `a_n -> L`, choose `N1` so `L - epsilon < a_n` for `n >= N1`.
3. From `c_n -> L`, choose `N2` so `c_n < L + epsilon` for `n >= N2`.
4. Choose `N3` so the inequalities `a_n <= b_n <= c_n` hold for `n >= N3`.
5. For `n >= max(N1, N2, N3)`, chain `L - epsilon < a_n <= b_n <= c_n < L + epsilon`.
6. Convert the two-sided bound into `|b_n - L| < epsilon`.
