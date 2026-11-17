# Examples: Counting, Double Counting, and Pigeonhole

## Example 1: Handshake Lemma

**Problem shape:** Prove the sum of vertex degrees in a finite graph is twice the number of edges.

**Use of technique:**
1. Count incidences `(v, e)` where vertex `v` lies on edge `e`.
2. Counting by vertices gives `sum_v deg(v)`.
3. Counting by edges gives `2 |E|`.
4. Equate the two counts.

## Example 2: Pigeonhole Divisibility

**Problem shape:** Among `n + 1` integers, two have the same residue modulo `n`.

**Use of technique:**
1. Objects are the `n + 1` integers.
2. Boxes are the `n` residue classes modulo `n`.
3. By pigeonhole, two integers land in the same box.
4. Their difference is divisible by `n`.

## Example 3: Counting Paths In A Grid

**Problem shape:** Count monotone lattice paths from `(0,0)` to `(m,n)`.

**Use of technique:**
1. A path has `m` right steps and `n` up steps.
2. Count paths by choosing positions of the right steps.
3. Get `binom(m+n, m)`.
4. Check this counts each path exactly once.

## Fully Explicit Goal Reduction: Handshake Lemma

**Statement:** Let `G = (V, E)` be a finite undirected graph with no loops. Prove `sum_{v in V} deg(v) = 2 |E|`.

**Goal:** Establish an equality of two natural numbers.

**Reduction by double counting:**
1. Define the incidence set `I = {(v, e) : v in V, e in E, v is an endpoint of e}`.
2. Vertex-count subgoal: prove `|I| = sum_{v in V} deg(v)` by partitioning incidences by vertex.
3. Edge-count subgoal: prove `|I| = 2 |E|` because every edge has exactly two endpoints.
4. Combine the two equalities through `|I|`.
5. Conclude `sum_{v in V} deg(v) = 2 |E|`.
