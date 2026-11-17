# Examples: Cases and Exhaustion

## Example 1: Parity Cases

**Problem shape:** Prove an integer statement by considering parity.

**Use of technique:**
1. Split into cases: `n` even or `n` odd.
2. In the even case, write `n = 2k`.
3. In the odd case, write `n = 2k + 1`.
4. Prove the same target in both branches.

## Example 2: Residues Modulo 3

**Problem shape:** Prove `n^2` is congruent to `0` or `1` modulo `3`.

**Use of technique:**
1. Exhaust residues: `n = 0, 1, 2 mod 3`.
2. Square each residue.
3. Record results `0, 1, 1`.
4. Conclude all cases satisfy the claim.

## Example 3: Degenerate And Nondegenerate Geometry Cases

**Problem shape:** Prove a statement about two lines in a plane.

**Use of technique:**
1. Split into parallel and nonparallel cases.
2. Treat coincident lines separately if needed.
3. Use intersection arguments only in the nonparallel case.
4. Verify all geometric configurations are covered.

## Fully Explicit Goal Reduction: Squares Modulo 4

**Statement:** For every integer `n`, prove `n^2` is congruent to `0` or `1` modulo `4`.

**Goal:** Prove `(n^2 mod 4 = 0) or (n^2 mod 4 = 1)`.

**Reduction by exhaustion:**
1. Reduce the integer `n` to its residue modulo `4`.
2. Exhaust the four cases:
   - `n = 0 mod 4`, so `n^2 = 0 mod 4`;
   - `n = 1 mod 4`, so `n^2 = 1 mod 4`;
   - `n = 2 mod 4`, so `n^2 = 4 = 0 mod 4`;
   - `n = 3 mod 4`, so `n^2 = 9 = 1 mod 4`.
3. Each case proves one side of the disjunction.
4. Exhaustiveness of residues modulo `4` closes the universal statement.
