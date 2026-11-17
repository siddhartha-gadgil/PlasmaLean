# Examples: Algorithmic Correctness

## Example 1: Euclidean Algorithm

**Problem shape:** Prove the Euclidean algorithm returns `gcd(a, b)`.

**Use of technique:**
1. Define the loop state `(x, y)`.
2. Prove the invariant `gcd(x, y) = gcd(a, b)`.
3. Prove termination by the strictly decreasing second coordinate.
4. At termination, `y = 0`, so `x = gcd(x, 0) = gcd(a, b)`.

## Example 2: Binary Search

**Problem shape:** Prove binary search finds a target if it is in a sorted array.

**Use of technique:**
1. Maintain the invariant: if the target exists, it lies in the current interval.
2. Each comparison removes a half-interval while preserving the invariant.
3. Termination follows because interval length strictly decreases.
4. If the loop exits unsuccessfully, the invariant implies the target was absent.

## Example 3: Recursive Evaluation Of Syntax Trees

**Problem shape:** Prove an evaluator agrees with denotational semantics.

**Use of technique:**
1. Define the algorithm by recursion on expression structure.
2. Prove termination by structural recursion.
3. Prove correctness by structural induction over constructors.
4. Combine constructor cases into total correctness.

## Fully Explicit Goal Reduction: Euclidean Algorithm

**Statement:** For natural numbers `a` and `b`, the loop
`while y != 0 do (x, y) := (y, x mod y)` starting from `(a, b)` terminates and returns `gcd(a, b)`.

**Goal:** Prove total correctness of the loop.

**Reduction by algorithmic correctness:**
1. Termination subgoal: prove the second coordinate `y` strictly decreases whenever `y != 0`, because `x mod y < y`.
2. Invariant subgoal: prove `gcd(x, y) = gcd(a, b)` is preserved by the assignment `(x, y) := (y, x mod y)`.
3. Exit subgoal: when the loop stops, `y = 0`.
4. Postcondition subgoal: from the invariant and `y = 0`, derive `x = gcd(x, 0) = gcd(a, b)`.
5. Combine termination and postcondition to conclude total correctness.
