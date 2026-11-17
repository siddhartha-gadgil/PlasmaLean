# Skill: Epsilon-Delta Proofs

**Pre-condition:** Apply this skill when the goal is a limit, continuity, uniform continuity, convergence, or a metric/topological statement with explicit tolerances.

**Goal:** Choose the right tolerance parameter and verify the implication demanded by the definition.

**Instructions:**
1. **Unfold the Definition:** Write the exact quantified statement with `epsilon`, `delta`, neighborhoods, or sequence indices.
2. **Fix the Tolerance:** Let `epsilon > 0` or the requested neighborhood be arbitrary.
3. **Choose the Control Parameter:** Define `delta`, `N`, or a smaller neighborhood in terms of the data.
4. **Verify Positivity/Admissibility:** Prove the chosen control parameter is valid.
5. **Run the Estimate:** Starting from the assumed closeness, derive the target closeness.
6. **Use Standard Reductions:** For sums, products, and compositions, split the tolerance into manageable pieces.

**Common Failure Modes:**
- Choosing `delta` after assuming a special `x`.
- Forgetting the `0 < |x-a|` condition where needed.
- Not proving the chosen parameter is positive.
