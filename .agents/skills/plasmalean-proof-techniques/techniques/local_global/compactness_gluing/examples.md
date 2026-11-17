# Examples: Compactness and Local-to-Global Gluing

## Example 1: Finite Subcover

**Problem shape:** Prove a compact set has a finite subcover from an open cover.

**Use of technique:**
1. Express the local data as an open cover.
2. Apply compactness to extract finitely many open sets.
3. Use the finite subcover to obtain a uniform or global bound.
4. Conclude the desired global statement.

## Example 2: Gluing Continuous Functions

**Problem shape:** Define a global continuous function from local continuous functions.

**Use of technique:**
1. Cover the space by open sets `U_i`.
2. Define continuous functions `f_i` on each `U_i`.
3. Prove `f_i = f_j` on overlaps `U_i cap U_j`.
4. Glue the `f_i` into a unique global continuous function.

## Example 3: Logic Compactness

**Problem shape:** Show an infinite theory has a model.

**Use of technique:**
1. Verify every finite subset of the theory has a model.
2. Apply compactness for first-order logic.
3. Obtain a model of the whole theory.
4. Transfer the desired property from the theory to the model.

## Fully Explicit Goal Reduction: Continuous Function Is Bounded On Compact Space

**Statement:** Let `X` be compact and `f : X -> R` continuous. Prove `f` is bounded.

**Goal:** Prove `exists M, forall x in X, |f(x)| <= M`.

**Reduction by compactness/local-to-global:**
1. For each `x in X`, continuity gives a neighborhood `U_x` on which `|f(y)| <= |f(x)| + 1`.
2. The sets `U_x` form an open cover of `X`.
3. Compactness subgoal: choose a finite subcover `U_{x_1}, ..., U_{x_n}`.
4. Define `M = max(|f(x_1)| + 1, ..., |f(x_n)| + 1)`.
5. For arbitrary `y in X`, choose `i` with `y in U_{x_i}` and conclude `|f(y)| <= M`.
