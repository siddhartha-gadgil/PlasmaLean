# Examples: Generic Arguments and Almost-All Reasoning

## Example 1: Dense Open Property

**Problem shape:** Show a property holds for a generic point of an irreducible variety.

**Use of technique:**
1. Identify the bad locus as the vanishing set of a nonzero polynomial.
2. Conclude the complement is Zariski open and dense.
3. Work on that dense open subset.
4. State the result as holding generically.

## Example 2: Almost Everywhere Equality

**Problem shape:** Prove two integrable functions define the same integral functional.

**Use of technique:**
1. Show the functions differ only on a null set.
2. Use the measure-theoretic fact that null-set changes do not alter integrals.
3. Conclude equality of the functionals.
4. Track the exceptional set explicitly.

## Example 3: Baire Category Argument

**Problem shape:** Prove a typical continuous function has a property.

**Use of technique:**
1. Express the desired property as a countable intersection of open dense sets.
2. Use completeness of the ambient metric space.
3. Apply the Baire Category Theorem.
4. Conclude the property holds on a residual set.

## Fully Explicit Goal Reduction: Nonvanishing Is Generic

**Statement:** Let `k` be an infinite field and let `p in k[x_1, ..., x_n]` be a nonzero polynomial. Prove there is a Zariski dense open subset `U` of `A^n_k` such that `p(a) != 0` for all `a in U`.

**Goal:** Exhibit a dense open set on which `p` does not vanish.

**Reduction by generic argument:**
1. Define the bad set `Z(p) = {a : p(a) = 0}`.
2. Define `U = A^n_k \ Z(p)`.
3. Open-subset subgoal: prove `U` is Zariski open because `Z(p)` is closed.
4. Density subgoal: prove `U` is dense because `p` is not the zero polynomial.
5. Verification subgoal: by definition of `U`, every `a in U` satisfies `p(a) != 0`.
