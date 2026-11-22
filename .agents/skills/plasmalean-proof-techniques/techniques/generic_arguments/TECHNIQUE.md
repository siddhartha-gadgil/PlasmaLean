# Skill: Generic Arguments & "Almost All" Reasoning

**Pre-condition:** Do not apply this skill unless the problem involves a property claimed to hold for "almost all" objects, "generic" configurations, or requires proving a global result by analyzing a representative point in a dense/thick subset.

**Goal:** Leverage topological, measure-theoretic, or algebraic notions of "genericity" to simplify proofs or establish results on dense subsets.

**Instructions:**

### 1. Identify the Notion of Genericity
Select the appropriate framework based on the problem context:
- **Topological/Baire Category:** Property holds on a residual set (countable intersection of dense open sets). Use for complete metric spaces.
- **Measure-Theoretic:** Property holds "almost everywhere" (complement is a null set). Use for integration or probability.
- **Algebraic Geometry:** Reasoning via the generic point $\eta$ of an irreducible scheme or a Zariski-dense open set.
- **General Topology:** Property holds on a dense open subset.

### 2. The Generic Strategy
1. **Define the Space:** Identify the space $X$ (e.g., a manifold, a scheme, a function space $C^k$).
2. **Select the "Generic" Representative:**
   - **Algebraic:** Work in the function field $k(X)$.
   - **Analytic:** Pick a point $x$ avoiding a specific countable union of "bad" sets (e.g., resonances, singular values).
   - **Measure:** Assume the property holds for $x$ outside a set of measure zero.
3. **Prove at the Generic Level:** Establish the result for this representative.
4. **Spread/Extend:**
   - Use **continuity** to extend from a dense set to the whole space.
   - Use **compactness** or **Baire Category Theorem** to show the intersection of generic properties is still generic.
   - Use **Fubini's Theorem** for slice-wise genericity in measure theory.

### 3. Handle the Exceptional Set
Characterize the "bad" set $E$ where the property fails.
- Is $E$ meager (1st category)?
- Is $E$ a null set?
- Is $E$ a proper closed subvariety?
