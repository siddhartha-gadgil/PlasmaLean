# Examples: Density and Approximation

## Example 1: Proving An Identity First For Polynomials

**Problem shape:** Prove a continuous linear identity for all functions in a normed space.

**Use of technique:**
1. Prove the identity for polynomials, where computation is explicit.
2. Use density of polynomials in the chosen function space.
3. Approximate arbitrary `f` by polynomials `p_n`.
4. Use continuity of both sides to pass to the limit.

## Example 2: Simple Functions In Integration

**Problem shape:** Prove an integral inequality for nonnegative measurable functions.

**Use of technique:**
1. Prove the inequality for nonnegative simple functions.
2. Approximate the measurable function by an increasing sequence of simple functions.
3. Apply monotone convergence.
4. Conclude the inequality for the original function.

## Example 3: Smooth Approximation

**Problem shape:** Extend a PDE estimate from smooth compactly supported functions to a Sobolev space.

**Use of technique:**
1. Prove the estimate for `C_c^\infty` functions.
2. Use density of `C_c^\infty` in the Sobolev norm.
3. Pass the estimate to the limit using norm convergence.
4. Check the weak derivative terms converge as required.

## Fully Explicit Goal Reduction: Equality Of Continuous Linear Maps

**Statement:** Let `X` and `Y` be normed vector spaces, let `D` be dense in `X`, and let `T S : X -> Y` be continuous linear maps. If `T d = S d` for every `d in D`, prove `T x = S x` for every `x in X`.

**Goal:** For arbitrary `x in X`, prove `T x = S x`.

**Reduction by density:**
1. Choose a sequence or net `d_i in D` with `d_i -> x`.
2. Reduce the goal to proving both `T d_i -> T x` and `S d_i -> S x`, using continuity.
3. Use the hypothesis to rewrite `T d_i = S d_i` for every `i`.
4. Reduce equality of limits to uniqueness of limits in `Y`.
5. Conclude `T x = S x`, then generalize over `x`.
