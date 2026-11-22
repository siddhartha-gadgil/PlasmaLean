# Examples: Universal Property Arguments

## Example 1: Products Are Unique Up To Unique Isomorphism

**Problem shape:** Show an object `P` is isomorphic to `A x B`.

**Use of technique:**
1. State the product universal property for `A x B`.
2. Show `P` has maps `p1 : P -> A` and `p2 : P -> B`.
3. For any object `X` with maps `f : X -> A` and `g : X -> B`, construct the unique map `h : X -> P`.
4. Conclude `P` and `A x B` are canonically isomorphic by uniqueness of products.

## Example 2: Maps Out Of A Quotient

**Problem shape:** Define a function from `G / N` to another group `H`.

**Use of technique:**
1. Start with a homomorphism `phi : G -> H`.
2. Verify `N <= ker(phi)`.
3. Invoke the quotient universal property to obtain a unique homomorphism `G / N -> H`.
4. Prove any other map compatible with the quotient projection is equal to this one.

## Example 3: Tensor Product Bilinear Factorization

**Problem shape:** Convert a bilinear map `M x N -> P` into a linear map `M tensor N -> P`.

**Use of technique:**
1. Verify the map is bilinear.
2. Use the universal property of tensor products to get a linear map.
3. Check the linear map agrees on pure tensors.
4. Use uniqueness to prove two such linear maps are equal.

## Fully Explicit Goal Reduction: Product Comparison

**Statement:** Let `P` be a set with maps `p1 : P -> A` and `p2 : P -> B`. Suppose that for every set `X` and maps `f : X -> A`, `g : X -> B`, there exists a unique map `u : X -> P` such that `p1 o u = f` and `p2 o u = g`. Prove `P` is isomorphic to `A x B`.

**Goal:** Construct a bijection `Phi : P -> A x B`.

**Reduction by universal property:**
1. Define `Phi(p) = (p1(p), p2(p))`.
2. Use the product universal property of `P` with `X = A x B`, `f = fst`, and `g = snd` to obtain `Psi : A x B -> P`.
3. Reduce `Phi o Psi = id` to the two projection equalities:
   - `fst o Phi o Psi = fst`;
   - `snd o Phi o Psi = snd`.
4. Reduce `Psi o Phi = id` to the uniqueness clause for `P` with `X = P`, `f = p1`, and `g = p2`.
5. Conclude `Phi` and `Psi` are inverse bijections.
