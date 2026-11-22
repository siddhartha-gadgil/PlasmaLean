# Examples: Equivalence and Reduction

## Example 1: Set Equality By Mutual Inclusion

**Problem shape:** Prove `A = B`.

**Use of technique:**
1. Reduce equality to `A subset B` and `B subset A`.
2. Prove each inclusion by taking a generic element.
3. Combine the two inclusions by extensionality.
4. Conclude `A = B`.

## Example 2: Three Equivalent Conditions

**Problem shape:** Prove `P`, `Q`, and `R` are equivalent.

**Use of technique:**
1. Prove `P -> Q`.
2. Prove `Q -> R`.
3. Prove `R -> P`.
4. Conclude all three conditions are equivalent by cycling implications.

## Example 3: Reduction To Diagonal Matrices

**Problem shape:** Prove a theorem for diagonalizable matrices.

**Use of technique:**
1. State the current claim for a diagonalizable matrix `A`.
2. Reduce to `A = P D P^{-1}` with `D` diagonal.
3. Prove the result for `D`.
4. Transfer the result back to `A` by conjugation.

## Fully Explicit Goal Reduction: Distributivity Of Intersection Over Union

**Statement:** For sets `A`, `B`, and `C`, prove `A cap (B union C) = (A cap B) union (A cap C)`.

**Goal:** Prove equality of two sets.

**Reduction by equivalence/extensionality:**
1. Reduce set equality to elementwise equivalence: for arbitrary `x`, prove
   `x in A cap (B union C) iff x in (A cap B) union (A cap C)`.
2. Forward direction:
   - assume `x in A` and `x in B union C`;
   - split `x in B union C` into cases `x in B` or `x in C`;
   - prove `x in A cap B` or `x in A cap C`.
3. Reverse direction:
   - assume `x in (A cap B) union (A cap C)`;
   - split the union;
   - in either case prove `x in A` and `x in B union C`.
4. Conclude the original set equality by extensionality.
