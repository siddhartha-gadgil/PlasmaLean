# Examples: Existence, Construction, and Uniqueness

## Example 1: Existence Of An Even Prime

**Problem shape:** Prove there exists an even prime.

**Use of technique:**
1. Choose witness `2`.
2. Verify `2` is even.
3. Verify `2` is prime.
4. Package the witness with both properties.

## Example 2: Unique Additive Identity

**Problem shape:** Prove an additive identity in a monoid is unique.

**Use of technique:**
1. Existence is given by the monoid axioms.
2. Let `e` and `e'` both be additive identities.
3. Use `e` as a left identity and `e'` as a right identity to show `e = e + e' = e'`.
4. Conclude uniqueness.

## Example 3: Constructing A Lift

**Problem shape:** Prove there exists a lift satisfying a commutative square.

**Use of technique:**
1. Define the candidate lift explicitly or by a lifting theorem.
2. Verify it maps into the correct object.
3. Check the required diagram commutes.
4. If uniqueness is claimed, compare two lifts by composing with the relevant maps.

## Fully Explicit Goal Reduction: Unique Additive Identity

**Statement:** Let `M` be a type with an associative operation `+`. Suppose `0` and `0'` are both additive identities, meaning `0 + x = x`, `x + 0 = x`, `0' + x = x`, and `x + 0' = x` for all `x`. Prove `0 = 0'`.

**Goal:** Prove equality of the two candidate identities.

**Reduction by uniqueness:**
1. Use the right-identity property of `0'` with `x = 0` to get `0 + 0' = 0`.
2. Use the left-identity property of `0` with `x = 0'` to get `0 + 0' = 0'`.
3. Reduce `0 = 0'` to transitivity through the common term `0 + 0'`.
4. Conclude any two additive identities are equal.
