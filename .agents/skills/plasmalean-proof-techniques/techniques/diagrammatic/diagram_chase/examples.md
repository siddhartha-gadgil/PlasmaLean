# Examples: Diagram Chase and Diagrammatic Reasoning

## Example 1: Kernel-Image Step In An Exact Sequence

**Problem shape:** Given exactness at `B`, prove an element in `ker(g)` comes from `A`.

**Use of technique:**
1. Start with `b in B` and `g(b) = 0`.
2. Exactness says `ker(g) = im(f)`.
3. Obtain `a in A` with `f(a) = b`.
4. Use this preimage in the rest of the proof.

## Example 2: Commutative Square

**Problem shape:** Prove two ways of mapping an element agree.

**Use of technique:**
1. Name the square maps `f, g, h, k`.
2. Use commutativity: `k o f = h o g`.
3. Apply both sides to the chosen element.
4. Rewrite one path into the other.

## Example 3: Lifting In A Diagram

**Problem shape:** Construct an element whose image is a given element.

**Use of technique:**
1. Chase the target element backward along a surjective map.
2. Use commutativity to check compatibility with the next map.
3. Use exactness to adjust by an element from an earlier object.
4. Verify the adjusted lift has the desired image.

## Fully Explicit Goal Reduction: Exactness Gives A Preimage

**Statement:** Let `A --f--> B --g--> C` be maps of abelian groups, exact at `B`, so `im(f) = ker(g)`. If `b in B` and `g(b) = 0`, prove there exists `a in A` such that `f(a) = b`.

**Goal:** Prove `exists a, f(a) = b`.

**Reduction by diagram chase:**
1. Start with the element `b in B`.
2. The assumption `g(b) = 0` reduces to `b in ker(g)`.
3. Exactness reduces membership `b in ker(g)` to membership `b in im(f)`.
4. Unfold `b in im(f)` to obtain `exists a in A, f(a) = b`.
5. This witness `a` proves the goal.
