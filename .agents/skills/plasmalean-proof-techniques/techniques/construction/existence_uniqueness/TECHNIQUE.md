# Skill: Existence, Construction, and Uniqueness

**Pre-condition:** Apply this skill when the goal contains `exists`, `exists unique`, a request to construct an object, or a statement asserting canonical existence.

**Goal:** Build or justify a witness and verify all required properties; for uniqueness, show any two witnesses coincide.

**Instructions:**
1. **Parse the Goal:** Separate the witness type from the property it must satisfy.
2. **Construct or Source a Witness:**
   - Explicit construction: define the object.
   - Nonconstructive existence: identify the theorem, compactness, choice, counting, or contradiction argument that supplies it.
   - Search for a witness: when the witness is a concrete object (finite data or a short program) and none is known, assess whether an evolutionary search could find one, following "Consider an evolutionary search" in the `plasmalean-examples-counterexamples` skill, and if so launch it with a sub-agent in parallel while pursuing a construction or a nonconstructive argument by hand. A witness found this way comes with Lean proofs of its properties.
3. **Verify Properties:** Check each conjunct or defining property of the witness.
4. **Uniqueness:** Assume two objects satisfy the property and prove they are equal or equivalent in the required sense.
5. **Package the Result:** For `exists unique`, present existence first and uniqueness second.

**Common Failure Modes:**
- Providing a candidate without verifying all required fields or properties.
- Proving uniqueness only among constructed objects rather than all objects satisfying the predicate.
- Hiding a nonconstructive existence theorem without naming its hypotheses.
