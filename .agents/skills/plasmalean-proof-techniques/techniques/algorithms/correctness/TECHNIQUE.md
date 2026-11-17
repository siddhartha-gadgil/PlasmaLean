# Skill: Algorithmic Correctness

**Pre-condition:** Apply this skill when the statement is proved by giving a procedure, recursive definition, decision method, computation, or constructive algorithm.

**Goal:** Prove that the algorithm terminates and returns an output satisfying the specification.

**Instructions:**
1. **Specify Inputs and Outputs:** State preconditions and postconditions precisely.
2. **Define the Algorithm:** Give enough detail that every step is deterministic or its allowed choices are specified.
3. **Termination:** Exhibit a decreasing measure, well-founded recursion, finite search space, or loop variant.
4. **Partial Correctness:** Prove that if the algorithm terminates, the output satisfies the specification.
5. **Maintain Invariants:** For loops or iterative procedures, state and prove the loop invariant.
6. **Conclude Total Correctness:** Combine termination and partial correctness.

**Common Failure Modes:**
- Proving correctness only for examples.
- Omitting termination for recursive or iterative procedures.
- Using an invariant that is not strong enough to imply the postcondition.
