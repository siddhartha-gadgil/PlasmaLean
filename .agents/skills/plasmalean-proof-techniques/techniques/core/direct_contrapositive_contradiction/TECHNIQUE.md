# Skill: Direct, Contrapositive, and Contradiction Proofs

**Pre-condition:** Apply this skill when the goal is an implication, a negation, an impossibility statement, or a proposition whose negation has strong usable content.

**Goal:** Select the most efficient propositional proof skeleton and expose the assumptions that should drive the proof.

**Instructions:**
1. **Classify the Goal Form:**
   - For `P -> Q`, first try a direct proof: assume `P`, prove `Q`.
   - If `not Q` gives stronger algebraic or structural information, try the contrapositive: prove `not Q -> not P`.
   - If the negation of the whole goal creates a useful object or forbidden configuration, use contradiction.
2. **Open the Correct Assumptions:**
   - Direct: record the hypotheses and the assumed antecedent.
   - Contrapositive: record the negated conclusion and target the negated hypothesis.
   - Contradiction: record the exact negation of the claim and the contradiction target.
3. **Drive Forward:** Derive concrete consequences of the assumptions before invoking high-level theorems.
4. **Close the Proof:** Make the final contradiction, negated hypothesis, or desired conclusion explicit.

**Common Failure Modes:**
- Using contradiction when a direct implication proof is shorter.
- Forgetting that contrapositive only applies directly to implications.
- Treating "prove a contradiction" as a claim rather than deriving an explicit false statement.
