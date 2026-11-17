# Skill: Equivalence and Reduction

**Pre-condition:** Apply this skill when the goal is an equivalence, a list of equivalent conditions, or a statement that should be reduced to a known theorem or simpler case.

**Goal:** Replace a hard target by directed implications or a reduced goal whose proof is already known or easier.

**Instructions:**
1. **For `P iff Q`:** Prove `P -> Q` and `Q -> P` as separate subgoals.
2. **For Multiple Equivalences:** Prefer a cycle `P1 -> P2 -> ... -> P1` when it is shorter than all pairwise implications.
3. **For Reduction:** Record:
   - current claim `P`;
   - reduced goal `Q`;
   - proof that `Q` implies or solves `P`;
   - proof or citation of `Q`.
4. **Preserve Hypotheses:** Track which assumptions are transported through the reduction.
5. **Return to the Original Goal:** Explicitly conclude the original claim, not just the reduced statement.

**Common Failure Modes:**
- Proving only one direction of an equivalence.
- Reducing to a statement that is not actually known.
- Losing side conditions during conjugation, localization, normalization, or passage to a special case.
