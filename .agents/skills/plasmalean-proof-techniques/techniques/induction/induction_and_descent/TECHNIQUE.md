# Skill: Induction, Minimal Counterexample, and Descent

**Pre-condition:** Apply this skill when the statement is indexed by natural numbers, recursively defined structures, well-founded orders, or when a smallest counterexample can be chosen.

**Goal:** Prove a family of statements by a well-founded step principle, or refute counterexamples by descending to a smaller one.

**Instructions:**
1. **Identify the Index:** Determine whether the proof should use ordinary induction, strong induction, structural induction, minimal counterexample, or infinite descent.
2. **State the Induction Predicate:** Write the exact property `P(n)` or `P(x)` being proved.
3. **Base Cases:** Prove every minimal case required by the recurrence or constructor list.
4. **Step Case:**
   - Ordinary induction: assume `P(n)`, prove `P(n+1)`.
   - Strong induction: assume `P(k)` for all `k < n`, prove `P(n)`.
   - Structural induction: handle every constructor and use induction hypotheses for recursive arguments.
5. **Counterexample Variant:** Assume a least counterexample, use minimality to prove all smaller cases, then contradict failure at the least case.
6. **Descent Variant:** From any counterexample, construct a strictly smaller counterexample and cite well-foundedness.

**Common Failure Modes:**
- Choosing ordinary induction when the step needs several previous cases.
- Omitting constructor cases in structural induction.
- Failing to prove the descent is strict and remains inside the same domain.
