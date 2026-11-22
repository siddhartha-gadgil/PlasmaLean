---
name: plasmalean-try-to-prove
description: Attempt a proof of a precisely stated mathematical claim with the reasoning loop. Invoke for requests such as "try to prove ...", "prove that ...", "attempt a proof of ..." or "try to prove N-...". Runs `plasmalean-reasoning-loop` in problem-solving mode and writes all work to a task folder under notes/reasoning/.
---

# Try to prove a claim

1. **Identify the claim.** It may be given in words or LaTeX, or as a project item (`N-*`, `Q-*`,
   a conjecture in a research brief). Copy it verbatim into the task card, with the item it came
   from. If it is too vague to have fixed hypotheses and a fixed goal, say so and offer
   `plasmalean-explore-mathematics` instead, or ask for the missing hypotheses.
2. **Set the modes:**
   - objective `PROBLEM_SOLVING`;
   - verification `WITH_LEAN` by default, since this is a Lean project; use `INFORMAL_ONLY` when
     the user asks for an informal or paper proof, or when the statement needs definitions that
     do not yet exist in Lean, and record that reason;
   - execution `INTERACTIVE` by default; `AUTONOMOUS` when the user asks to run without stopping
     or is in `keep working` mode.
3. **Run `plasmalean-reasoning-loop`** with these modes. It creates
   `notes/reasoning/<YYYY-MM-DD>-<slug>/`, runs the phases, recurses on hard lemmas and
   terminates with a final manuscript or a failure report.
4. **Report** the outcome and its evidence state (refuted, proof-ready, or lean-ready with the
   draft file and check command), the task folder, and next choices: for a lean-ready or
   proof-ready result, promotion into the library with `plasmalean-formalize-theory`; for a failure, the
   precise obstacle as a question to explore or a weaker statement to try.

A proof found here is not a verified project result until it is formalized in `PlasmaLean/` and
passes the validity gate.
