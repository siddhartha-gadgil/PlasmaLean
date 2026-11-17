---
name: plasmalean-explore-mathematics
description: Explore an open-ended mathematical question with the reasoning loop, producing ranked questions, probes, examples, stress-tested conjectures and a research brief. Invoke for requests such as "explore ...", "what can be said about ...", "find conjectures about ...", "generalize ..." or "explore Q-...". Runs `plasmalean-reasoning-loop` in exploratory research mode and writes all work to a task folder under notes/reasoning/.
---

# Explore a mathematical question

1. **Identify the seed:** a topic, a theorem to extend or vary, a question `Q-*`, a note `N-*`, or
   an obstacle from an earlier failure report. Copy it verbatim into the task card with the item
   it came from.
2. **Set the modes:**
   - objective `EXPLORATORY_RESEARCH`;
   - verification `INFORMAL_ONLY` by default, labelling conjectures `supported`, `refuted`,
     `needs_hypotheses` or `open`; `WITH_LEAN` when the user asks for Lean checks, for example
     of explicit counterexamples or small lemmas;
   - execution `INTERACTIVE` by default; `AUTONOMOUS` when the user asks to run without stopping
     or is in `keep working` mode.
3. **Run `plasmalean-reasoning-loop`** with these modes. It creates
   `notes/reasoning/<YYYY-MM-DD>-<slug>/`, formulates and ranks questions, runs probes and
   stress tests, and terminates with a research brief or an obstacles report. When metacognition
   reaches `THEOREM_MODE`, it continues as a proof attempt on the emerging theorem, as
   `plasmalean-try-to-prove` would.
4. **Report** the strongest supported conjectures with their evidence, refuted candidates and
   their counterexamples, the example ledger, and next choices, each a possible `plasmalean-try-to-prove` or
   further `plasmalean-explore-mathematics` task.

Exploration produces questions and conjectures, never established results. Conjectures worth
keeping become `Q-*` or `N-*` entries in the research graph, as described in `plasmalean-reasoning-loop`.
