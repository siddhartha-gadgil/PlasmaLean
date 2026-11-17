---
name: plasmalean-evolve-optimize
description: Evolutionary optimization of Lean terms with proved constraints, in the AlphaEvolve pattern. A candidate is a package of Lean code defining a term of a given type and proving the required properties; the task server checks the proofs and computes a measure to maximize or minimize. Keeps a population of good candidates, analyses why they score well and why their proofs work, generates many new candidates (with sub-agents), evaluates and selects. Invoke for "evolve ...", "optimize ... subject to ...", or "search for a ... maximizing/minimizing ..." when the result must come with proofs.
---

# Evolve optimal terms with proved constraints

The evaluation is automatic and trusted only as far as Lean checks it; generating candidates is the
creative part done by agents. The loop follows AlphaEvolve: keep a population of the best
candidates, study what makes them good and why their constraints could be proved, generate many
variations and new ideas, evaluate them all on the server, and select.

Tools: `scripts/evolve/evolve.py` (evaluation, selection and bookkeeping; standard-library Python),
the task server (`plasmalean-ensure-theory-server`), and for quick experiments `plasmalean-check-compilation` and
`plasmalean-evaluate-on-server`. Phases: `phases/analyse.md` and `phases/generate.md`. A worked example is in
`example/`.

## 1. The problem and the run folder

A run is a reasoning task folder `notes/reasoning/<YYYY-MM-DD>-evolve-<slug>/` with the
`README.md` task card and `log.md` of `plasmalean-reasoning-loop`, and the files of `evolve.py`. Create it with
`python3 scripts/evolve/evolve.py init <folder>` and write:

- `problem.json`: `name`, `description`, `objective` (`maximize` or `minimize`), the Lean `type` of
  the term, the `measure` (a Lean term in `candidate` of type `ℕ`, `ℤ`, `ℚ` or `Float`, whose
  `toString` is a number), and `constraints`, each with a `name` (a Lean identifier), a
  `statement` (a proposition in `candidate`) and a `description`. Settings: `population_size`
  (default 8), `near_miss_size` (default 4), extra `forbidden` regular expressions.
- `context.lean`: definitions the measure and constraints use (no imports; the server has
  Mathlib and PlasmaLean).
- Seeds in `generations/gen-000/candidates/`: a few simple, diverse candidates and any known
  constructions from the literature.

A candidate file defines `candidate : <type>` and one theorem per constraint, named exactly as in
the problem, proving its statement for `candidate`. It may define helper functions and lemmas.
Optional first lines record lineage: `-- evolve: parents = …`, `-- evolve: strategy = …`,
`-- evolve: idea = …`.

Before evolving, sanity-check the problem as for a kernel law (`plasmalean-examples-counterexamples`, and the
red-team checklist of `plasmalean-audit-domain` for units, normalizations and degenerate data):
evaluate the measure on known examples with `plasmalean-evaluate-on-server`, and check that candidates
violating each constraint really fail it. A badly stated constraint makes the whole search
optimize the wrong thing. Make the problem finite where possible: bound sizes by constraints, so
that the measure terminates quickly on every candidate (evaluation has no time limit yet).

## 2. How a candidate is judged

`evolve.py evaluate` builds, for each candidate, the package context + preamble + candidate +
harness, and sends it to the server in one `assess` request that leaves the server environment
unchanged:

- the **preamble**, before the candidate, defines the measure (as a string) and each constraint
  statement as a function of `candidate`, so nothing the candidate declares (instances, notation,
  opened namespaces) can change their meaning;
- the **harness**, after it, checks that `candidate` has the type and that each named proof proves
  the fixed statement for `candidate`;
- the server reports errors, the axioms of each check, and the measure, computed whenever the
  candidate itself is clean, even if some proof fails.

A candidate is **valid** when the package compiles with no errors and no `sorry`, and the
candidate and every constraint proof use only `propext`, `Classical.choice` and `Quot.sound`
(this rejects `sorry` hidden in a helper lemma and `native_decide`). Before sending, the script
rejects forbidden constructs that could fake proofs, hide computation or run code on the server:
`sorry`, `axiom`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`, `native_decide`,
commands such as `#eval` and `run_cmd`, new syntax or elaborators, imports, heartbeat or recursion
options, and names starting with `evolve_`.

Selection keeps the `population_size` best distinct valid candidates (ties broken by shorter
code) and up to `near_miss_size` **near misses**: the best-scoring candidates whose measure was
computed but some proof failed. Near misses are where proof repair pays off; some are
unrepairable because the constraint is actually violated, which the analysis must decide.

## 3. The generation loop

Run generation 0 with `evaluate` and `select`, then repeat for generation `g = 1, 2, …`:

1. `python3 scripts/evolve/evolve.py next <folder>` creates `generations/gen-g/candidates/` and
   lists the parents.
2. **Analyse** the population following `phases/analyse.md`, and write
   `generations/gen-(g-1)/analysis.md`; update the cumulative `insights.md` of the run.
3. **Generate** many candidates following `phases/generate.md`. Launch several sub-agents in
   parallel, each with its own strategy, parents and file prefix, so that they write disjoint
   files; without sub-agents, generate them yourself. Aim for a few dozen candidates per
   generation, mixing exploitation, exploration and repair.
4. **Evaluate**: `python3 scripts/evolve/evolve.py evaluate <folder>` (the server must be
   running; it evaluates one candidate at a time).
5. **Select**: `python3 scripts/evolve/evolve.py select <folder>`; the best package so far is in
   `best/package.lean`.
6. Record in `log.md`: candidates, valid count, best score and whether it improved, and the main
   lesson. In interactive mode report and ask whether to continue; in autonomous mode continue.

Use `evolve.py status <folder>` for the progress per generation and `evolve.py try <folder>
<file>` to evaluate one file without recording it. Stop at the generation budget agreed with the
user, after two or three generations without improvement (then change the approach: new
representations, a different decomposition, or a relaxation), when a proved bound shows the best
is optimal, or when the user stops.

## 4. Results, evidence and promotion

Write `05_evolution_report.md`: the best package and its score, its lineage, the score history,
the insights (what makes candidates good, which proof patterns work), open near misses, and the
next ideas. Keep the evidence states of `plasmalean-reasoning-loop` distinct:

- the constraint proofs of a valid candidate were checked by Lean on the server: **lean-ready**;
- its score was computed by compiled evaluation, which is evidence, not a proof;
- nothing shows the score is optimal: the best score is only a bound (a lower bound when
  maximizing). Optimality is a separate question for `plasmalean-try-to-prove` or `plasmalean-explore-mathematics`.

To make the result **verified**, promote the best package into the library with
`plasmalean-formalize-theory` and `plasmalean-lean-proofs`: a module, for example in `PlasmaLean/Design/`, with the
context, `candidate`, the constraint theorems, and a theorem fixing its measure
(`measure candidate = v`, or the bound) proved by the kernel (`norm_num`, `rfl`, `kernel_fact`,
following the no-`decide` policy, which also applies to proofs carried over from candidates).
Build it within the laptop budget (stop the server first if the module is heavy) and pass the
axiom audit; add the module to `PlasmaLean.lean` only if it is light enough for the default build,
otherwise make it an on-demand module under the workstation policy. Then register the outcome in
the research graph as described in `plasmalean-reasoning-loop` (with `plasmalean-add-note`).

## Uses in the project

Searches are often launched from other work: `plasmalean-examples-counterexamples` and the existence
technique of `plasmalean-proof-techniques` assess whether a search could find a counterexample or a witness,
and if so launch this skill with a sub-agent in parallel, with a budget. When running as such a
sub-agent, stay within the budget, generate candidates yourself if you cannot launch sub-agents,
and report the best package, its score, whether the target property was proved, and the insights.

- Constructions and designs: parameters, shapes or schedules that satisfy proved constraints and
  optimize a figure of merit (`plasmalean-design-stellarator`). In PlasmaLean the term is exact
  data (rationals, lists of Fourier or coil coefficients, cell lists), the constraints are the
  checkable conditions of a gate (an inequality checked by a certificate, a separation, a bound
  on a parameter box), and the measure is a margin, for example the certified lower bound of an
  energy form or the distance of a coil from the plasma. A noncomputable quantity over `ℝ` cannot
  be a measure: use its exact rational enclosure from `PlasmaLean/Certificates/`.
- Resources: the server and evaluation obey the laptop budget (`plasmalean-ensure-theory-server`).
  A run of a few dozen small candidates per generation suits the laptop; searches whose
  candidates need heavy certificate checks go to the workstation (`Workstation.md`). Sub-agents
  generating candidates must not run `lake build` while the server is up.
- Counterexamples and witnesses: an extremal object, or a certificate for a bound
  (`plasmalean-certify-numerics`), where the constraint is the property that must be proved.
- Discovery: when the best candidates share a structure, state it as a conjecture
  (`plasmalean-explore-mathematics`) and try to prove it in general (`plasmalean-try-to-prove`).
