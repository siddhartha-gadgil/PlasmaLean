# Generate candidates

Generation is done by the coordinating agent or, better, by several sub-agents working in
parallel. Give each sub-agent a brief like the one below, with a distinct strategy, its parents
and a distinct file prefix, so that the agents write disjoint files.

## Brief for a generator

> You are generating candidates for generation `<g>` of the evolutionary run in `<folder>`.
> Read `problem.json`, `context.lean`, `insights.md` and `generations/gen-<g-1>/analysis.md`, and
> the parent files listed below. Your strategy is: `<strategy>`. Parents: `<ids and files>`.
>
> Write `<n>` candidate files to `generations/gen-<g>/candidates/`, named `<prefix>NN_<word>.lean`
> (for example `b07_shift.lean`). Do not write anywhere else, and do not run `evolve.py evaluate`
> or `select`: the coordinator does that.
>
> Each file is Lean code that defines `candidate : <type>` and proves one theorem per constraint,
> named exactly `<constraint names>`, stating the constraint for `candidate`. Start the file with
> `-- evolve: parents = …`, `-- evolve: strategy = …` and `-- evolve: idea = …` (one line saying
> what changed and why it should help). Do not use `sorry`, `axiom`, `partial`, `unsafe`,
> `opaque`, `implemented_by`, `extern`, `native_decide`, `#eval` or other commands, imports,
> heartbeat or recursion options, or names starting with `evolve_`. Keep the measure fast to
> compute.
>
> You may check a candidate with `python3 scripts/evolve/evolve.py try <folder> <file>` (it does
> not record anything) and fix its errors, but spend most of your effort on new ideas rather than
> on polishing one file. Report the files written and, for each, its idea in one line.

## Strategies

Mix strategies within a generation, following the plan of the analysis:

- **Mutation:** a small change to one good parent: adjust parameters, swap or move parts, extend
  or shorten, apply a symmetry. Keep the parent's proofs working, adapting them minimally.
- **Exploration:** a new construction, representation or idea suggested by the analysis, the
  literature or an analogy, with its own proofs.
- **Recombination:** combine features of two or more good candidates.
- **Proof repair:** keep the term of a promising near miss whose constraint is actually satisfied,
  and find proofs that Lean accepts, using the proof patterns that worked elsewhere.
- **Generalization:** replace explicit data by a short definition that generates it (a formula, a
  recursion with structural termination), when the analysis shows a pattern; proofs about the
  pattern can scale better than proofs by computation.
- **Simplification:** a candidate with the same score and shorter code or simpler proofs; shorter
  candidates win ties and are easier to promote.

Prefer proofs that will survive promotion into the library: `simp`, `norm_num`, `omega`,
`kernel_fact` and lemmas, rather than `decide` (allowed in candidates, but forbidden in the
library by the project's policy).
