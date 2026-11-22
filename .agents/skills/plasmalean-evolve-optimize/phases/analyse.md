# Analyse the population

Before generating generation `g`, study generation `g - 1` and write
`generations/gen-(g-1)/analysis.md`. The quality of the next generation depends on this step: it
turns scores and error messages into ideas.

Read `population.json`, the files of the members and near misses, and the results of the last
generation (`results.jsonl`: validity, reasons, scores, messages with their line in the
candidate). Then answer, concretely and with references to candidate ids:

1. **What makes the best candidates good?** Compare the top members with each other and with
   weaker ones: shared structure of the term, parameter values, symmetries, patterns in the data.
   Relate features to scores. Compute small statistics with `plasmalean-evaluate-on-server` when useful.
2. **Why do their constraints hold, and how were they proved?** For each constraint, record the
   proof patterns that worked (tactics such as `simp [candidate]`, `norm_num`, `omega`, `decide`,
   `kernel_fact`, or a lemma and its use) and on which kinds of candidates. Note when a proof
   depends on a structural property of the term rather than on computation: such properties
   suggest families of candidates that are valid by construction.
3. **Why did the others fail?** Group invalid candidates by reason: forbidden constructs,
   candidates that do not elaborate, measures not computed, and failed proofs. For each near miss,
   decide whether the constraint is actually violated (check the statement on the candidate, for
   example by evaluating a decidable version, or with `plasmalean-examples-counterexamples`) or only the proof
   failed. Unrepairable near misses should not be used as parents for repair.
4. **Where is the frontier?** The best score, how it moved over recent generations, and what
   limits it: a constraint that becomes tight, a representation that cannot express better
   terms, proofs that do not scale to larger candidates.
5. **Plan for the next generation.** A list of directions, each with the parents to use and the
   expected effect, and how to split the candidates between them: small mutations of the best
   (exploitation), new ideas or representations (exploration), proof repair of promising near
   misses, and recombination of features from different good candidates.

Append the lasting lessons to the run's cumulative `insights.md`: features that correlate with
high scores, proof patterns per constraint, recurring errors with their fixes, and dead ends. Keep
observations and conjectures apart, as in the rest of the project.
