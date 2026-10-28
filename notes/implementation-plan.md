# Implementation plan: theory → proof techniques → successively realistic models

Skeleton of the plan of record. Replace every ‹…› slot with your domain; keep the section order.
Each section has one or two lines of guidance.

## 0. Goals and current status

‹State the main goals (G1, G2, …) as precise target theorems or contracts
(`notes/formalization/00-model-contracts.md`), and one paragraph on where the project stands.›

## 1. Corrections to the starting notes

‹List claims from the starting notes that are false or underspecified as written, each with its
precise replacement. Do these first: formalizing them as written would be unsound.›

## 2. Layers

‹Describe the three interacting layers: theory (results above the kernel), proof techniques
(certificate formats and checkers) and the model ladder (§5).›

### 2.1 Kernel extensions

‹Planned kernel additions: minimal, laws as typeclasses only, no axioms, each with its sanity
triad (degenerate case, instance, counterexample).›

## 3. Running a cycle

‹One run in the sense of `notes/domain-libraries.md`: pick targets, formalize, certify, audit
(`lake build`, `scripts/check_axioms.lean`), record in §9 and §13.›

## 4. Theory tracks

‹Table of theory tracks, each with its technique companion (which certificate or checker makes
it effective) and its first deliverable.›

## 5. Model ladder

‹Rungs from the simplest model to the most realistic one; for each rung, which goals it addresses
and what must be proved to climb to the next (reduction theorems or error envelopes).›

## 6. Cycle schedule

‹Ordered cycles (Cycle 1, Cycle 2, …), each naming its rung, tracks and expected outputs.›

## 7. Sub-agent prompt template

‹A reusable prompt for delegated work: goal, files to read, scope, what is already ruled out,
the policies (no decide, standard axioms, zero warnings, ≤ 6 GB per process), and the report
format.›

## 8. Definition of done

‹Per cycle: statements compiled with docstrings and sanity theorems, zero warnings, axiom audit
passed, entry points registered, notes and progress log updated, honest scope statement.›

## 9. Progress log

‹One dated entry per phase: what was proved (declaration names), what failed and why, checks
run, next targets.›

## 10. Evidence gates

‹For each claim headed to a design: which contracts must hold for the same witness, and which
evidence (proof, certificate, external validation) is required at each gate.›

## 11. Implementation log

‹Technical notes per stage: certificate formats introduced, build-time and memory measurements,
refactors, workstation runs (see `workstation/REVIEWED.md`).›
