---
name: plasmalean-reasoning-loop
description: Run the mathematical reasoning loop (deconstruct, triage, strategy or probes, execute, verify, metacognition, terminate) on one proof attempt or exploratory investigation in PlasmaLean, writing every artifact to a task folder under notes/reasoning/. Launched by `plasmalean-try-to-prove` and `plasmalean-explore-mathematics`; use directly when a note needs a structured proof attempt, recursive sub-lemmas, or a conjecture search.
---

# Mathematical reasoning loop

The loop is the detailed engine for mathematical discovery. `plasmalean-try-to-prove` launches it in
problem-solving mode and `plasmalean-explore-mathematics` in exploratory mode; `plasmalean-discover-theory` and
`plasmalean-develop-theory` may launch it for a single note. Its phases live in `phases/`, structured output
formats in `schemas/`, example construction in `plasmalean-examples-counterexamples` and the technique
library in `plasmalean-proof-techniques`.

## Configuration

Record the three modes in the task card before starting.

- **Execution:** `INTERACTIVE` (default) pauses after every phase, reports, and asks how to
  continue. `AUTONOMOUS` runs to termination; use it when the user says so or is in
  `keep working` mode.
- **Verification:** `WITH_LEAN` checks steps in Lean; `INFORMAL_ONLY` uses peer-review style
  checks. The entry skills choose defaults.
- **Objective:** `PROBLEM_SOLVING` for a well-stated theorem, exercise or lemma with fixed
  hypotheses and goal. `EXPLORATORY_RESEARCH` for open-ended requests: extend a theorem, find
  variants, formulate questions, search for conjectures or map a research direction. `AUTO` keeps
  problem solving whenever the input contains a precise claim to prove, and branches to
  exploration only when no fixed target is present or the user asks for questions or conjectures.

## The task folder

Every output of the loop goes in one folder per task:
`notes/reasoning/<YYYY-MM-DD>-<short-slug>/`, written `<task>/` in the phase files. Reuse the
folder when the task is resumed. Its layout:

| File | Contents |
| --- | --- |
| `README.md` | Task card: the input verbatim, modes, linked `G-*`/`Q-*`/`N-*` items, status, outcome, artifact index |
| `log.md` | Dated log: phases entered, triage and metacognition decisions, commands run and their results |
| `01_problem_formalization.md` | Givens, hypotheses, goal, definitions, intuition, classification, seeds |
| `02_examples.md` | Early examples, boundary cases and candidate counterexamples |
| `02_literature_review.md` | Source study |
| `02_research_questions.md` | Ranked research questions (exploratory) |
| `03_strategy_plans.md` | Proof plans with step difficulties (problem solving) |
| `03_exploration_plan.md` | Planned probes (exploratory) |
| `04_execution_trace.md` | Executed and verified proof steps (problem solving) |
| `04_research_trace.md` | Probe results and stress tests (exploratory) |
| `05_final_manuscript.md` | Complete proof, when problem solving succeeds |
| `05_failure_report.md` | Why problem solving stopped, with the precise obstacle |
| `05_research_brief.md` | Synthesis of an exploration |
| `05_research_obstacles.md` | Blockers, failed conjectures and next probes, when exploration stalls |
| `lean/` | Lean drafts checked in `WITH_LEAN` mode |
| `computations/` | Scripts and outputs of exploratory computations |
| `subtasks/<slug>/` | Recursive loops on `hard` steps, with the same layout |

Create `README.md` and `log.md` first. Write nothing outside the task folder during the loop: no
library code, no edits to other notes. The only exception is the registration at termination
below.

## Before starting

Read `notes/implementation-plan.md` and any linked note, goal or question. Identify which
prerequisites are verified Lean declarations and which are only notes: an unverified note may be
used only as an explicitly conditional premise. If the claim concerns the domain model, read the
relevant kernel modules (`PlasmaLean/Kernel/`) and `notes/formalization/00-model-contracts.md`
so that the formalization uses the project's definitions, units and conventions.

## The loop

Follow the phases strictly, and update the task card and `log.md` at every milestone.

**Phase 1: formalization and triage.**
- Run `phases/01-deconstruct.md`, then `phases/02-triage.md`.
- If definitions are unfamiliar, hypotheses look sharp or the statement may be false, run
  `plasmalean-examples-counterexamples` and save to `02_examples.md`. In problem solving, examples are a
  sanity check only and never replace a proof.
- On `SOURCE_STUDY`, run `phases/03-source-study.md`. On `DIRECT_PROOF`, proceed.
- On `EXPLORATORY_RESEARCH`, run `phases/08-question-formulation.md`, and
  `phases/03-source-study.md` too if background is needed.

**Phase 2: strategy.**
- Problem solving: run `phases/04-strategy.md`, using `plasmalean-proof-techniques` and any recorded
  examples to discard false plans. Classify steps as `easy`, `standard` or `hard`.
- Exploratory research: run `phases/09-exploratory-probe.md` to write the exploration plan,
  classifying each probe by cost and type.

**Phase 3: execution engine.**
- Problem solving, for the selected plan, repeat:
  1. execute with `phases/05-execute-step.md`; a `hard` step starts a subtask loop, and a
     doubtful new lemma gets `plasmalean-examples-counterexamples` before a long proof;
  2. verify with `phases/06-verify.md` in the active verification mode;
  3. assess with `phases/07-metacognition.md`, and act on its decision.
- Exploratory research, for the selected question, repeat:
  1. probe with `phases/09-exploratory-probe.md`, using `plasmalean-examples-counterexamples` for
     constructions;
  2. stress-test emerging conjectures with `phases/10-conjecture-stress-test.md`;
  3. assess with `phases/07-metacognition.md` in research mode. On `THEOREM_MODE`, continue in
     problem solving with that theorem as the goal, in a subtask folder if the exploration should
     continue afterwards.

**Phase 4: termination.**
- Problem-solving success: write `05_final_manuscript.md`, a self-contained proof with every
  step's justification and verification status.
- Problem-solving stuck: write `05_failure_report.md`, with the plans tried, where each failed,
  any counterexample and the exact obstacle as a mathematical question.
- Research consolidation: run `phases/11-research-synthesis.md` and write `05_research_brief.md`.
- Research stuck: write `05_research_obstacles.md` with precise blockers, failed conjectures and
  promising next probes.

## Evidence states

The loop's outputs keep the project's evidence states distinct (`notes/domain-libraries.md`):

- an informally verified final manuscript is a complete argument: **proof-ready**;
- a proof whose statement and steps compiled as drafts in `lean/`, with standard axioms only, is
  **lean-ready**: the statement and proof route are checked, but the result is not yet part of
  the library;
- only after promotion into `PlasmaLean/` with `plasmalean-formalize-theory`, compilation in the default
  build and the required audit is a result **verified** and usable as an established premise;
- a counterexample checked against the exact definitions **refutes** the claim;
- conjectures from exploration are **stated** at most, never established.

## Registration at termination

Link the outcome into the research graph, so that later work can find it:

- if the task was launched for an existing `N-*`, `Q-*` or `G-*` item, add a short outcome and a
  link to the task folder in that note and in its row of `notes/implementation-plan.md`, as
  bookkeeping only (implemented notes keep their content; see `plasmalean-modify-notes`);
- otherwise, register the task as a new `N-*` note with `plasmalean-add-note` (RG.3 row whose
  file is the task card `<task>/README.md`, with the metadata of `notes/note-template.md`, the
  affected RG.1/RG.2 rows and a §13 log entry);
- record new conjectures and obstacles as `Q-*` candidates in the report, and add them to the
  registry only when the user agrees or in `keep working` mode;
- publish as in `plasmalean-add-note` §4: regenerate and check the site, commit with explicit
  paths (including the task folder) and push.

Then report: the outcome and its evidence state, the artifacts written, open obstacles, and ready
next choices such as formalizing a proof-ready result, trying to prove a conjecture, or a further
probe.
