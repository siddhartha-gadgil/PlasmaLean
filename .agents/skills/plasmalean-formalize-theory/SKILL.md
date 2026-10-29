---
name: plasmalean-formalize-theory
description: Formalize sourced mathematical results for PlasmaLean in Lean and build reusable theory above its domain kernel. Use for geometry, MHD equilibrium or stability, guiding-centre dynamics, transport, error bounds, or engineering theorems taken from literature or a complete mathematical proof.
---

# Formalize plasma theory

## Load only the relevant material

Read `notes/domain-libraries.md`, the actual kernel modules, `notes/formalization/00-model-contracts.md`, the topic note, and the corresponding entries in `09-literature.md`. Resolve these paths relative to the selected PlasmaLean repository even when this skill is installed globally. If the supplementary notes are absent, use the source links in the project notes and state the narrower available context. Also read the originating research note and its entry in the research graph of `notes/implementation-plan.md`.

**Dependency gating.** Confirm that every required upstream result has a named compiled declaration (default build, or an on-demand module accepted under the workstation policy). If a dependency is only conjectural, sketched or sourced, do not silently formalize downstream of it as if it were established: formalize the prerequisite first, or keep the theorem explicitly conditional (the dependency as a named hypothesis, the conditional status in the name or docstring and in the note).

## Extract a source theorem before coding

Retrieve the primary paper or book chapter, including corrigenda and relevant supplements. Record authors, title, stable identifier, version, theorem/equation locator, and retrieval date. Reconstruct the result in your own words. Identify every geometric, analytic, boundary, normalization, and model hypothesis. If only an abstract is available, record a literature lead; do not assert a theorem from the abstract.

Distinguish published theorem, formal asymptotic calculation, numerical result, and empirical fit. Follow `09-literature.md`'s extraction protocol. Check signs, SI factors, Fourier conventions, and whether the conclusion is necessary, sufficient, local, or asymptotic.

## Design the Lean statement

1. Write the intended informal theorem and its intended design use.
2. Search existing declarations in the pinned dependencies with `rg` and inspect their signatures.
3. Choose the weakest adequate analytic interface: algebraic identities before PDE existence; an abstract quadratic form before the full MHD operator; a fixed boundary before a moving interface.
4. State model laws as explicit hypotheses or typeclass arguments, following the project architecture.
5. Choose spaces, measures, boundary traces, coordinate domains, and regularity. Explain any restricted theorem in its name and docstring.
6. List missing mathematical lemmas as a dependency graph. Keep mathematical infrastructure in reusable modules rather than embedding it inside one design proof.

Use Euclidean domains first when differential geometry would delay a useful result. Introduce a manifold bridge through a theorem when needed. Do not assume that anticipated Sobolev, trace, differential-form, spectral, or PDE APIs already exist in Mathlib or TauCeti.

## Build and verify incrementally

Prove prerequisite lemmas, then the theorem, then useful corollaries and sanity cases. Check a file with `lake env lean <path>`; build changed modules one at a time (`lake build <module>`), and the library only when dependencies are fresh. Keep each Lean process within 6 GB, and build stale dependencies one at a time (`lake build --no-build <Top>` lists them); heavy first builds go to the workstation. Do not claim successful compilation if dependency retrieval, the toolchain or the resource budget blocks it.

Use docstrings for every definition and theorem and module documentation describing the model. Use `simp`, `norm_num`, `linarith`, `nlinarith`, `grind`, or other proof-producing tactics when appropriate; search for a conceptual theorem before brute-force unfolding. Follow `plasmalean-lean-proofs` for tactic choice (`grind`, `fun_induction`) and for concrete checks (`kernel_fact`, `bool_cert`, `eval_cert`/`fiv_cert`, the SubsetSum pattern): no `decide` of any kind in new code. Keep completed library results free of `sorry`, `admit`, new project axioms, and unchecked external numerical oracles. Do not put an assumption equivalent to the desired conclusion inside a misleadingly named law bundle.

Inspect `#print axioms` for certificate entry points and important public results, and add them to `scripts/check_axioms.lean` (on-demand modules: `scripts/check_axioms_heavy.lean`); only `propext`, `Classical.choice` and `Quot.sound` are allowed. Distinguish standard Lean/Mathlib logical axioms from new project axioms and additional execution trust. Record any extra trust explicitly; prefer kernel-checkable proof terms for certificate arithmetic.

## Preserve the theorem's meaning

Recheck the original informal statement against the final Lean declaration. Verify that a nonempty admissible class remains, that the chosen norm is the one advertised, and that boundary terms and symmetry modes have not disappeared through an unjustified restriction. A stability theorem on a finite subspace must retain that scope in its name.

Deliver the source locator, declaration names, assumptions, compiled checks, useful sanity theorems, remaining dependencies, and the next target. Label sketches and unformalized source results separately from verified library code.

**Update the note graph and the plan after every work unit, including failures.** Record in the originating note and in the registries of `notes/implementation-plan.md` the declaration names, assumptions, build status (default or on-demand), compiled checks, barriers and newly ready notes, with a dated §13 entry for plan-relevant results. A failed formalization goes back to the note as information: a missing hypothesis, a false statement, an unsuitable definition or a library gap.

## Finish the stage

After each completed stage of progress (including a recorded failure or barrier), follow the reporting
protocol in `notes/domain-libraries.md`: update the notes and plan registries, refresh
`progress/slideshow.json` (and the progress report when substantive), regenerate and check the site
(`node scripts/generate_handbook.mjs`, `node scripts/check_site.mjs`), then commit with explicitly
staged paths and `git push`.
