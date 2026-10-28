---
name: formalize-theory
description: Formalize sourced mathematical results in Lean for a LeanTheory-based formalization and build reusable theory above its domain kernel. Use for geometry, dynamics, analysis, PDE or stability results, error bounds, or engineering theorems taken from literature or a complete mathematical proof.
---

# Formalize theory

## Load only the relevant material

Read `notes/domain-libraries.md`, the actual kernel modules, `notes/formalization/00-model-contracts.md` and the relevant existing theory in `LeanTheory/Theory/`. Resolve paths relative to the selected repository even when this skill is installed globally. If supporting notes are absent, state the narrower available context.

## Extract a source theorem before coding

Retrieve the primary paper or book chapter, including corrigenda and relevant supplements. Record authors, title, stable identifier, version, theorem/equation locator and retrieval date. Reconstruct the result in your own words and identify every geometric, analytic, boundary, normalization and model hypothesis. If only an abstract is available, record a literature lead; do not assert a theorem from the abstract.

Distinguish published theorem, formal asymptotic calculation, numerical result and empirical fit. Check signs, unit factors, normalization conventions, and whether the conclusion is necessary, sufficient, local or asymptotic.

## Design the Lean statement

1. Write the intended informal theorem and its intended use.
2. Search existing declarations in the pinned dependencies with `rg` and inspect their signatures.
3. Choose the weakest adequate analytic interface: algebraic identities before PDE existence; an abstract quadratic form before the full operator; a fixed domain before a moving one.
4. State model laws as explicit hypotheses or typeclass arguments, following the kernel pattern (`OscillatorLaw` in `LeanTheory/Kernel/Example.lean`).
5. Choose spaces, measures, boundary traces, coordinate domains and regularity. Explain any restriction in the name and docstring.
6. List missing lemmas as a dependency graph. Keep mathematical infrastructure in reusable `Theory` modules rather than inside one design proof.

Use Euclidean domains first when differential geometry would delay a useful result; add a manifold bridge through a theorem when needed. Do not assume that anticipated Sobolev, trace, differential-form, spectral or PDE APIs already exist in Mathlib.

## Build and verify incrementally

Prove prerequisite lemmas, then the theorem, then corollaries and sanity cases. Check a file with `lake env lean <path>`; build changed modules one at a time (`lake build <module>`), and the library only when dependencies are fresh. Do not claim successful compilation if the toolchain or dependency retrieval blocks it.

Use docstrings for every definition and theorem and a module docstring describing the model. Use `simp`, `norm_num`, `linarith`, `nlinarith`, `grind`, `fun_induction` and other proof-producing tactics; search for a conceptual lemma before brute-force unfolding. Follow `lean-proofs` for tactic choice and for concrete checks: no `decide` of any kind. Keep the library free of `sorry`, `admit`, new axioms and unchecked external numerical oracles. Do not put an assumption equivalent to the desired conclusion inside a misleadingly named law bundle.

Inspect `#print axioms` for important public results and add certificate entry points to `scripts/check_axioms.lean`; only `propext`, `Classical.choice` and `Quot.sound` are allowed.

## Preserve the theorem's meaning

Recheck the informal statement against the final Lean declaration. Verify that a nonempty admissible class remains (a concrete instance, as in `LeanTheory/Sanity/Example.lean`), that the chosen norm is the advertised one, and that boundary terms and symmetry modes have not disappeared through an unjustified restriction. A result on a finite subspace must say so in its name.

Deliver the source locator, declaration names, assumptions, compiled checks, sanity theorems, remaining dependencies and the next target. Label sketches and unformalized source results separately from verified library code.
