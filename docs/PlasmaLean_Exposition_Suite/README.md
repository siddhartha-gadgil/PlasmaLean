# PlasmaLean Exposition & Pure-Mathematics Onboarding Suite

This package is a self-contained website extension and documentation suite designed for direct integration into **[siddhartha-gadgil.github.io/PlasmaLean/](https://siddhartha-gadgil.github.io/PlasmaLean/)**.

## Contents of the Suite

1. **`index.html`** — Main hub linking all 4 exposition pillars, pure math bounties, and slides.
2. **`rosetta-stone.html` & `markdown/ROSETTA_STONE.md`** — **Suggestion 1**: Interactive 3-column Rosetta Stone mapping 14 core stellarator physics concepts to pure Topology, Differential/Symplectic Geometry, and Complex Geometry alongside exact Lean 4 kernel declarations.
3. **`blueprint-dag.html`** — **Suggestion 2**: Interactive SVG Formalization Blueprint & Dependency DAG across the workstreams, showing Kernel Contracts, Non-Vacuity Sanity Checks, Compiled Proofs, and Open Math Targets.
4. **`kernel-audit.html` & `markdown/KERNEL_AUDIT_GUIDE.md`** — **Suggestion 3**: "Audit the Small Kernel in 10 Minutes" split-pane interactive guide explaining the De Bruijn criterion for physical models and how sanity checks prevent vacuous specifications.
5. **`certificate-anatomy.html` & `markdown/CERTIFICATE_WALKTHROUGH.md`** — **Suggestion 4**: 5-stage walkthrough of the compiled **Tolerance-Aware Vacuum-Fixture Certificate**, paired with an interactive Biot–Savart Lipschitz tolerance calculator.
6. **`math-challenges.html` & `lean_stubs/Challenge1..6.lean`** — **Pure Math Onboarding**: 6 self-contained Lean 4 micro-bounty stubs tailored for researchers in **Topology**, **Differential/Symplectic Geometry**, and **Complex Geometry**.
7. **`slides-onboarding.html`** — Interactive **Reveal.js** slide deck suitable for geometry/topology seminars and contributor onboarding.
8. **`style.css`** — Shared dark-mode scientific stylesheet matching the existing `PlasmaLean` site.

## How to Integrate into `PlasmaLean`
Copy the HTML files, `style.css`, `markdown/`, and `lean_stubs/` into the root of your GitHub Pages branch (or under an `/exposition/` directory) and add a link in your main `<nav>` bar to `rosetta-stone.html` or `index.html`.
