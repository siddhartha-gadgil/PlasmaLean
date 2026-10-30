# PlasmaLean Exposition & Pure-Mathematics Onboarding Suite

Hand-written pages, published as part of **[siddhartha-gadgil.github.io/PlasmaLean/](https://siddhartha-gadgil.github.io/PlasmaLean/)**. The site generator does not refresh them, so review them by hand after each phase. Last checked against the source on 30 October 2026: every Lean declaration presented as real was checked to exist, and anything not in the library is labelled as an illustrative sketch or a plan.

## Contents (7 HTML pages, 3 Markdown files, 6 Lean stubs)

1. **`index.html`**: hub linking the four pillar pages, the pure-mathematics invitations and the slides.
2. **`rosetta-stone.html`** and **`markdown/ROSETTA_STONE.md`**: a three-column dictionary of 14 stellarator concepts (physics, geometry, PlasmaLean). Each entry shows real declarations with module paths where they exist (5 in the library, 8 partly) and a labelled sketch where they do not (1).
3. **`blueprint-dag.html`**: an interactive picture of part of the research graph of the [implementation plan](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/implementation-plan.md): 4 kernel laws, 5 compiled results, 5 questions (Q-16, Q-18, Q-19, Q-20, Q-21) and 5 goals (G-1, G-2, G-4, G-8, G-10) of the stellarator contract. It is drawn by hand and may lag behind the plan.
4. **`kernel-audit.html`** and **`markdown/KERNEL_AUDIT_GUIDE.md`**: a 10-minute guide to the six kernel modules (`PlasmaLean/Kernel/{Equilibrium, Slab, ThermalSlab, Vacuum, Transport, Fusion}.lean`, about 900 lines), their sanity theorems, and the [strict kernel audit of 30 October 2026](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-kernel-audit.md).
5. **`certificate-anatomy.html`** and **`markdown/CERTIFICATE_WALKTHROUGH.md`**: a 5-stage walkthrough of the field-error and clearance certificate for the two-loop calibration fixture (`Design/VacuumPair`, `Design/VacuumTolerance`, `Design/VacuumDerivative`, `Design/VacuumPairVolumeError`), with a calculator that evaluates the proved bounds. The fixture is axisymmetric and makes no confinement claim.
6. **`math-challenges.html`** and **`lean_stubs/Challenge1..6.lean`**: six self-contained Lean 4 invitations for topology, differential and symplectic geometry, and complex geometry. Challenge 6 is partly done in the library in the constant-metric case (`Theory/Geometry/TorusHodge`); Challenge 1 overlaps the kernel (`field_tangency`, `current_tangency`) and the explicit torus map of the Grad counterexample (`Design/LandremanGradCounterexample`).
7. **`slides-onboarding.html`**: a 10-slide Reveal.js deck for seminars and contributor onboarding, including the stellarator contract C1–C5.
8. **`style.css`**: shared stylesheet.
