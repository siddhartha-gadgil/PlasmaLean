# PlasmaLean
Lean and AI-assisted mathematics toward verified stellarator design.

The library now contains explicit restricted MHD and thermal model laws, analytic
sanity cases, energy/form inequalities, exact certificate soundness, continuous
clearance and filament-field bounds, synthetic validation examples, and an exact
small two-loop vacuum-field fixture with a proved on-axis field. It does
**not** yet certify a practical stellarator, toroidal equilibrium, or all-mode MHD
stability. See the [progress and assumption ledger](progress/2026-10-12-progress.md).

## Build and audit

Lean and Mathlib are pinned to v4.34.1. From the repository root:

```sh
lake build
lake env lean scripts/check_axioms.lean
node scripts/generate_handbook.mjs
node scripts/check_site.mjs
```

Import `PlasmaLean` for the public library, or a specific module. The architecture
separates `Kernel`, `Sanity`, `Theory`, `Certificates`, `Bridge`, and labelled
`Design` fixtures. Model laws are hypotheses, not new axioms. The audit rejects
unexpected logical axioms in every declaration owned by a project module.

## Read the program

The [website](docs/index.html) retains the original motivations and interactive
graphics and links to the [handbook](docs/handbook.html) and task progress. Source
plans live in [notes/domain-libraries.md](notes/domain-libraries.md) and
[notes/formalization/](notes/formalization/08-roadmap.md). They retain their original
planning context; the dated progress ledger identifies subsequent compiled work.
