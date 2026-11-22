# Examples: Composition of Contracts on a Common Witness

## Example 1: A robust design over an operating range

**Problem shape:** Show a design is an equilibrium, stable, confined and within component limits
for every parameter `θ` in an operating box `U`.

**Use of technique:**
1. Choose a branch `θ ↦ branch θ` of equilibria (for example from a fixed-point certificate at
   each `θ`, see `certificate_reduction`).
2. Prove `C.equilibrium`, `C.stability`, `C.transport` and `C.components` for `branch θ`, for all
   `θ ∈ U`.
3. Conclude `RobustDesign C d U` by `compose_branch` (`PlasmaLean/Bridge/Contracts.lean`).

## Example 2: Composition from uniqueness

**Problem shape:** Existence of an equilibrium, stability and transport were proved in separate
modules, each with its own existential witness.

**Use of technique:**
1. Prove uniqueness of the equilibrium in the relevant class (for instance from a
   radii-polynomial certificate, which gives uniqueness in a ball).
2. Then every witness is the same state, and `compose_of_unique` combines the clauses.
3. Without uniqueness, the separate existence statements do not compose.

## Example 3: Why a common witness is required

**Problem shape:** Is `(∃ e, P e) ∧ (∃ e, Q e)` enough for `∃ e, P e ∧ Q e`?

**Use of technique:**
1. Witness: on `Bool`, `P b := b = true`, `Q b := b = false`.
2. Each has a witness, no common one: `incompatible_witnesses`
   (`PlasmaLean/Bridge/Contracts.lean`).
3. Lesson for design claims: an equilibrium proved stable and a different equilibrium proved
   confined say nothing about one machine.
