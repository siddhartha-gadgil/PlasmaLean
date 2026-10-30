# Existence of the orbits that the confinement theorems quantify over

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-26` |
| Title | Orbit existence: global Newton–Lorentz orbits of the reactor Solov'ev field; local off-axis Boozer guiding-centre orbits |
| Kind | proof / formalization |
| Addresses | audit findings MA-M2 (full orbits) and MA-M1 (near-QA Boozer orbits) of `notes/audit/2026-10-30-model-audit.md`; goals `G-1`, `G-6` |
| Depends on | `N-8` (`SolovevAlpha.reactor_alpha_confined`), `N-4` (`BoozerGCOrbitOn`, `boozerGC_trapped_until`); Lean: `ODEGlobal.uniform_local_existence`, `extend_right`, `extend_left`, `exists_global` (`Theory/Fields/FieldLineExistence`), `canonicalMomentum_conserved`/`orbit_trapped` (`Theory/Kinetic/CanonicalMomentum`), `Solovev.field_coords`, `region_bounds`, `region_norm`, `field_axisymmetric`, `NearAxisQA.field`, `reactorQA_B_bounds`, `NearAxisQAAveraged.alpha_trapped_reactorQA_averaged_of_le`; Mathlib Picard–Lindelöf (`IsPicardLindelof`) |
| Dependency requirement | compiled statements only (all are in the default build) |
| Produces | 5 new default-build modules (below); 14 new axiom-checked entry points in `scripts/check_axioms.lean` |
| Difficulty | moderate (A); routine for local existence, research for the full horizon (B) |
| Status | A: verified. B: local existence verified; full-horizon existence open (see barriers) |
| Lean evidence | `PlasmaLean/Theory/Fields/ODEContinuation.lean`, `PlasmaLean/Theory/Kinetic/LorentzExistence.lean`, `PlasmaLean/Design/SolovevAlphaExistence.lean`, `PlasmaLean/Theory/Kinetic/BoozerGCExistence.lean`, `PlasmaLean/Design/NearAxisQAExistence.lean` (all default build) |
| Audit evidence | not audited (addresses MA-M1, MA-M2 of the audit of `cda8bd0`) |
| Last updated | 30 October 2026: created; A closed, B local |

## Purpose and scope

The full-orbit and guiding-centre confinement theorems have the form "every orbit with property X
stays confined". Such a statement has content only if orbits with property X exist. The audit
found two gaps:

- **MA-M2.** `SolovevAlpha.reactor_alpha_confined` and the alpha conjunct of `solovev_one_plasma_*`
  quantify over all `LorentzOrbit`s of `reactorField` with energy ≤ 3.5 MeV born at
  `ψ̃ ≤ ψ̃_e/4` (flux label `≤ 3/11`). The only witness was an alpha at rest on the axis.
- **MA-M1.** The near-QA results quantify over `BoozerGCOrbitOn reactorQA … T`, which requires
  `ψ > 0` on `[0, T]`. No such orbit of `reactorQA` was constructed.

Models: the non-relativistic Newton–Lorentz equation `m v' = q v × B(x)` in a static field (SI
units), and the vacuum Boozer guiding-centre model of `Theory/Kinetic/BoozerGuidingCentre` (a
supplied reduced model, not derived from the Lorentz force), on the state `(ψ, θ, φ, ρ)`.

## Dependencies

All dependencies are compiled default-build declarations (listed in the metadata). The Boozer
guiding-centre equations and the near-axis field strength remain supplied *models* (N-4); this
note does not change their status.

## Sources and prior work

Standard ODE theory: Picard–Lindelöf local existence and continuation of solutions as long as they
stay in a compact subset of the domain where the vector field is locally Lipschitz (for example
Hartman, *Ordinary Differential Equations*, ch. II, Theorems 1.1 and 3.1). Mathlib supplies the
local theorem (`IsPicardLindelof`); the continuation argument is new in the repository,
generalizing `ODEGlobal.exists_global` (field lines, `Theory/Fields/FieldLineExistence`).

## Theory development

**Generic continuation (`ODEContinuation`).** `exists_global` needs one compact set that traps all
local solutions. A charged particle has only a time-dependent bound (position within `|v₀| T` of
the start after time `T`). `APrioriBounded f U x₀` asks, for every horizon `T`, for a compact
`K_T ⊆ U` that contains every solution on `[-c, c]` (`c ≤ T`) from `x₀`. Under it,
`extend_to_horizon` extends a solution on `[-S, S]` to `[-T, T]` by steps `ε_T/2` (the uniform
Picard–Lindelöf time of `K_T`). Both endpoints are extended at once, so only the bound on the old
interval is used. The solutions on `[-n, n]` are then glued, which gives `exists_global_of_apriori`.

**A: Lorentz orbits.** Phase-space field `lorentzField m q B (x, v) = (v, (q/m) v × B(x))`. It is
`C¹` on `V × Space` when `B` is `C¹` on `V`. Speed and, for axisymmetric fields, canonical
momentum are conserved on closed intervals (`speed_eq_Icc`, `canonicalMomentum_eq_Icc`), so
the trapping argument has an interval version (`orbit_trapped_Icc`, using the intermediate value
theorem on `[a, b]`).

- If `B` is `C¹` on all of space, `K_T = closedBall x₀ (|v₀|T) × closedBall 0 |v₀|`, which gives
  `lorentzOrbit_exists` for every initial condition.
- The Solov'ev field is singular on the vertical axis (`∇φ = (-y, x, 0)/R²`), so it is `C¹` only on
  `{R² ≠ 0}` (`field_contDiffOn`). Under the rigidity and birth hypotheses of `orbit_confined`,
  the interval trapping keeps every interval solution in the compact set
  `{ψ̃ ≤ 11L⁴/192} × closedBall 0 |v₀|`, which lies in `R² ≥ L²/2` (`solovev_apriori`). The
  confinement proof thus also supplies the a priori bound for existence.

**B: Boozer guiding-centre orbits.** `boozerVF F m q μ` is the right-hand side of `BoozerGCOrbit`
on `ℝ⁴`. For the near-axis models (`NearAxisQA.field`) its coefficients contain `r = √(2ψ/B₀)` and
`1/r`; they are smooth on `{ψ > 0}`, and `fun_prop` proves `C¹`. Picard–Lindelöf on `{s₀}`, plus
continuity of `ψ` at `0`, gives an orbit on `[0, T]` with `T = min(ε, δ)/2 > 0`.

## Claims and evidence

| Claim | Status | Declaration (all default build, standard axioms) |
| --- | --- | --- |
| Continuation: a `C¹` field on open `U ∋ x₀` with a priori bounds on every horizon has a global solution from `x₀` | compiled Lean theorem | `PlasmaLean.Fields.ODEGlobal.exists_global_of_apriori`; helpers `extend_to_horizon`, `apriori_of_locallyInvariant`; sanity `exists_global_of_apriori_zero` |
| A global solution of the phase-space system is a `LorentzOrbit` (`m ≠ 0`) | compiled | `PlasmaLean.Kinetic.lorentzOrbit_of_flow` |
| Speed and canonical momentum conserved on closed intervals; interval trapping | compiled | `speed_eq_Icc`, `canonicalMomentum_eq_Icc`, `trapped_of_gap_Icc`, `orbit_trapped_Icc` |
| **`B` `C¹` on all of space, `m ≠ 0` ⇒ for every `x₀, v₀` a Lorentz orbit for all `t ∈ ℝ` with `x 0 = x₀`, `v 0 = v₀`** | compiled | `PlasmaLean.Kinetic.lorentzOrbit_exists`; sanity `lorentzOrbit_exists_uniform` |
| `B` `C¹` on open `V ∋ x₀` plus a priori trapping in compact subsets of `V × Space` ⇒ global orbit | compiled | `PlasmaLean.Kinetic.lorentzOrbit_exists_of_apriori` |
| Solov'ev field `C¹` off the axis; orbits under the `orbit_confined` hypotheses exist for all time | compiled | `Design.SolovevAlpha.field_contDiffOn`, `solovev_apriori`, `solovev_orbit_exists` |
| **Every alpha (m, e in the stated ranges) born at `ψ̃ ≤ ψ̃_e/4` with energy ≤ 3.5 MeV (any pitch) has a `reactorField` orbit for all `t ∈ ℝ`** | compiled | `Design.SolovevAlpha.reactor_alpha_orbit_exists`; label form `reactor_alpha_orbit_exists_label` (`label x₀ ≤ 3/11`, the hypothesis of `solovev_one_plasma_*`) |
| **Such orbits exist and every such orbit stays at `ψ̃ ≤ (11/12)ψ̃_e`, `R² ≥ 50` for all `t`** | compiled | `Design.SolovevAlpha.reactor_alpha_born_confined` |
| **Explicit witness at exactly 3.5 MeV, born on the axis, confined forever** | compiled | `Design.SolovevAlpha.reactor_alpha_confined_nonvacuous_35MeV` (with `alpha35Velocity_energy`); old rest case recovered by `reactor_alpha_orbit_exists_rest` |
| Phase-space solutions that stay in `ψ > 0` are `BoozerGCOrbitOn`/`BoozerGCOrbit` trajectories | compiled | `Kinetic.Boozer.boozerGCOrbitOn_of_flow`, `boozerGCOrbit_of_flow` |
| **Boozer field `C¹` on `{ψ > 0}` ⇒ from every `s₀` with `ψ₀ > 0` an orbit on `[0, T]` for some `T > 0`** | compiled | `Kinetic.Boozer.boozerGCOrbitOn_exists_local` |
| Existence on a prescribed `[0, T]` from a two-sided a priori bound in a compact subset of `{ψ > 0}`; all-time existence from bounds on every horizon | compiled (conditional on the bound) | `boozerGCOrbitOn_exists_of_apriori`, `boozerGCOrbit_exists_of_apriori` |
| Every near-axis QA model, in particular `reactorQA`, has a `C¹` Boozer field on `{ψ > 0}` and local off-axis orbits | compiled | `Design.NearAxisQAExistence.field_boozerVF_contDiffOn`, `nearAxis_orbit_exists_local`, `reactorQA_orbit_exists_local` |
| **The hypothesis bundle of `alpha_trapped_reactorQA_averaged_of_le` (E = E_α, pitch, `ψ₀ = psiStart`) is satisfied by a constructed orbit on `[0, T]`, some `0 < T ≤ 0.19 s`** | compiled | `Design.NearAxisQAExistence.alpha_trapped_reactorQA_averaged_nonvacuous` (μ = 0, `v_∥² = 2E_α/m`) |

Uniqueness of the orbits is not stated (it follows from Grönwall, as in
`ODEGlobal.unique_global`, if needed).

## Difficulty, barriers and readiness

- **A is closed** for the advertised hypothesis class: `reactor_alpha_confined` and the alpha
  conjunct of `solovev_one_plasma_*` now apply to genuine 3.5 MeV orbits, through every admissible
  initial condition. MA-M2 can be marked resolved after coordinator verification.
- **B is local only.** `T` is not quantified, so the near-QA theorems are shown non-vacuous only on
  some short horizon `(0, T]`, not on `[0, 0.19 s]` (`alpha_trapped_reactorQA_averaged`) or
  `[0, 8 × 10⁻⁴ s]` (`alpha_trapped_reactorQA`). The missing input is an a priori bound for the
  hypothesis class: `ψ ≥ ψ_min > 0` and `|ρ| ≤ ρ_max` up to the horizon. With it,
  `boozerGCOrbitOn_exists_of_apriori` applies; the angles grow at most linearly, so a compact
  set on a finite horizon is available. Such a bound **cannot hold for the whole class**: a
  passing alpha born at `ψ₀ ≤ psiStart ≈ 0.51 T m²` can reach the axis. The helical-momentum
  band gives `|ψ − ψ₀| ≲ |G| Δρ/ι ≈ 58.1 · 0.0295/0.422 ≈ 4 T m²` (rough, not in Lean), which
  is far larger than `psiStart`.
- **Smallest next steps for B.**
  1. A quantitative Picard–Lindelöf time for `reactorQA`: bound `|boozerVF|` on a box around
     `s₀`. It would be short (the drift `ψ̇` is small, but the box in `ψ` must stay away from 0),
     and it gives an explicit `T`.
  2. A sub-class with a two-sided band: a lower-bound analogue of
     `boozerGC_trapped_until_averaged` for orbits born at `ψ₀ ≥ ψ_min + (band width)`, which
     yields existence on `[0, 0.19 s]` through `boozerGCOrbitOn_exists_of_apriori`. This needs
     births further out than `psiStart`, i.e. a restated theorem.
  3. Alternatively, Cartesian near-axis coordinates `(√ψ cos θ, √ψ sin θ)`, in which the model
     may extend through the axis. This would remove `ψ > 0` from the orbit definition (the fix
     suggested by MA-M1); it changes the model statement and is a user decision.

## Outputs and next dependencies

- Audit: MA-M2 resolved (pending coordinator check). MA-M1: the existence part is resolved
  locally, and full-horizon existence is open as stated above. The restatement "every supplied
  passing orbit that stays off the axis on [0, 0.19 s]" is still the correct reading of the
  near-QA claims.
- G-1: the full-orbit Solov'ev alpha confinement is now unconditional on orbit existence. G-6:
  the near-QA theorems are non-vacuous only on a short horizon.
- Registry: the coordinator should register `N-26` in RG.3 (edges `N-8 → N-26`, `N-4 → N-26`),
  index this note in `notes/theory/README.md`, and add a §13 entry.
