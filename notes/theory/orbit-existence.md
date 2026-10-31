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
| Produces | 7 new default-build modules (below); 26 new axiom-checked entry points in `scripts/check_axioms.lean` |
| Difficulty | moderate (A); routine for local existence, research for the full horizon (B) |
| Status | A: verified. B: prescribed-horizon existence verified for an outer birth band (route ii, up to 0.05 s) and, for the original class, on an explicit μs horizon (route i); full-horizon existence for the original class open (obstruction: the chart, see barriers) |
| Lean evidence | `PlasmaLean/Theory/Fields/ODEContinuation.lean`, `PlasmaLean/Theory/Kinetic/LorentzExistence.lean`, `PlasmaLean/Design/SolovevAlphaExistence.lean`, `PlasmaLean/Theory/Kinetic/BoozerGCExistence.lean`, `PlasmaLean/Design/NearAxisQAExistence.lean`, `PlasmaLean/Theory/Kinetic/BoozerGCForward.lean`, `PlasmaLean/Design/NearAxisQAExistenceFull.lean` (all default build) |
| Audit evidence | not audited (addresses MA-M1, MA-M2 of the audit of `cda8bd0`) |
| Last updated | 30 October 2026: created; A closed, B local; later the same day B on prescribed horizons (routes i and ii) |

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

**B on prescribed horizons (`BoozerGCForward`, `NearAxisQAExistenceFull`).** The trapping
estimates are forward estimates for genuine orbits (which stay off the axis by definition), so
three pieces are needed.

1. *Forward continuation.* `exists_forward_of_apriori` extends a solution to the right only
   (steps `ε/2` with `extend_right`), so only bounds for solutions on `[0, c]` are needed (the
   symmetric `[-c, c]` bounds of `extend_to_horizon` would need backward estimates).
   `boozerGCOrbitOn_exists_of_region`: if forward solutions stay in a closed `R ⊆ {ψ > 0}` with
   `‖boozerVF‖ ≤ M` on `R`, they stay in `R ∩ closedBall s₀ (MT)`, which is compact, so the
   angles need not be bounded in `R`. For `reactorQA` the field is bounded on every band
   `a ≤ ψ ≤ b`, `|ρ| ≤ ρ_m` (`a > 0`) by `2π`-periodicity in both angles
   (`reactorQA_VF_bounded`); `|ρ| ≤ 0.055 m` follows from energy conservation and `B ≥ 4.93`.
2. *Bootstrap.* `boozer_bootstrap`: if every orbit on `[0, t]` that has stayed in
   `|ψ − ψ₀| ≤ D` (`D < ψ₀`) satisfies `|ψ t − ψ₀| ≤ D' < D`, then every solution of the
   first-order system stays in `|ψ − ψ₀| ≤ D'` (continuous induction, `trapped_until`).
3. *Two-sided estimates for orbits.*
   - Route (ii), `band_estimate`: with `P = q(Gρ − ι₀ψ)`,
     `ι₀ |ψ t − ψ 0| ≤ |G| |ρ t − ρ 0| + |P t − P 0|/q`. The orbit width `Δρ ≈ 1.88 cm`
     (`rho_dev`) and the averaged drift `|ΔP| ≤ 2 (1935 + 218 + 93) q/Ω₀ + 11 q t`
     (`averaged_drift`, extracted from the proof of `alpha_trapped_reactorQA_averaged_of_le`)
     give `|ψ t − ψ 0| ≤ D(t) = (|G| Δρ + 2∑Aⱼ/Ω₀ + 11 t)/ι₀ ≈ 2.593 + 26.07 t` T m², valid while
     `ψ ≤ ψ_a`, for passing alphas (`v_∥² ≥ 0.81 v²`, energy `E_α`, `μ ≥ 0`).
   - Route (i), `radius_lipschitz`: `ψ̇ ∝ ∂_θB = O(r)`, so `ṙ = ψ̇/(B₀ r)` is bounded:
     `|ṙ| ≤ (2E_α/(q B_min)) (|η| + 2|B₂c| a/B₀) ≤ 57000 m/s` for every pitch.

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
| Forward continuation: `C¹` field, forward solutions from `x₀` on `[0, c]` (`c ≤ T`) in a compact `K ⊆ U` ⇒ solution on `[0, T]` | compiled | `Fields.ODEGlobal.exists_forward_of_apriori`; sanity `exists_forward_of_apriori_zero` |
| Boozer: forward bound in a compact, or in a closed region with bounded vector field ⇒ orbit on `[0, T]` staying there; bootstrap from orbit estimates to solution bounds | compiled | `Kinetic.Boozer.boozerGCOrbitOn_exists_of_forward_apriori`, `boozerGCOrbitOn_exists_of_region`, `boozer_bootstrap` |
| `reactorQA` vector field `2π`-periodic in the angles, bounded on bands; `|ρ| ≤ 0.055 m` at energy `E_α`; a forward band bound gives an orbit on `[0, T]` | compiled | `Design.NearAxisQAExistenceFull.boozerVF_periodic`, `reactorQA_VF_bounded`, `abs_rho_le`, `orbit_exists_of_forward_band` |
| Two-sided band estimate for passing alphas: `|ψ t − ψ 0| ≤ D(t)` while `ψ ≤ ψ_a` | compiled | `averaged_drift`, `band_estimate`, `Dpsi` (`Dpsi_mono`, `Dpsi_short`: `D(8e-4) ≤ 2.65`, `Dpsi_005`: `D(0.05) ≤ 3.9`) |
| **Route (ii): passing 3.5 MeV alphas born with `D(T) < ψ₀`, `ψ₀ + D(T) < ψ_a` have an orbit on all of `[0, T]`, staying in `|ψ − ψ₀| ≤ D(T)`** | compiled | `alpha_band_orbit_exists`, `alpha_band_orbit_exists_of_le` |
| **`T = 8 × 10⁻⁴ s` (horizon of `alpha_trapped_reactorQA`): births `2.75 ≤ ψ₀ ≤ 5.5` T m² (`r₀ ≈ 0.58–0.82 a`), any angles, stay in `0.1 ≤ ψ ≤ 8.2`** | compiled | `alpha_band_orbit_exists_short` |
| **`T = 0.05 s`: births `4 ≤ ψ₀ ≤ 4.3` T m² (`r₀ ≈ 0.70–0.72 a`) stay in `0.1 ≤ ψ ≤ 8.2`; constructed witness at `ψ₀ = 4`, `E = E_α`, `μ = 0`** | compiled | `alpha_band_orbit_exists_005`, `alpha_band_nonvacuous_005` |
| **Route (i): every birth of the original class (`0 < ψ₀ ≤ ψ_start`, `E_α`, `μ ≥ 0`, any pitch) has an orbit on `[0, r₀/285000 s]` (`1.49 μs` at `r₀ = a/4`), staying in `|ψ − ψ₀| ≤ 0.44 ψ₀`; with passing pitch the averaged theorem then applies to it** | compiled | `radius_lipschitz`, `alpha_orbit_exists_explicit`, `alpha_trapped_reactorQA_averaged_explicit` |
| Limits of the band method: `D(T) > ψ_start` for all `T ≥ 0` (never reaches the original class); `2 D(T) > ψ_a` for `T ≥ 0.06 s`, in particular at `T_av = 0.19 s` (band empty) | compiled | `Dpsi_gt_psiStart`, `band_empty_of_ge`, `band_empty_Tav` |

Uniqueness of the orbits is not stated (it follows from Grönwall, as in
`ODEGlobal.unique_global`, if needed).

## Difficulty, barriers and readiness

- **A is closed** for the advertised hypothesis class: `reactor_alpha_confined` and the alpha
  conjunct of `solovev_one_plasma_*` now apply to genuine 3.5 MeV orbits, through every admissible
  initial condition. MA-M2 can be marked resolved after coordinator verification.
- **B: what is covered.** (1) *Outer band, prescribed horizon (route ii).* Passing 3.5 MeV
  alphas born at `2.75 ≤ ψ₀ ≤ 5.5` T m² exist on the full worst-case horizon `[0, 8 × 10⁻⁴ s]`,
  and those born at `4 ≤ ψ₀ ≤ 4.3` T m² on `[0, 0.05 s]`, staying in `0.1 ≤ ψ ≤ 8.2`; in general
  any `T < 0.058 s` with `D(T) < ψ₀ < ψ_a − D(T)`. These classes are **disjoint from** the class
  `ψ₀ ≤ ψ_start ≈ 0.51 T m²` of `alpha_trapped_reactorQA*` (births further out); for them the
  band theorem itself is the confinement statement. (2) *Original class, explicit horizon
  (route i).* Every birth with `0 < ψ₀ ≤ ψ_start` (any pitch) exists on `[0, r₀/285000 s]`,
  at most 1.49 μs (at ψ₀ = ψ_start) and proportional to `r₀ = √(2ψ₀/B₀)`, so it shrinks to 0
  at the axis (audit AR-M5).
- **B: what is open, and why.** Existence on `[0, 0.19 s]` or `[0, 8 × 10⁻⁴ s]` for births with
  `ψ₀ ≤ ψ_start`. Obstructions (the last two are compiled sanity theorems):
  - the band half-width contains the orbit-width term `|G| Δρ/ι₀ ≈ 2.59 T m² > ψ_start`
    (`Dpsi_gt_psiStart`), and even the physical orbit width (`Δρ ≈ ρ_∥ ΔB/B ≈ 3 mm`, giving
    `|G| Δρ/ι₀ ≈ 0.4 T m²`, a rough estimate, not in Lean) is comparable to `ψ_start`: passing
    alphas born that close to the axis can reach it, so no lower bound `ψ ≥ ψ_min > 0` holds for
    the class. The obstruction is the chart `ψ > 0` itself;
  - for the outer band, the secular averaged rate `11 q` T m²/s gives `D(T) ≥ 26 T`, so no band
    fits inside `(0, ψ_a)` for `T ≥ 0.06 s` (`band_empty_of_ge`, `band_empty_Tav`); even with
    `Δρ = 0` the limit would be `T ≈ 0.16 s`;
  - the radial-speed route gives only microseconds (`57 km/s` against `r₀ ≤ 0.43 m`).
- **Smallest next steps for B.**
  1. Route (iii): Cartesian near-axis coordinates `(√ψ cos θ, √ψ sin θ)`; `NearAxisQAAveraged`
     already shows that the orbit ODE is polynomial in `x = r cos θ, y = r sin θ` (`hasDerivAt_orbX`,
     the `1/r` singularities cancel). An orbit notion in these variables, without `ψ > 0`, would
     make existence for the original class a matter of a priori bounds on `x² + y² ≤ a²`, which
     the upper trapping bound already gives (a model-statement change; user decision).
  2. A longer outer-band horizon needs a smaller secular amplitude bound on an annulus (the
     `amp 3` cover is a sup over the whole disc) and a sharper orbit width (local `B` range).

## Outputs and next dependencies

- Audit: MA-M2 resolved (pending coordinator check). MA-M1: existence on prescribed horizons is
  proved for an outer birth band (up to 0.05 s) and, for the original class, on an explicit
  microsecond horizon; full-horizon existence for the original class is open, with the chart
  `ψ > 0` identified as the obstruction. The restatement "every supplied
  passing orbit that stays off the axis on [0, 0.19 s]" is still the correct reading of the
  near-QA claims.
- G-1: the full-orbit Solov'ev alpha confinement is now unconditional on orbit existence. G-6:
  the near-QA theorems for births at `r ≤ a/4` are non-vacuous on an explicit microsecond
  horizon; for births at `r ≈ 0.6–0.8 a` existence and two-sided confinement hold on the full
  `8 × 10⁻⁴ s` horizon, and at `r ≈ 0.7 a` on `0.05 s`.
- Registry: the coordinator should register `N-26` in RG.3 (edges `N-8 → N-26`, `N-4 → N-26`),
  index this note in `notes/theory/README.md`, and add a §13 entry.
