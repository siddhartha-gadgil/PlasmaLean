# Refresh audit of all changes since 31 October 2026, 23 November 2026

Skill: `plasmalean-audit-domain`, proof policy `plasmalean-lean-proofs`.

| Item | Value |
| --- | --- |
| Previous audited commit | `921a8c3` (refresh audit, 31 October 2026); partial audit of three form modules at `1e5d4f3` (16 November 2026, findings AD-*) |
| Audited commit | `6ceca0e` (branch `main`, 23 November 2026); corrections are in the commit that adds this record |
| Toolchain | Lean `v4.36.0`; TauCeti `v4.36.0`; Mathlib transitive at `fc4f59e577` |
| Scope | **complete refresh audit**: every Lean file changed since `921a8c3` (304 files, 259 added): 42 modules added on 23 November (form topology, periods, contact geometry, the anti-self-dual lift, charged-particle Noether and Hamiltonian theory), the contract and theory changes of 1–16 November, the Dommaschk certification chain (192 files) and the other design changes, the proof repairs for Lean v4.35.0 and v4.36.0, the task-server tooling merged from another project; and the note-to-code links of N-41–N-48, the plan, the README and the Rosetta-stone page |
| Method | mechanical checks by the lead; six independent read-only sub-audits, each given files and a red-team checklist, not the author's conclusions; fixes by three further agents on disjoint files; every fix rebuilt and axiom-checked by the lead. Findings carry the prefix `AV-` |
| Result | **no critical finding; no false or vacuous exported theorem found.** 1 high (a mislabelled sign in docstrings and notes), 12 medium, about 40 low. All high and medium findings are resolved or recorded as open below |

## Commands run

- Scan of the 304 changed files for `sorry`, `admit`, `axiom`, `native_decide`, `decide` variants,
  `unsafe`, `implemented_by`, `@[extern]`, `opaque`, `set_option`, instances and attributes.
  - No real `sorry`, `admit`, `axiom` or `native_decide`. The hits are strings and docstrings in
    the task-server tooling (`Elaborate.lean` writes `sorry` templates at run time).
  - `decide`: only as a Boolean function inside checker statements (pre-existing), three legacy
    `decide +kernel` fixtures in `Certificates/Kronecker2D`, two `decide_cbv` in
    `Theory/Fields/CylAlgebra` (pre-existing).
  - `unsafe`: only in the tooling (`Elaborate.lean`, `ResponseExt.lean`, the two `main`s), inside
    `IO`/`TermElabM` code that cannot prove a proposition.
  - `set_option`: linter, `maxRecDepth`, `maxHeartbeats` only.
- `lake build` of **all** 1,728 modules (default and on-demand) and both executables, before the
  fixes: up to date, 13,001 jobs, no warning. After the fixes: see "Resolution".
- `lake env lean scripts/check_axioms.lean`: passed, "Axiom audit passed for 52017 PlasmaLean
  declarations" (before the fixes). The check is enforced: a `run_cmd` collects the axioms of
  every project declaration and throws on anything other than `propext`, `Classical.choice`,
  `Quot.sound`. One sub-audit confirmed that proof bodies of `module` files are visible to it
  and that no project theorem is imported as an axiom.
- `lake env lean scripts/check_axioms_heavy.lean`: passed (115 printed entry points).
- Sub-audit scratch checks (`lake env lean` on scratch files outside the repository): axioms of
  16 theorems; a compiled check that the inverse momentum map pulls the canonical form back to
  `Ω − q π^*ω_B` (AV-H1); signatures of the measure-theory lemmas behind the energy identity.
  The design-layer sub-audit ran no scratch check (its one attempt was refused by the
  permission system); it is an audit by reading.

## Findings

### AV-H1 (high, documentation; resolved): sign and direction of "the magnetic symplectic form"

`Theory/Kinetic/MagneticSymplectic`. The proved identity is correct: for the map `Ψ` from
canonical to kinetic momentum, `Ψ^*Ω = Ω + q π^*ω_B`. The docstrings, note N-48 and the
Rosetta-stone page called `Ω + q π^*ω_B` "the magnetic form" and reversed source and target. In
TauCeti's convention (`ι_X Ω = dH`) the magnetic form on kinetic phase space, for which the free
Hamiltonian generates `m v' = q v × B`, is `Ω − q π^*ω_B`. `lorentzOrbit_hamilton` was not
affected.

Resolution: docstrings, N-48 and the Rosetta page corrected. New theorems
`kineticMomentumMap_neg_comp`, `canonicalForm_fderiv_kineticMomentumMap_neg_flux`,
`magneticForm`, `lorentzForceField`, **`magneticForm_lorentzForceField`** (with the form
`Ω − q π^*ω_B` the free Hamiltonian generates the Lorentz force; this pins the sign),
`magneticForm_fderiv_kineticMomentumMap`, `lorentzOrbit_kineticCurve`. Regressions in
`Sanity/MagneticSymplectic`: `uniform_magneticForm_lorentzForceField` (accepted),
`uniform_plus_sign_fails` (rejected: the plus sign fails by `2qB₀/m`), `helix_kineticCurve`.

### AV-M1 (medium; resolved): the clause-C1 corollaries are Stokes on a planar disc

`Theory/Fields/FormConvexRegion`: `CurrentFreeTransform.imax_zero_of_meridianHalfSpace` and
relatives. The statements are correct, but they were described (docstrings, N-48, plan, Rosetta
page, and the lead's reports) as "the net-current bound of C1 is automatic for vacuum fields".
What they say: a field with no current through the planar poloidal cross-section has zero
circulation around it. For such fields the current clause carries no information; the torus and
transform clauses are assumed, not derived. The half-space hypothesis excludes every
coil-generated field.

Resolution: docstrings and documents reworded. New general form
`CurrentFreeTransform.imax_zero_of_convex`, `CurrentFreeTransform.current_eq_zero_of_convex`
(any convex region containing the loop); the half-space version is now derived from it. Fixture
on a bounded ball: `rationalStellarator_ball_fixture`.

### AV-M2 (medium; resolved): `rationalStellarator_fixture` is staged

Its source instance already has `I_max = 0`; the fixture forgets this and recovers it. It is a
satisfiability and consistency check, not evidence that the corollary improves an allowance. No
instance exists whose current bound was proved by an estimate. Docstrings corrected.

### AV-M3 (medium; resolved): `noetherMomentum_add_gradient` cited as gauge invariance

It is a hypothesis-free algebraic identity. Resolution: docstrings and documents corrected; new
composed theorem `noetherMomentum_gauge_invariant` (for `B = ∇ × A`, equivariance up to `∇χ`,
`H = ∇Λ`, and any admissible gauge term `χ'` of `A + H`: same field, conserved momentum, equal to
the old one minus the constant `q(χ'(0) − χ(0))`) and `noetherMomentum_gauge_eq_iff`.

### AV-M4 (medium; partly resolved): global-domain restriction of the kinetic theorems

Every Noether, Hamilton and uniqueness theorem assumes a vector potential differentiable on all of
space with `B = ∇ × A` everywhere. This excludes the straight-wire and toroidal vacuum fields and
any field defined on a toroidal region only. A helical (screw) generator is covered by neither
the linear nor the translation theorem. Uniqueness of orbits went through potentials.

Resolution: the limit is stated in the module docstrings. New
`lorentzOrbit_unique_of_contDiff`, `lorentzOrbitOn_unique_of_contDiff` (uniqueness for `C¹` `E`
and `B`, no potentials) and `lorentzOrbit_existsUnique_of_contDiff` (existence and uniqueness for
a `C¹` field `B`, `E = 0`). New fixture with a nonlinear potential, `shear_momentum_conserved`
(`A = (x²/2)e_y`). **Open:** versions on an open set containing the orbit; the helical generator.

### AV-M5 (medium; resolved): the energy identity had no check with period `ℓ ≠ 1`

`integral_liftInner_hymLiftCircle` is true as stated (the sub-audit looked for a counterexample
and found none). Resolution: docstring states the conventions for non-measurable `Ω` and
non-integrable `|B|²`; fixtures `energy_ball_three`, `energy_ball_one_eq_third`, `energy_empty`,
`energy_junk`, `energy_univ_junk`.

### AV-M6 (medium; resolved): `extDeriv_hymLift_eq_zero_iff` is `True ↔ True` where `ω` is not differentiable

Disclosed in the docstring; no fixture. Resolution: `differentiableAt_hymLift_iff` exported;
regression `absLift_junk_closed` (`|x|·dy∧dz` has a "closed" lift at `0` by junk values); concrete
discontinuous fixture `stepForm_circle_not_continuous`. The `C²` iffs are not affected.

### AV-M7 (medium; **open**): field-level clause C2 has only a vacuous instance

`Theory/Contract/BoozerModel`: the only proved `OmnigeneityContract` is for the purely toroidal
field with `ι = 0`, where there is no trapped bounce, so it holds vacuously. The bridge theorems
`omnigeneityContract_of_qa`, `omnigeneityContract_of_defect_le` are applied to no field. That
field fails C1, so **no field is shown to satisfy C1 and C2 together**, and C2 for a field has no
non-vacuous witness.

Partial resolution: stated in the docstrings; regression `exists_trappedBounce_driftMirror`
(a trapped bounce exists at model level, for a model without a chart). Open: a chart-backed field
with a constructed trapped bounce.

### AV-M8 (medium; documented, definition unchanged; **open**): `BoozerChart` does not pin the poloidal angle

Verified in Lean: for any chart and any integer `k`, relabelling `θ ↦ θ − kφ` gives a chart of the
same field with `ι + k` (`relabelChart`, `BoozerModelOf.relabel`); the toroidal field has a model
with `ι = 1` (`toroidal_boozerModelOf_iota_one`). So the `ι` of C2 is defined modulo integers, the
hypotheses `ιmin ≤ F.ι` of the bridge theorems are chart-dependent, and nothing ties it to the `ι`
of C1. Open: add a poloidal-angle clause to `BoozerChart`, or prove the link to `IotaOnTorus`.

### AV-M9 (medium, documentation; resolved, one part open): clause names read stronger than the predicates

C1 is satisfied by a single invariant torus (`S` nonempty); the torus predicates do not assert
embeddedness (AF-1); "current-free" is a bound on one circulation at one toroidal angle per
surface. Resolution: "Scope and limits" paragraphs in `StellaratorContract`. Uniqueness of `ι`
for a fixed parametrisation does not follow from `IotaOnTorus.tendsto`; it is proved under
differentiability of the surface at one point with nonzero `θ`-derivative
(`fieldTorus_iota_unique`, `iotaOnTorus_iota_unique`). Open: the unconditional statement.
Later the same day (not audited): for a `C²` surface and a field `C¹` and curl-free on an open
set containing it, the circulation does not depend on the toroidal angle
(`FieldTorus.poloidalCirculation_eq_of_curl_eq_zero`, `Theory/Fields/FormFluxSurfacePeriods`).
An embeddedness predicate now exists (`EmbeddedTorus`, `Theory/Fields/FormFluxSurfaceEmbedded`),
with a `FieldTorus` that is not embedded (`dbl_fieldTorus`, `dbl_not_embeddedTorus`); it is not
a clause of `CurrentFreeTransform`. Later the same day the clause was added as the
strengthened predicate `Contract.EmbeddedCurrentFreeTransform`
(`Theory/Contract/EmbeddedSurfaces`). The subsequent Q-36 proofs establish that clause
on the rational stellarator torus A and on Dommaschk tori C and A, including the nested Q-16
witnesses. AF-1 still describes the bare predicates. Even a smooth winding-one
`IotaOnTorus` at zero transform can have a stationary tangent. These developments postdate
the audited revision. [N-52](../theory/irrational-return-embedding.md)

AV-M4: orbit existence and uniqueness for fields
on an open set, without potentials, are in `Theory/Kinetic/LorentzOrbitOpen` (not audited).

### AV-M10 (medium; resolved): `dommaschk_Q16_vacuum` hides the regularity behind its defect bounds

New theorem `dommaschk_Q16_chart`: the headline with `BoozerChartHyp` for both tori and their
closeness (`10⁻¹²`) to the data tori.

### AV-M11 (medium, documentation; resolved): README overclaims

"Landreman family 2 fails C1" is conditional on the surface's loop being the family-2 loop in its
given parametrisation; "two field periods" of the Dommaschk candidate is not a theorem about the
field. Reworded. Open (low): reparametrisation invariance of `poloidalCirculation`.

### AV-M12 (medium, documentation; resolved): note N-48 contradicted itself

Written in eight stages on one day; early "Not done" items were done later. A "Current state"
section now precedes the chronological sections, and the stale table entries are corrected.

### Low findings

| ID | Finding | Status |
| --- | --- | --- |
| AV-L1 | `TorusQADefectLe` has no regularity clause (holds for a constant map and for `B = 0`) | docstring warning; regressions `torusQADefectLe_const`, `torusQADefectLe_zero_field` |
| AV-L2 | the tooling's `assess` gate rejected only `sorryAx` | fixed: requires the three standard axioms |
| AV-L3 | task-server tooling is part of the default library import (two new tokens, a `run_command_seq` command, generic names) | **open** (no effect on term elaboration) |
| AV-L4 | header of `check_axioms_heavy.lean` overstated coverage (`PlasmaLeanMeta` is not covered; on-demand modules outside the import closure are not; `debug.skipKernelTC` is not detected) | header corrected |
| AV-L5 | new global `@[simp]` lemmas in `QSLinearSystem`, `SectionStokes`, `DommaschkKamPoly` and others | recorded; all are true rewrite rules |
| AV-L6 | layering: `Theory/Contract/BoozerModel` imports a design module; `chartJac` defined twice; `CurrentFreeTransform.circulation_eq_zero` lives in a sanity namespace | **open** |
| AV-L7 | `WeakQS.lieBracket_eq_zero` needs more than `WeakQS`; module docstring did not say so | docstring corrected |
| AV-L8 | three exported `SimplyConnectedSpace` instances | named and documented; kept |
| AV-L9 | `VacuumField.exists_vectorPotential` dropped the regularity of `A` | new `exists_vectorPotential_contDiffOn` |
| AV-L10 | stale or inexact docstrings in 9 modules; a docstring citing a non-existent name | corrected |
| AV-L11 | sanity theorems that are instantiations or follow from one computation; missing fixtures | docstrings say so; added `reeb_not_unique_of_lam_zero`, `symGauge_symmetricFlux_explicit`, `shear_orbit_existsUnique` |
| AV-L12 | "no hypothesis on `m`" statements are about a junk Hamiltonian at `m = 0`; iffs without differentiability are junk where `A` is not differentiable | docstrings say so |
| AV-L13 | notes: stale names in N-35; N-37 said the lift is not formalized; N-43 metadata; registry rows; entry-point and job counts in N-48; a quote in the Rosetta page dropped its hypothesis | corrected |
| AV-L14 | Dommaschk: `∃ S` form of the single-torus theorems; `q16_bounds_lt_strong` is arithmetic; "nested" carries AF-1; namespace `DommaschkKamA` reuses names of `DommaschkKamC` | recorded |
| AV-L15 | AD-L4, AD-L5 (16 November) are still open as recorded; `decide_cbv` in two pre-existing fixtures | unchanged |
| AV-L16 | duplicated proofs in `CrossedFieldOrbit` | recorded |

## Checked and found sound

- **Signs and conventions**, re-derived by hand by the sub-audits: the Lagrangian
  `(m/2)|v|² + qA·v` and its Euler–Lagrange equation; `inner_cross_curlOp`; the Hamiltonian and
  TauCeti's convention; the conserved quantities in the symmetric and Landau gauges; the gauge
  term; the `E × B` drift; `wedge12_eq_wedge` (exact, not up to a factor); the lift
  `ℱ = β − α ∧ dt` against the source and N-37; `liftStar` against TauCeti's intrinsic star and
  the orientation; `|ℱ|² = 2|B|²`.
- **Period theorems**: the path classes are those of the curve integrated on the left;
  `periodHom` is not a junk value under the stated hypotheses; `lineIntegral` with `deriv` is
  handled correctly at corners and end points.
- **Contract changes of November** (`PoloidalAngle` about a moving curve, `IotaOnTorus`,
  `CurrentFreeTransform` with the Ampère circulation, `BoozerChart`, `OmnigeneityContract`):
  consistent with the stated resolutions of AR-H1, AR-M1, AR-L4.
- **All recorded AD-* fixes** of 16 November are in the code.
- **Proof repairs** for Lean v4.35.0 and v4.36.0: no statement, definition or instance changed in
  any of the repaired files (confirmed from the diffs, file by file).
- **Dommaschk chain**: the headline theorems state what the README and notes claim (exact field,
  exact rotational transforms, bounds on the certified tori, not on surrogates). The trust path
  runs through soundness theorems with kernel-checked proof terms (`kernel_fact` 6,121 leaves,
  `kron2_proof` 1,224, `kron_lt` 1,203); 17 data and check modules spot-checked for shape.
- **Note-to-code links**: every declaration cited for N-45–N-48 exists; TauCeti file counts in
  N-48 are correct; versions agree in all documents; note and question IDs are unique after the
  renumbering of 22 November.

## Not examined

- Proof bodies in general (compilation and the axiom check were relied on); the proofs of
  `KamFlowFrameG`, `KamFlowStepG`, `KamFlowIterationG`; the internals of the handwritten Dommaschk
  chain modules beyond the declarations named in the sub-audit; numeric data values and the
  Python generators.
- TauCeti itself: its statements were read where used; its proofs and definitions were not
  audited.
- About 1,000 lines of intermediate lemmas in `BoozerWirtinger`; parts of `VacuumBoozerTorus` and
  `QSLinearSystem`; function bodies of the tooling.
- Older index lines of `notes/theory/README.md` cite declarations that do not exist
  (`vacuum_minB_counterexample` and others); not checked whether they are presented as planned.

## Open items after this audit

| ID | Item |
| --- | --- |
| AV-M7 | a chart-backed field with a constructed trapped bounce (C2 has no non-vacuous field instance) |
| AV-M8 | pin the poloidal angle of `BoozerChart`, or link its `ι` to `IotaOnTorus` |
| AV-M9 | uniqueness of `ι` without the differentiability hypothesis |
| AV-M4 | local (open-set) versions of the kinetic theorems; the helical generator |
| AV-M11 | reparametrisation invariance of `poloidalCirculation` |
| AV-L3, AV-L6 | tooling in the default import; layering |
| AF-1 | Bare predicates omit embeddedness. The candidate obligations were subsequently proved in Q-36. [N-52](../theory/irrational-return-embedding.md) |
| AD-L4, AD-L5 | unchanged |

## Downstream claims to re-read after the fixes

- Any statement that a candidate "satisfies C2": none is made; the README says C2 is open.
- Statements about "the magnetic symplectic form" and "gauge invariance" in N-48 and the Rosetta
  page: corrected in the same commit.
- Statements that the C1 current bound is "automatic": corrected in the same commit.

## Resolution (23 November 2026)

Fixes applied in the commit that adds this record. No existing theorem or definition statement
was changed; `StellaratorContract.lean` was changed in docstrings only. New sanity module
`Sanity/AuditContractC2`.

Commands run after the fixes:
- `lake build` of all 1,729 modules and both executables: successful, 13,003 jobs, no warning.
- `lake env lean scripts/check_axioms.lean`: "Axiom audit passed for 52147 PlasmaLean
  declarations"; 605 printed entry points, 20 of them the regression theorems of this audit.
- `lake env lean scripts/check_axioms_heavy.lean`: "Heavy axiom audit passed for 59106 PlasmaLean
  declarations"; 116 printed entry points, including `dommaschk_Q16_chart`.
- `node scripts/generate_handbook.mjs`, `node scripts/check_site.mjs`: passed.
