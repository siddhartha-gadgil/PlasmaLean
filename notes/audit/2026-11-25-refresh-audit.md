# Refresh audit of all changes since 23 November 2026, 25 November 2026

Skill: `plasmalean-audit-domain`, proof policy `plasmalean-lean-proofs`. Findings carry the
prefix `AW-`.

| Item | Value |
| --- | --- |
| Previous audited commit | `6ceca0e` (complete refresh audit, 23 November 2026, findings AV-*); scoped reviews at `4b0bf64` (annulus and embedding) and at N-60 |
| Audited commit | `0bec221` (branch `main`, 25 November 2026) |
| Toolchain | Lean `v4.36.0`; TauCeti `v4.36.0`; Mathlib transitive at `fc4f59e577` |
| Scope | every Lean file changed since `6ceca0e` (531 files: 361 Design, 101 Theory, 39 Certificates, 26 Sanity, root, task handlers, both axiom scripts); the generated-module pipeline in `scripts/dommaschk_kam/` (about 160 scripts that compile Lean into caches under `.lake/`); 180 changed documents (164 new notes N-49–N-210, the plan, README, progress) |
| Kernel | unchanged since the last audit (`PlasmaLean/Kernel/` not touched in the range) |
| Method | mechanical checks by the lead; six independent read-only sub-audits (kinetic mirror theory; geometry, contract, ODE and stability theory; forms, Noether and Lorentz modules; certificate checkers; the generated-module pipeline; notes and public claims), each given files and a red-team checklist, not the authors' conclusions; the lead re-checked the main findings in the code |
| Result | **no critical finding: no false or vacuous exported theorem in the repository, and no certificate checker that can accept false data.** 3 high (public C2 evidence outside the repository; reproducibility; a C2 band clause without content), 14 medium, 16 low |

## Commands run

- `lake build --no-build` (default targets): up to date, 11,949 jobs, no warning.
- `lake build --no-build` of the 180 on-demand modules imported by `scripts/check_axioms_heavy.lean`:
  two stale (`DommaschkInterfaceArcProfiles`, `DommaschkKamAInterfaceColumns`); built alone,
  peak 1.6 GB and 5.1 GB.
- `lake env lean scripts/check_axioms.lean`: "Axiom audit passed for 55063 PlasmaLean
  declarations".
- Task server: started with `ensure_server.sh`, `check` and `eval` tasks against new
  declarations (`MovingRadialFaces.stays_between`, `.separator`), stopped.
- Scan of the 531 files for `sorry`, `admit`, `axiom`, `native_decide`, `decide`, `bv_decide`,
  `unsafe`, `implemented_by`, `@[extern]`, `opaque`, `ofReduceBool`, `set_option`, `instance`:
  hits only in docstrings and in the task-handler tooling. Five instances, all proved
  (`SimplyConnectedSpace` of explicit regions, a `Decidable` by `inferInstanceAs`). `set_option`:
  `maxHeartbeats` (up to 0 = unlimited, 11 uses), `maxRecDepth`, `Elab.async`, the line linter.
- `scripts/audit_kernel_fact.py` (leaf-size classification, informational): stopped by a
  10-minute timeout before finishing; not a soundness check, not repeated.
- Copyright headers: `Theory/Geometry/UniformRadialWindow.lean` (default build) and
  `Design/DommaschkRadialActionWindows.lean` lacked the `Authors:` line (fixed, AW-L1).

## Findings

### High

**AW-H1 — public C2 claims rest on Lean declarations that are not in the repository.**
The headline results of the QA2R campaign are stated by theorems that Python scripts in
`scripts/dommaschk_kam/` generate (f-string sources), compile with `lean` against the current
`.lake/build`, and record in `accepted.json` receipts in caches under `.lake/<name>/` (ignored by
git). Examples: `DommaschkCertifiedRadialSector.on_nested_tori` (N-205, README "All 2,656 signed
ODE steps … have passed Lean"), `DommaschkPeriodicOriginalCollar.cartesian_field_line` (N-203,
N-210), `DommaschkFullSignedBirth.*` and `DommaschkActionFlightFloor326.from_birth` (README flight
times 54.98668 < T < 264), the N-161/N-162 variation bounds, `DommaschkQ0R523MirrorBandBirth337`
(N-207). Neither `scripts/check_axioms.lean` nor `scripts/check_axioms_heavy.lean` audits them,
and `workstation/REVIEWED.md` has no entry for the campaign. Of 159 new notes with a Lean-evidence
row, 43 cite only generated declarations and 73 a mixture; 28 notes with a "verified" status cite
only generated names; N-205 has no evidence row. "On demand" is used for cache-only modules,
although the plan defines on-demand modules as committed modules outside the default import.

The pipeline itself was found sound given an honest filesystem: each receipt comes from `#print
axioms` of the fully qualified theorems with the exact set `{propext, Classical.choice,
Quot.sound}` required, and the key hashes the full generated source. Its weaknesses are AW-M10 to
AW-M12. See "Headline re-check" below for what was re-verified on the laptop.

*Action:* label these claims "workstation-generated Lean (receipt key …), not in the repository
build or axiom audit" until the final-layer sources are committed to an on-demand directory and
audited by an opt-in script (user decision, see "Decisions").

*Resolved, 25 November 2026 (user decision 1: commit the sources).* The generated modules cited
in the notes (184), with every generated module they import, are in the repository: 43,435 Lean
sources, stored as 258 compressed archives in `generated/qa2r/archives/` with a SHA-256 manifest
and the campaign receipts. They form the on-demand Lake library `QA2RGenerated`. A cold
`lake build` of all of them on the workstation passed (about 8.7 hours on 22 jobs; largest
module 34 GB), and `scripts/check_axioms_qa2r.lean`, run once for each cited module, found only
`propext`, `Classical.choice` and `Quot.sound` in about 4.97 million declarations of the
43,435 modules; all 70,219 fully qualified receipt theorems exist. Report:
`generated/qa2r/replay-report.json`. "On demand" now has its plan meaning for these modules.
Generated modules that no note cites (about 27,000 in the workstation caches, mostly superseded
versions) remain outside the repository and support no claim. The metadata findings (AW-M14)
are not changed by this.

**AW-H2 — the main C2 results cannot be reproduced from the repository.** 119 of the 161 new notes
cite `/tmp` paths (354 distinct names). The N-205 replay needs `/tmp/plasma-n169-packets.json`,
`/tmp/plasma-n186-height-band.json`, `/tmp/plasma-n188-faces.json`, produced by commands spread over
other notes, which use further `/tmp` inputs; the commands use `.venv-ws`, which the repository
does not define for this purpose. N-203 (the collar) takes no `/tmp` input and is reproducible in
principle. *Action:* a single replay script with repository-local intermediate files, or committed
compressed intermediate results with hashes.

**AW-H3 — the band form of C2 (`Contract.GuidingCentreBand`) can be met without confinement
content.** `Theory/Contract/TrappedBirthBand.lean:119`. The birth measure `ν`, the support set, the
fraction (relative to `support ∩ trapped`), the horizon (`0 < horizon`) and the excursion are all
free. The library proves `Sanity/TrappedBirthBand.quadratic_guidingCentreBand`: a Dirac measure on
one birth, `support = covered = {birth}`, fraction 1, any horizon. In the design layer
`DommaschkCommonLittlejohnTime.BandAt` and `VacuumLittlejohnWindow.exists_control`,
`VacuumLittlejohnCompact.compact_guidingCentreBand` give `∃ T > 0` from local existence; N-125
notes that this works at every regular vacuum seed. So instances of the band clause carry no
design content unless the horizon, the population and a fraction floor are fixed inputs. The notes
(00-model-contracts.md, README, progress "positive covered fraction") present these instances as
C2 progress. Related: the clause puts no Maxwell or regularity condition on `B` and uses the
totalised `fderiv` (AW-M3); `axis` may be any compact set (AW-M4).
`quadratic_guidingCentreBand` is the compiled regression for this finding.

*Addendum, 28 November 2026 (not an audit).* A `BandContract` instance for the QA2R field was proved at the user's request (`DommaschkWideTubeRows000Band.band_contract`, N-216 stage 5). Its horizon is an input bounded by an explicit inequality (not `∃ T > 0` from local existence), the birth law must be absolutely continuous, the field is Maxwell-regular on the region and the axis is a curve. It does not remove this finding: the support is defined as the interior of the reference population of good births, so the fraction 1 holds by construction, the excursion is the envelope size, and the horizon is about a tenth of a half bounce. The instance has not been audited.
*Action:* treat every band-form instance with an existential horizon as not establishing C2
(recorded in the plan); strengthening the clause is a contract change (user decision).

*Resolved, 25 November 2026.* The evidence is the Lean sources, and these are now in the
repository; `python3 scripts/qa2r/replay.py` unpacks them, checks the hashes, builds them with
`lake build` and runs the axiom audit, reading nothing under `/tmp` and no campaign cache. The
generators and their numerical inputs remain untrusted and are not needed for the replay.
Regenerating the sources from the `/tmp` inputs is still not possible from the repository; this
does not affect the validity of the Lean results. The cold build also answers AW-M10 for the
committed modules (every module recompiled), and the replay report records the commit and a
dirty-tree flag (AW-M11).

### Medium

- **AW-M1 (documentation)** N-48 says closedness of the HYM lift "without regularity" removes a
  limit; it is an extension by junk values (`FormHYMComplex.lean:577–680`). Witness: the step
  form `H(x₀) dx₁∧dx₂` gives `mextDeriv = 0` although `dω = δ(x₀) dx₀dx₁dx₂`. Regression to add:
  `stepForm_regionForm_closed`.
- **AW-M2** `oneWayBounceTime` (`MirrorBounceTime.lean:22`) is 0 when the integrand is not
  integrable (tangent mirror, infinite physical time). All current consumers carry an integrability
  hypothesis; a future upper bound without one would be trivially true.
- **AW-M3** `GuidingCentreBand`: no `div B = 0`, vacuum or `C¹` condition; `littlejohnVelocity`
  uses `fderiv`, which is 0 where `B` is not differentiable; the sanity field has `div B = 2x₀`.
- **AW-M4** `GuidingCentreBand.axis` may be any nonempty compact set (a ball containing the band
  makes the excursion clause trivial near it).
- **AW-M5** `Geometry.AnnulusOrbitExistence.exists_inverse_square_orbits` (the c/ε² theorem) is
  sound and satisfiable, but `VolumeChart` has no sanity instance and no bridge to Littlejohn
  dynamics or to `GuidingCentreBand`; 00-model-contracts.md cites it as the form of the C2 band
  clause.
- **AW-M6** Fixed-window clipped action versus first-well action: `MirrorHeightAction.unique_height`,
  `MirrorActionComparison.exists_continuous_fixed_action_height`, `MirrorActionFlight.*` work with
  the action on a fixed bracket, which adds all accessible pockets; at the returned height the well
  may have merged (`launch_action_can_be_discontinuous`). True statements; docstrings should say
  "clipped-window action".
- **AW-M7** ODE certificates give existence (`TrajectorySlabs.Step.solve`,
  `PositionFrameChain.Chain.trajectory`, `DommaschkEndpointSignedTrace.Joined : ∃ y`), while notes
  speak of "the solution". Uniqueness is derivable from `FieldBounds` (continuous Jacobian on a
  compact trial region); add `Chain.unique` or reword.
- **AW-M8** `RadialTile.Half.Encloses`, `DommaschkLocalMirrorGraphs.TraceBounds`, `sector_graphs`:
  all field inequalities are hypotheses; no theorem derives `Encloses` from the checked chain, and
  `sector_graphs` has no users. The note calls the result a compiled on-demand theorem; it is
  conditional.
- **AW-M9** N-210 C2 row: everything Lean establishes there is a field-line statement; `stays_inside`
  is about arbitrary functions with hypotheses `faces`, `Observes` (|φ| ≤ 2⁻¹⁹, height within
  2·10⁻⁶ of `h_U` at every possible exit) and `drift`, undischarged for any particle. Q-35 row:
  "particle observable" is a field-line action.
- **AW-M10** Cache reuse trusts `accepted.json` without re-running Lean; N-203's "byte-for-byte
  replay" does not show recompilation (the output drops timing and artifacts). Add a cold-cache
  `--reverify` mode and record the machine, commit and cache state of each replay.
- **AW-M11** Receipt keys cover the generated source, parent keys and hand-picked Lake `.trace`
  digests; no git commit or dirty-tree flag is recorded.
- **AW-M12** `scripts/dommaschk_kam/results/completed_radial_sector_20261125.json` is hand-assembled;
  counts such as 2,656 slabs and 31,200 cells and several N-203 figures are script diagnostics, not
  Lean statements (the Lean statements match where they exist; see the constants check).
- **AW-M13** Public wording: slide 1 title ("controls particle motion for times of order ε⁻²"),
  README "finite-time radial confinement from a bound on action drift", README/progress "positive
  covered fraction" (AW-H3); README:105–109 says the band predicate is realised only by a quadratic
  mirror, which contradicts README:47.
- **AW-M14 (metadata)** 28 notes with "verified" status cite only generated names; N-205 and N-200
  have no Lean-evidence row.

### Low

- **AW-L1** Missing `Authors:` header in two files (fixed).
- **AW-L2** N-48: stale "not formalized" lists in `FormHYMLift`/`FormHYMStar` and plan lines
  2634, 2681; the "Current state" table and the fourth-round bullet still give the wrong hypotheses
  for global Lorentz existence (`LorentzGlobalExistence` needs `C¹` `E`, `B`, no potential).
- **AW-L3** `LorentzOrbitOpen.lorentzOrbit_existsUnique_of_confined` has no instance.
- **AW-L4** HYM energy fixtures use only τ-independent variations; `chernNumber` is over the tori
  γ×S¹ for periodic cylinder-chart data only (disclosed; keep the qualifier in public wording).
- **AW-L5** `MovingRadialFaces.separator` and `.stays_between` are unused; `stays_between`'s face
  hypotheses are not restricted to times before the first exit (unlike `FaceBounds.stays_inside`).
- **AW-L6** `CylinderInterfaceGap.nonaxisymmetric_gap`: `ℓ`, `D` free (linked to `log h`,
  `(h²−1)/2` only by `close_wall`); Bessel and impedance inputs are hypotheses (disclosed).
- **AW-L7** `TrappedBirthCoordinates.positive_mass` assumes the birth lies in the interior of the
  regular-birth set; openness is proved only in Design files.
- **AW-L8** `MirrorFlowPersistence` global versions need a globally Lipschitz, bounded, nowhere-zero
  `B` (not coil fields); the local versions are the usable ones.
- **AW-L9** Argument order differs between `action (f w a b h)` and
  `oneWayBounceTime (weight f height left right)`; "dimensionless action" is wrong (length ×
  √field; the full bounce invariant is twice the one-way value).
- **AW-L10** `MirrorWellComponent.LaunchWell.regular_at` includes the mirror endpoints;
  `decreasing_density_counterexample` uses a negative field strength.
- **AW-L11** No `Sanity` module for the mirror theory; `Branch`, `Family`, `CappedFamily`,
  `FlowBracketIn`, `FamilyControl` lack explicit parabolic inhabitants (Design instantiates
  `Branch`/`Family`).
- **AW-L12** Duplicate lemma: `TrajectoryTaylorModel.dyadic_cover` and `cover_spatial_radius`.
- **AW-L13** Pre-existing `decide +kernel` in `PolyInterval`, `Kronecker2DWeighted`,
  `KronLowMemCompute` (sound; against the no-`decide` rule).
- **AW-L14** Pipeline: parent import roots after the first are merged without a receipt check; the
  axiom audit has no planted-`sorry` negative test; four leaf verifiers omit
  `-DwarningAsError=true`; N-210 cites the conditional `cartesian_field_line` where
  the generated `DommaschkPeriodicOriginalCollar.original_collar` is the unconditional statement
  on the certified tori (the repository's `DommaschkPeriodicBirthCollar.from_period` needs the
  generated `Sector 0 (202/64)`).
- **AW-L15** Note hygiene: stale names `SurfaceData.Spans`, `VacuumField.not_isContactAt`,
  `FIv.coshSmall`, four module-prefixed names in N-42/N-43, the planned
  `Fields.fieldLine_confined_of_proportional_defect`; "Updated" instead of "Last updated" in four
  notes; "physical"/"actual" should be defined once (true solutions of the vacuum field-line ODE in
  dimensionless units, not particles or SI).

- **AW-L16** On-demand modules are not warning-free: building
  `DommaschkRadialActionWindows` replays 267 linter warnings from nine on-demand modules
  (`DommaschkBounceFlowStep`, `BounceLaunchStep`, `BounceTubeData`, `MirrorBracketSlab`,
  `MirrorFramePath`, `MirrorLaunch`, `MirrorLaunchData`, `MirrorSectorFlow`,
  `ReferenceFirstDefect`): long lines, missing spaces, unexplained or unscoped `maxHeartbeats`,
  deprecated `if_true`/`if_false`, unused tactics. The default build has none.

## Checked and found sound (selection)

- Mirror theory normalisation: `action = ∫ w√(2(h−f))`, `oneWayBounceTime = ∫ w/√(2(h−f))`,
  dJ/dh = T without a factor-2 error; `MirrorAction.shape`, `action_eq_fixed`, layer-cake and
  collar estimates, Sard and area-formula height statistics, `CylindricalActionSensitivity`.
- `IrrationalTorus`/`IrrationalSection`/`SectionFlow` (embedded torus from irrational transform),
  `EmbeddedTorus` strong enough for C1; annulus confinement with uniform constants and estimates
  used only up to the first hit; ODE, Grönwall and moving-frame files; level graphs and crossings;
  `InterfaceFourierTaylor`, `InterfacePrincipalDirection`.
- Forms: integer periods (`IsPeriodic.torusPeriod_mem`, non-trivial wire bundle), anti-self-duality
  and complex structure of the lift, the magnetic-form sign, global Lorentz existence; AV-H1, AV-M3,
  AV-M4, AV-M5, AV-M6 fixes still hold.
- Certificates: dyadic Taylor/Horner fits and covers (no gaps), outward rounding in native
  intervals, quadrature directions and clipping, sublevel grids and speed histograms,
  position-frame slabs and gluing, trigonometric packets and harmonic blocks; `FieldBounds`
  discharged in `DommaschkPhysicalBackwardSecondStep`.
- Numeric constants in notes against Lean: 0.2386 = 1193/5000; 0.0063, 0.0090; 0.000996 =
  249/250000; u ∈ [47/100, 239/500]; |φ| ≤ 2⁻¹⁹; 54.986688 and 57.806066 floors, 264; collar 1/256,
  1/1000, 1/1536; area 1.972·10⁻⁹: all match.

## Open items from 23 November

AV-M7 (C2 has no field instance with content; now sharpened by AW-H3), AV-M8 (`BoozerChart` does
not pin the poloidal angle), AV-M9, AV-M11, AV-L3, AV-L6 remain open; AV-M4 partly resolved.

## Decisions for the user

1. *(Decided 25 November 2026: commit, as compressed archives; done, see AW-H1.)* Commit the final-layer generated Lean sources (at least the headline modules and their
   parents) to an on-demand directory with an opt-in axiom audit, or keep them workstation-only
   with labelled claims (AW-H1, AW-H2).
2. *(Decided 28 November 2026: `BandContract` of N-213 is adopted as the band form of C2, with an acceptance rule applied at review; the Lean definition is not strengthened yet. AW-H3 partly resolved.)* Strengthen `GuidingCentreBand` with fixed inputs (horizon floor, absolutely continuous or
   thermal birth density, fixed support with nonempty interior, fraction floor, Maxwell and
   regularity of `B`, axis as a curve) (AW-H3, AW-M3, AW-M4).
