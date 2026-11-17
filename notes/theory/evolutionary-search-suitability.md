# Where evolutionary search fits the PlasmaLean goals

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-41` |
| Title | Suitability of evolutionary search (`plasmalean-evolve-optimize`) for the PlasmaLean goals and questions |
| Kind | research approach / design |
| Addresses | G-2, G-4, G-5, G-8, G-9, G-10; Q-3, Q-12, Q-13, Q-24, Q-25, Q-26; plan tracks for certificates and design (rungs L1–L2 of `plasmalean-design-stellarator`) |
| Depends on | The task server and search framework (`PlasmaLean.TaskHandlers`, `theory_server`, `scripts/evolve/evolve.py`, commit `c74b6b0`); `lowerBound_le`; `svFloorF`, `svCeilF`; `family2_stable_of_cert`; `suydamForm_lower_bound`, `picone_certificate`, `BartaCertificate.lower_bound`; `fieldDiv_fqsGen`; `filamentField_perturbation`; `compose_branch`; N-38 (Q-26) |
| Dependency requirement | Compiled declarations used as the analytic half of a certificate (the search supplies only finite data); the framework as tested on 17 November 2026 |
| Produces | A classification of goals and questions by fit; four ranked pilots; cautions; no theorems |
| Difficulty | routine (the assessment); moderate to research (the pilots) |
| Status | stated (proposal; no search run yet on a project question) |
| Lean evidence | infrastructure only: `PlasmaLean.ResponseExt`, `PlasmaLean.Elaborate`, `PlasmaLean.TaskHandlers` (default build); no claim of this note is a Lean theorem |
| Audit evidence | not audited |
| Last updated | 17 November 2026: created from a discussion with the user after the framework was added |

## Purpose and scope

The evolutionary framework searches for **one concrete Lean term** of a fixed type. A candidate
must (i) prove its constraints itself, cheaply, on the task server; (ii) have a **graded measure**
computable in exact arithmetic (`ℕ`, `ℤ`, `ℚ`; not `ℝ`) whose improvement means progress; (iii) be
cheap to check. On the laptop the server holds about 9.3 GB (7.2 GB mapped oleans, 2.1 GB heap),
checks one candidate at a time, and evaluation has no time limit.

Its comparative advantage is **proof-carrying results** and **structure found by the generating
agents** (replacing data by a formula so proofs scale), not raw numerical optimization, where
SIMSOPT, DESC, VMEC or a Python optimizer are faster. It therefore fits the places where the
project needs a finite witness or certificate with a margin. It does not fit general theorems,
all-time or open-ended claims as a whole, or per-candidate checks costing gigabytes.

Out of scope: running any search (that is the pilots' job), and any claim of optimality.

## Dependencies

All named declarations are compiled (default build unless stated); they supply the analytic half
("certificate ⇒ property") of each proposed search. `stable_band_of_sign_change` (Q-26 a) is
**not** yet in Lean; the burn-window pilot needs it first or states its sign conditions directly.

## Sources and prior work

The framework follows the AlphaEvolve pattern (population, analysis, generation by agents,
evaluation, selection) as implemented in the LeanTheory template (commits `72e8608`–`406a45b`).
The classification below is the user's question and this note's assessment; it is an opinion
about fit, not a result.

## Theory development

### Good fits

1. **Test functions for stability bounds (G-4, Q-3; technique `energy_coercivity`).** A Barta,
   Picone or Riccati gauge reduces stability to a pointwise inequality. Candidate: a test
   function with rational coefficients (polynomial or piecewise); measure: the margin `c`, made
   exact by the Horner bound `QPoly.lowerBound` with `lowerBound_le`; constraint: `c > 0` proved.
   For Q-3 the reduction is compiled (`family2_stable_of_cert`) and the certificate is missing.
   Barrier recorded in RG.2: linear-in-s certificates fail and the B-spline × rational basis fails
   the dense check at k = 0.9, and a full check is about 8,000 boxes per surface (100–200 CPU-h
   for the band search). So the search should evolve the *representation* of the test function
   against a cheap proxy (one surface, coarse cells, the hardest k), with the full check on the
   workstation. That is exactly where agent-generated structure may beat the bases tried so far.
   Caveat: family 2 carries net toroidal current (Q-18), so Q-3 is a C3 technique result, not
   current-free progress.
2. **Quasisymmetry jets (Q-24, Q-25 d, G-10).** Candidate: polynomial or Taylor-jet vacuum fields
   with rational coefficients (curl- and divergence-free by `ring`/`norm_num`); measure: the
   order to which the strong-QS linear system of `Theory/Fields/QSLinearSystem` holds, or the
   residual at a fixed order. The compiled jet obstruction (Q-25 a–b) constrains where to look.
   Output is evidence and conjectures for `explore-mathematics` / `try-to-prove`, never a proof of
   existence in a volume (Q-24 is open in the literature).
3. **Burn operating windows (G-2, Q-13, Q-26 a).** Candidate: rational operating points or profile
   parameters; constraints: power-balance sign conditions with the Bosch–Hale enclosures
   (`svFloorF`, `svCeilF`) inside their validity windows; measure: the band margin around a
   certified T*, or the smallest admissible renewal fraction. Cheap and exact. Q-13 already has
   proved obstructions (`stellaris_measured_fren_no_access_steady`, `…_loss`); a search can only
   probe parameters outside their hypotheses (for example profile peaking), and a failed search is
   not a proof that the obstruction is unremovable.
4. **Smaller certificates (G-9, Q-12).** Per certificate *piece* (one cell family, one block),
   candidate: certificate data; constraint: the checker accepts it; measure: size, digits, cell
   count or check time. This is the workstation's stated purpose ("a smaller certificate, not a
   bigger proof"). Only pieces that check in seconds within the budget qualify. (Q-6, the
   `outerArc` lines, is already done.)
5. **Exact refinement of design data (G-5, G-8; rungs L1–L2).** Second stage of a two-stage
   pipeline: an external optimizer proposes coil or boundary data; the search rationalizes and
   improves it under proved constraints (separation, curvature, length, coil-error bounds via
   `filamentField_perturbation`, margins over a parameter box). Measures need exact rational
   enclosures; Biot–Savart over `ℝ` is noncomputable.

### Partial fits (pieces only, usually on the workstation)

- **KAM budgets and windows (Q-2, Q-4, Q-5).** Measures come from heavy Kronecker certificates
  (GBs, minutes): not per-candidate on the laptop. On the workstation, with an untrusted cheap
  pre-filter, a search could tune Chebyshev degree, grids and window splits.
- **Counterexamples for audits.** Hand construction is usually faster for sanity triads
  (`quasisymmetry_not_pde_symmetry` was found by hand); a search pays off for extremal witnesses
  or sharp constants, for example the constant of Q-23 (b).

### Unsuitable

- G-7 and Q-7–Q-11 (PDE existence and regularity): general theorems, no finite witness or measure.
- Q-21, G-11, Q-28 (a) (definitions, contracts, fixtures): formalization design.
- G-3 (model adequacy): judgment about omitted physics, not optimization.
- G-1, G-5, G-6 as whole claims (all-time confinement): only their finite certificate pieces.
- G-8 as one search: C1–C5 on a common witness is too heavy per candidate; search per gate and
  compose with `compose_branch`.

### Cautions

1. **Model exploitation.** Searches drift to validity-envelope edges (Bosch–Hale window ends,
   supplied ISS04 scaling, cell boundaries). Put envelopes in the constraints and red-team each
   problem with `plasmalean-audit-domain` before running.
2. **A score is a bound, not optimality.** Feasibility suffices for design; for obstruction
   questions (Q-13) a failed search is not evidence.
3. **Hard constraints stay constraints**, never objective penalties.
4. **Resources.** One server and one search at a time, no heavy builds alongside; heavy
   evaluations on the workstation.

## Claims and evidence

- The classification above: **conjecture** (an assessment of fit, untested on project questions).
- The framework works on PlasmaLean code (toy example optimum found, `sorry` rejected, a candidate
  using `QPoly.lowerBound` validated): **numerical observation** of the tooling, recorded in the
  plan's §13 entry of 17 November 2026; not a mathematical claim.

## Difficulty, barriers and readiness

The assessment is routine. Each pilot needs a carefully stated `problem.json` whose constraints
encode the exact hypotheses of a compiled reduction. Q-3 is limited by check cost (workstation);
the burn window by the missing `stable_band_of_sign_change`; the QS jets by choosing a measure
with a useful gradient.

## Outputs and next dependencies

Ranked pilots (each a run folder `notes/reasoning/<date>-evolve-<slug>/`):

1. **Picone gauge for a Newcomb or Suydam form** with a known answer (`picone_certificate`,
   `suydamForm_lower_bound`): calibrates the pipeline on plasma mathematics; laptop.
2. **Q-3: representation search for the family-2 Barta test function** on a one-surface proxy;
   full checks on the workstation.
3. **Q-24/Q-25 (d): QS-order exploration of polynomial vacuum jets**: highest research value,
   output conjectures.
4. **Q-26 (a)/Q-13: burn operating window**: cheap; after `stable_band_of_sign_change` is in Lean.

Registry: route added to Q-3, Q-12, Q-13, Q-24 and Q-26 (17 November 2026).
