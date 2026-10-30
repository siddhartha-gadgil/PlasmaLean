# PlasmaLean implementation plan: theory → proof techniques → successively realistic models

**Proposed review amendment, 24 October 2026:** section 11 adds a sourced evolution, symmetry and thermal-verification programme and contribution targets. It does not mark new mathematical work complete.

Prepared 2026-10-20 against `8dcf3a2` (baseline: 14 Oct 2026 run, 53 modules, standard axioms only). Updated after each phase; see §9.
This is a plan. Nothing listed here as a target is implemented until a progress report says so. Status marks (✅ ◐ ○) reflect the latest report.

## The stellarator contract (30 October 2026)

**User-approved restructuring (30 October 2026).** This section re-aims the project. It takes
precedence over older formulations of the goals in RG.1 and §0. History, verified results and
declaration names are unchanged; only the framing and the priorities change.

**Rationale.** Tokamaks are not stable in the sense that matters for a reactor: they rely on a large
inductive or driven toroidal plasma current, which brings current-driven instabilities (kinks,
tearing), disruptions and the need for continuous current drive. That is the reason for
stellarators. So the plan should not mainly try to prove the existence of *non-tokamak* or
*non-axisymmetric* solutions (a Grad counterexample, a field that is "not exactly symmetric"), but
of solutions with the additional properties a stellarator needs. Those properties exclude tokamaks
and are achievable by stellarators, and the decisive ones concern the drifts of thermal ions and
electrons.

**The contract.** A candidate satisfies the stellarator contract when, for one decoded field and
equilibrium with common witnesses:

| Clause | Requirement | What it rules out or admits |
| --- | --- | --- |
| **C1. Current-free rotational transform** | The net toroidal plasma current vanishes or is small: ‖I_tor‖ ≤ I_max, a stated bootstrap-level bound (vacuum, J = 0, is the limiting case); and the rotational transform satisfies ι ≥ ι_min > 0 on the confining surfaces, provided by the external field (3-D shaping or helical coils), not by plasma current | Excludes tokamaks: an axisymmetric current-free field has ι = 0 (its field lines do not rotate poloidally), so it confines nothing. Admits vacuum stellarator fields |
| **C2. Omnigeneity / small neoclassical transport for thermal particles** | For thermal ions **and electrons** (not only 3.5 MeV alphas): the bounce-averaged radial drift of trapped particles vanishes (omnigeneity) or is bounded by a stated amount, or the effective ripple ε_eff is bounded on the confining surfaces | Quasisymmetry and quasi-isodynamic fields are special cases. An axisymmetric field is automatically omnigenous; a generic 3-D field is not. C2 is what a stellarator needs to match tokamak neoclassical confinement |
| **C3. MHD stability at finite β** | Mercier (interchange), ideal ballooning and, where available, global ideal modes, at a stated β > 0, with the reductions named | Current-driven modes (kinks, tearing driven by I_tor) are absent by C1; pressure-driven modes remain |
| **C4. Existence** | Nested flux surfaces on the confining region (certified invariant tori, or a validated equilibrium) and force balance J × B = ∇p (vacuum: J = 0) | Makes C1–C3 statements about an object that exists |
| **C5. Thermal performance** (added 30 October 2026) | On the **same** candidate that satisfies C1–C4: the core temperature stays above a burn threshold (e.g. T ≥ 10 keV in the core) over the operating interval [0, T_burn] (or forever), and below wall and material limits. Derived from power balance with alpha heating (Bosch–Hale), bremsstrahlung and transport losses; the neoclassical losses come from C2 (omnigeneity bounds for thermal ions and electrons); anomalous (turbulent) transport is a stated, supplied scaling (ISS04 or an Â bound), never hidden | C5 is the existing goal G-2 restated as a contract clause. The Solov'ev results show it only for a tokamak model with a supplied transport solution |

C1–C4 are about the field and its stability; C5 makes the temperature requirement explicit.
**C2 couples into C5:** poor omnigeneity means large 1/ν neoclassical losses (χ ∝ ε_eff^{3/2} in the
1/ν regime), which can make burn inaccessible, as in the proved Stellaris obstructions
(`stellaris_measured_fren_no_access_steady`, `stellaris_measured_fren_no_access_loss`, Q-13).

**How this re-aims the project.**

- Non-axisymmetry and "not exactly symmetric" become *consequences* of C1 (with C4), not goals: a
  current-free field with ι > 0 cannot be axisymmetric. Results whose only content is
  non-axisymmetry (Q-17, the Grad counterexamples of N-28) are mathematical infrastructure, not
  design progress.
- C1 and C2 are the new primary filters for candidates. A candidate that carries a net toroidal
  current of the order of the field-producing current is tokamak-like under C1 however
  non-axisymmetric it is.
- C2 must be stated for **thermal** particles. Alpha confinement (G-6, Q-1) is one part of C2, not a
  substitute for it.
- Tokamak models (Solov'ev) stay in the library as models for G-2 and as test beds for techniques;
  they are not stellarator candidates.
- The goal registry RG.1 is restated around C1–C5 (G-1, G-2, G-4, G-8 restated; G-10, G-11 new),
  the questions Q-18–Q-22 are added, and the work selection RG.5 now puts current-free and omnigenous
  candidates first.
- Definitions of net toroidal current, bounce-averaged radial drift, omnigeneity and ε_eff, and the
  C5 thermal clause, are normative specifications in `notes/formalization/00-model-contracts.md`
  (contract entries `CurrentFreeTransform`, `BounceAveragedDrift`/`Omnigenous`/
  `EffectiveRippleBound` and `ThermalPerformance`), not yet in Lean as contract predicates (Q-21).

**Where the project stands against the contract (30 October 2026, honest summary).**

- **C1:** partial, vacuum only. The exact rational stellarator field is a vacuum field
  (`RationalStellarator.field_vacuum`), so it carries no plasma current, and a KAM-certified exact
  invariant torus with a Diophantine rotation number (torus A, ι ≈ 0.137, inside `torusA_exact`)
  confines its field lines for all time (`rationalStellarator_confined_forever_exists`). Not yet
  stated in Lean: ι ≥ ι_min on a nested family of surfaces, and any finite-β current-free
  equilibrium. The Landreman families carry a net toroidal current: for family 2,
  μ₀ I_tor(k₀)/2π = `curK` (`torCurrent_eq`), an integral of the positive integrand
  κ(F₁/2 + E/λ²)/2π (`F1_pos`, `Eint_pos`), so I_tor > 0 for k₀ > 0 (a short corollary, not yet a
  named declaration; Q-18). They are tokamak-like under C1 unless that current is shown to be
  bootstrap-level.
- **C2:** essentially nothing for thermal particles. Alpha results (passing alphas in the exact
  rational field for all time under the Littlejohn model; passing alphas in near-QA for 0.19 s) are
  particle-confinement results for one species and mostly for passing orbits. Weak quasisymmetry is
  defined (`WeakQS`, `qsDefect`) and the Landreman families are proved not weakly quasisymmetric
  (`family1_not_weakQS`, `family2_not_weakQS`). No bounce-averaged drift, omnigeneity or ε_eff is
  defined in Lean.
- **C3:** Landreman family 2 has a certified Mercier-stable band (`family2_mercier_stable_derived`;
  the Mercier index is supplied) and ballooning reduced to one certificate (Q-3), but family 2
  fails C1. The Solov'ev stability results are tokamak results. Nothing at finite β for a
  current-free candidate.
- **C4:** satisfied for the vacuum rational field on the region inside one certified torus; for
  finite β only for the Landreman families (which fail C1) and the symmetric models.
- **C5:** shown only for a tokamak model: on the Solov'ev field, for every supplied solution of the
  radial transport model starting in a certified band, the core stays ≥ 10 keV for all time
  (`solovev_one_plasma_actual` and variants; existence of the transport solution assumed, pressure
  bounded by a budget). On stellarator parameters only 0-D windows (Stellaris ISS04,
  `Design/BurnWindowStellarator`) and proved obstructions at measured renormalization factors
  (Q-13). Nothing on a C1–C4 candidate, and no neoclassical loss derived from C2.

Sources: [domain-libraries](domain-libraries.md) (run protocol), [roadmap](formalization/08-roadmap.md) (gates P0–P9, research problems R1–R8),
[PDE bounds](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/pde-bounds-and-verification-roadmap.md) (Stages 1–7, Milestones A–G),
[microturbulence](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/microturbulence-and-available-energy.md), [holomorphic/KYM/Wick](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/holomorphic-bundles-kym-wick-rotations.md),
[BKM/Perelman](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/bkm-regularity-and-perelman-burn-bounds.md).

---

## Research graph (added 29 October 2026)

This part adopts the LeanTheory theory-development workflow (skill `plasmalean-develop-theory`):
PlasmaLean builds theory and formalizes it while designing stellarators. It indexes goals (`G-*`),
questions (`Q-*`) and research notes (`N-*`) with stable identifiers; the sections §0–§13 below
are kept unchanged as the history and the dated logs. Statuses here are mapped from the logs of
§9, §10 and §13 and the dated reports in `progress/`; nothing is upgraded by this mapping.
A dependency is **established** only when its required output is a named compiled Lean declaration
(standard axioms only). Results in on-demand top modules (not imported by `PlasmaLean.lean`) are
marked *on-demand*: they were built and axiom-checked on the workstation and spot-checked on the
laptop (policy of 25 October 2026, `workstation/REVIEWED.md`). New notes follow
`notes/note-template.md`. `N-*` note IDs are distinct from the §12 work packages N1–N3, and the
gates P0–P9 (roadmap), E0–E8 (§11.2), P1–P4 (§12) and the rungs M0–M6 (§5) keep their names.

### RG.1 Goal registry

Restated around the stellarator contract (C1–C5, section above) on 30 October 2026. Stable IDs are
kept where the meaning carries over; superseded meanings are recorded in the row. New meanings get
new IDs (G-10, G-11).

| Goal | Goal and success criterion | Supports / supported by | Status | Evidence so far (declarations) / needed |
| --- | --- | --- | --- | --- |
| `G-1` | **Current-free confinement (C1 + C4)** (restated 30 October 2026): for one candidate, a field with net toroidal plasma current ‖I_tor‖ ≤ I_max (vacuum as the limiting case), nested certified invariant tori on a confining region, and ι ≥ ι_min > 0 on them provided by the field; field lines (and guiding centres, with the reduction named) stay inside. *Superseded meaning (legacy G1, 29 October):* "confinement and stability for one candidate", which counted symmetric and tokamak models; stability is now G-4 (C3) and omnigeneity G-10 (C2) | supported by G-5, G-6, Q-16, Q-18, Q-19, Q-21; supports G-8 | active (partial, vacuum) | Satisfies C1 + C4 in vacuum on one torus: `RationalStellarator.field_vacuum` (J = 0), `rationalStellarator_confined_forever_exists` (all-time field lines inside a KAM-certified exact torus with Diophantine rotation number ι ≈ 0.137); C2 unknown (Q-19). Guiding centres: `alpha_gc_passing_confined_forever`, `alpha_gc_confined_forever_robust`, `alpha_gc_confined_forever_pm` (passing alphas, Littlejohn model supplied). *Not candidates under C1:* the Solov'ev results (`reactor_alpha_born_confined`, `reactor_ballooning_all`, `reactor_mercier_stable`) are tokamak models, kept for G-2 and as technique test beds; `stable_uniform` (screw pinch) is a model problem. Needed: ι ≥ ι_min on a nested family of certified tori stated in Lean; a finite-β current-free equilibrium |
| `G-2` | **Thermal performance = contract clause C5** (legacy G2, restated 30 October 2026): on the same candidate that satisfies C1–C4, core temperature above a burn threshold (e.g. T ≥ 10 keV) over [0, T_burn] (or forever) and below wall and material limits, from power balance with Bosch–Hale alpha heating, bremsstrahlung and transport losses; neoclassical losses from C2 (Q-22), anomalous transport a stated supplied scaling (ISS04 or an Â bound). C2 couples into C5: poor omnigeneity (large 1/ν losses) can make burn inaccessible (Q-13) | supports G-8; supported by Q-10, Q-13, Q-15, Q-22, G-10 | active (tokamak model and 0-D only) | `m1_burn_window` (0-D), Stellaris ISS04 window (`Design/BurnWindowStellarator`), `solovev_one_plasma_actual` (two-sided band for every supplied transport solution, pressure budget; **a tokamak model**: the Solov'ev field is axisymmetric and current-carrying, so this is a model for G-2, not a candidate). Needed: barriers on stellarator geometry with χ bounded by C2 (Q-15, Q-22), existence of the transport solution |
| `G-3` | **Model adequacy and probabilistic goals** (§12): quantify one omitted effect on a design observable (N1), activation rules (N2), decision infrastructure (N3); probabilistic loss and uncertainty (P1–P4) | supports G-1, G-2, G-8 | proposed | none in Lean; specifications in `notes/goals/` |
| `G-4` | **Finite-β stable current-free equilibrium (C1 + C3 + C4)** (restated 30 October 2026): an exact or validated finite-pressure equilibrium with net toroidal current ‖I_tor‖ ≤ I_max and ι ≥ ι_min > 0 from the field, with certified Mercier, ballooning and interchange stability at a stated β > 0 (reductions named). *Superseded meaning (Phase 14):* "a stable non-axisymmetric finite-β equilibrium", which did not constrain the current | supports G-8; supported by Q-3, Q-14, Q-18, Q-20 | active (no current-free candidate) | Landreman family 1 force balance and `family1_mercier_unstable` (negative); family 2 `family2_mercier_stable_derived` (band k ∈ [0.7, 0.9], λ = 200, Mercier index supplied); ballooning reduced to one certificate (`family2_stable_of_cert`, `family2_stable_of_secular_cert`). **Both families carry net toroidal current** (family 2: μ₀ I_tor/2π = `curK` > 0 by `torCurrent_eq`, `F1_pos`, `Eint_pos`; Q-18), so they are C3 technique test beds, tokamak-like under C1 unless that current is bootstrap-level. Needed: a current-free finite-β equilibrium (Q-14 stepped pressure across the rational field's torus; or a finite-β Dommaschk/QA equilibrium) and then C3 on it; Q-3 stays useful as technique |
| `G-5` | **Coil-produced confinement** (Phase 13): field lines of the field of a concrete coil set confined for all time (or a long certified horizon) | supports G-1, G-8 | active (all-time: blocked, research) | `coil_stellarator_confined_concrete_N` (52 transits, field-line existence assumed). Needed: Q-2 |
| `G-6` | **Robust alpha confinement** (Phases 11–12): all-time confinement of 3.5 MeV alphas on physically meaningful energy, pitch and B₀R₀ ranges, passing and trapped. Under the contract the trapped part is the alpha component of C2 (G-10) | supports G-1, G-10 | active | `alpha_gc_passing_confined_forever_quarter` (on-demand; λ ∈ [0, 1/4], one energy and B₀R₀), `alpha_gc_confined_forever_energy_window` (on-demand; ±0.4 eV × λ ∈ [0, 1/16]), `alpha_trapped_reactorQA_averaged` (passing, near-axis QA, 0.19 s). Needed: Q-1, Q-4, Q-5 |
| `G-7` | **Verified plasma evolution** (§11): for one candidate, a certified interval on which the selected plasma model exists and stays within error, stability, thermal and geometric bounds | supports G-8; supported by Q-7–Q-11 | proposed (E1 done) | E1: `lieBracket_gradient_of_contDiffAt`, `quasisymmetry_not_pde_symmetry`; conditional `riccati_le_initial`. Needed: gates E2–E8 |
| `G-8` | **Integrated stellarator candidate (C1–C5 with common witnesses)** (restated 30 October 2026): one decoded candidate satisfying C1 (current-free ι ≥ ι_min), C2 (omnigeneity or a bounded ε_eff for thermal ions and electrons), C3 (finite-β stability), C4 (nested surfaces, force balance) and C5 (thermal performance, G-2) with the same witnesses, then coils and engineering margins (M6, §11.1). *Superseded meaning:* "coils, equilibrium, stability, transport and engineering margins on one candidate" without the C1/C2 filters | supported by G-1, G-2, G-4–G-7, G-10, G-11 | open | `Bridge/Contracts` (common-witness composition) only |
| `G-9` | **Auditable certificates within the laptop budget** (Phases 15–16, auxiliary): every concrete check an explicit certificate, ≤ 6 GB per Lean process, no `decide` of any kind | supports all | active | Certificate tactics in `PlasmaLean/Certificates/`; workstation pipeline. Needed: Q-6, Q-12 |
| `G-10` | **Omnigeneity for thermal particles (C2)** (new, 30 October 2026): on the certified surfaces of a current-free candidate (G-1), the bounce-averaged radial drift of trapped thermal ions and electrons vanishes (exact omnigeneity) or is bounded by a stated amount, or ε_eff ≤ ε_max (a stated value, e.g. the W7-X level of about 1 %); quasisymmetry and quasi-isodynamicity are admissible special cases | supports G-8, G-2 (via Q-22); supported by Q-16, Q-19, Q-21, Q-1 | open (definitions not in Lean) | Only adjacent: `WeakQS`, `qsDefect`, `family1_not_weakQS`, `family2_not_weakQS` (N-27); `boozerGC_trapped` (exact-symmetry Boozer model). Needed: Q-21 (definitions and sanity triad), then Q-19 on the rational field and Q-16 on a Dommaschk QA fit |
| `G-11` | **Contract infrastructure** (new, 30 October 2026, auxiliary): kernel-level definitions of net toroidal current, rotational transform of the field on a family of tori, bounce-averaged radial drift, omnigeneity and ε_eff, each with the sanity triad, and a `StellaratorContract` record composing C1–C5 on a common witness | supports G-1, G-4, G-8, G-10 | open | specifications in `notes/formalization/00-model-contracts.md` (not yet in Lean); adjacent compiled pieces: `torCurrent` (family 2), `iotaK`, `WeakQS`. Needed: Q-21 |

**Re-labelled results (30 October 2026).** The Solov'ev work (`solovev_one_plasma_*`,
`reactor_alpha_born_confined`, `reactor_ballooning_all`, `reactor_mercier_stable`) is a tokamak model
for G-2 and a technique test bed, not a candidate. Q-17 and the Grad counterexamples
(`family1_grad_counterexample`, N-28) are mathematical infrastructure, not design progress: they
establish non-symmetry, which the contract treats as a consequence. The vacuum rational stellarator
field (`Design/RationalStellarator*`) satisfies C1 in vacuum (current-free, KAM-certified torus with
ι ≈ 0.137 > 0); its C2 status is unknown (Q-19). The Landreman families are finite-β C3/C4 test beds
that carry net toroidal current (Q-18).

### RG.2 Question registry

| Question | Statement | Needed by | Status | Current best answer / barrier |
| --- | --- | --- | --- | --- |
| `Q-1` | All-time (or slowing-down-time) confinement of **trapped** 3.5 MeV alphas in near-QA: can the per-bounce remainder (phase shear) be bounded? *Re-framed (contract, 30 October 2026):* this is the alpha component of C2; the per-bounce radial kick is the single-orbit form of the bounce-averaged radial drift, so the definitions of Q-21 and the thermal-particle question Q-19 come first, and a bound here should be stated as an omnigeneity defect | G-6, G-10, N-17 | open (research, parked) | Compiled: `reference_kick_osc` (kick amplitude ≤ 0.0816 T m²), `exactQA_kick_osc`. Barrier: one-bounce remainders (Lipschitz–Grönwall hopeless, `e^{KP} ≈ e^{29000}`), shears, validated bounce-time enclosure, existence of re-anchored references (`trapped-alpha-status.md` §3); re-anchoring with absolute amplitudes cannot close (Phase 11 part 1) |
| `Q-2` | **Coil-produced all-time confinement**: can a KAM torus refitted to `tfField + polyCoilFieldC` meet the smallness budget? | G-5, N-16 | blocked (research) | On-demand `CoilKamCert` proves only a vacuous residual bound (≈ 10⁹ against ≈ 10⁻³⁰ needed). Barrier: sharp cancellation-aware complex sup bound, torus-adapted neighbourhood, anisotropic strips, high-precision refit (≈ 4 CPU-days estimated) |
| `Q-3` | **Family-2 ballooning certificate**: one pointwise inequality on surface × ℝ for Landreman family 2 on the Mercier-stable band. *Re-framed (contract):* family 2 carries net toroidal current (Q-18), so this is a C3 technique result on a tokamak-like test bed, not a stellarator candidate; lower priority than C1/C2 work, but the checker transfers to a current-free equilibrium | G-4 (technique) | open | Reduction compiled (`family2_stable_of_cert`, `family2_stable_of_secular_cert`); numerics stable (tail margin ×2.36–×9.39); linear-in-s certificates fail, the B-spline × rational basis fails the dense check at k = 0.9; checker not written (≈ 8,000 boxes per surface, 100–200 CPU-h for the band search) |
| `Q-4` | **Wider energy window** (±3 eV, then ±1 %) and a joint B₀R₀ range, with λ up to 1/4. *Re-framed (contract):* passing alphas in the vacuum rational field are a C1-compatible particle result; it does not address C2 (trapped and thermal particles), so it ranks after Q-19 and Q-21 | G-6, N-14 | open (workstation route) | Compiled (on-demand): ±0.4 eV × λ ∈ [0, 1/16]. Barrier: the torus family moves ≈ 30·Δρ; needs re-certified low-resolution chains with larger admissibility balls, ≈ 3 / ≈ 10 CPU-h (`energy-window.sh`) |
| `Q-5` | Passing confinement **beyond λ = 1/4** | G-6 | open | λ = 1/4 is the limit of the passing argument with ‖B‖ ≤ 3B₀ (`quarter_passing_margin`); needs a sharper ‖B‖ bound or another argument |
| `Q-6` | **Landreman `outerArc` certificates**: explicit certificates for the ≈ 135 `outerArc` lines of `LandremanFamily2Cert1–7` | G-9, G-4 | done (30 October) | All 136 outerArc checks in `LandremanFamily2Cert1–7` converted to `f2_arc_cert` (shared module `LandremanFamily2ArcCert`); Cert2/5/6 split (Cert2b/5b/6b) to stay ≤ 5.5 GB; CPU 1.43× (≈ 2025 s); peaks 3.5–5.2 GiB; `family2_mercier_stable(_derived)` on standard axioms; default-build `decide +kernel` lines 266 → 130 |
| `Q-7` | **E2–E3**: Pizzocchero–Tassi Proposition 4.3 on the periodic benchmark, then a certified trajectory with full residual enclosures | G-7, N-19 | open | not started in Lean (§11.3 is the first target) |
| `Q-8` | **E4**: toroidal-domain continuation (harmonic flux sectors, Hodge coercivity, Kozono–Shimizu–Yanagisawa small data) with a nonempty admissible set | G-7, N-19 | open | not started |
| `Q-9` | **Helical MHD regularity** (§1.3): a theorem, with hypotheses, for the helically symmetric reduction; the Riccati inequality dY/dt ≤ −νY + CεY² for MHD (R3) | G-7, N-19 | open (research) | Only the conditional comparison is compiled (`riccati_le_initial`, `riccati_exp_decay`); the inequality is a hypothesis |
| `Q-10` | **E5–E6**: existence/continuation for the radial transport model; a steady pressure-matched state (pressure equality, not a budget); the corrected relative-entropy identity with all terms | G-2, G-7, N-2, N-6 | open | Transport solutions are supplied in `solovev_one_plasma_*`; the relative-entropy identity is proved informally (N-2), not in Lean |
| `Q-11` | **E7–E8**: compatible numerics (constrained transport, admissible states) and integration on a shared candidate | G-7, G-8 | open | not started; E8 needs the earlier gates |
| `Q-12` | **Phase 16 remaining opaque leaves**: replace the remaining `decide +kernel` and opaque `kernel_fact` leaves within ≤ 6 GB and the olean budget | G-9 | active | §13 stage 9: 297 default / 2,114 overall lines with `decide +kernel`; 6,098 class-b `kernel_fact` leaves in the default build (0 of ≥ 0.1 s); `decide_cbv` in on-demand Mu3–Mu5 Adm; open: `NearAxisQAAveraged` parts, the fast side `famTB − famO`, `nodeFin`/`famL1` leaves, `KamTorusACheck`/`SurrogateCheck`/`FrameCheck` |
| `Q-13` | Is the 0-D / 1-D burn obstruction at nominal confinement removable by profile peaking on stellarator geometry (ISS04 needs f_ren above measured values)? *Contract (C5):* this is the C5 obstruction for supplied anomalous scaling; with Q-22 the same question must be asked with C2-derived neoclassical losses added (poor omnigeneity can make burn inaccessible) | G-2 (C5), N-5 | open | Proved obstructions: `stellaris_measured_fren_no_access_steady`, `stellaris_measured_fren_no_access_loss`; the 1-D route on stellarator geometry is Q-15 |
| `Q-14` | **Stepped pressure across the exact KAM torus** (Phase 14 route A): a finite-β equilibrium glued across the certified torus of the rational field. Under the contract this is the lead route to Q-20 (current-free finite β), provided the net toroidal part of the sheet currents is controlled | G-4, Q-20, N-12, N-13 | open (lead) | plan only (`after-kam.md` §3, `finite-beta-stellarator.md`) |
| `Q-15` | Transport barriers (T ≥ 10 keV in the core) on a **non-axisymmetric** validated geometry, with χ bounds from Â or neoclassical theory stated as supplied scalings; under the contract the geometry should satisfy C1 and the neoclassical χ comes from C2 (Q-22) | G-2, Q-22 | open | Barriers exist on the cylinder, helical and Solov'ev geometries only |
| `Q-16` | **A quasisymmetric solution**, *re-aimed at C1 + C2 (contract, 30 October 2026)*: the target is a current-free field with ι ≥ ι_min > 0 (C1) that is omnigenous in the quasisymmetric form (C2). The decided vacuum criterion below already fits the contract (vacuum ⇒ I_tor = 0; ι ≥ ι_min; small ε_QS relative to ι). The finite-β criterion is now decided by the contract: **zero (bootstrap-level) net toroidal current**, ‖I_tor‖ ≤ I_max, replacing the alternative non-Killing bound on ξ. Decided criterion (user, 30 October 2026), vacuum version: an explicit or validated **vacuum** field with certified invariant tori on a nested region, rotational transform ι ≥ ι_min > 0 on them, and a certified quasisymmetry defect ε_QS small **relative to ι** (both numbers reported; in vacuum an axisymmetric field has ι = 0, so ι ≥ ι_min excludes trivially near-axisymmetric fields). The finite-β version needs a separate criterion (plasma current gives ι > 0 to near-tokamak fields): zero net toroidal current or a non-Killing bound on the generator ξ, to be decided | G-1, G-10, G-4, G-6 | open (research); the strong form (exact QS in a volume) is open mathematics | See N-27. Exact QS on a volume: neither existence nor non-existence is known (Constantin–Drivas–Ginsberg, arXiv:2009.08860; Burby–Kallinikos–MacKay, arXiv:1912.06468). Route (i), near-axis remainder, not recommended (the vacuum expansion is ill-posed without regularization, Ruth–Jorge–Bindel arXiv:2411.04352). Route (iii) negative: QS with a generator nonvanishing on the axis forces constant ‖B‖ on the axis, and both Landreman families have non-constant axis ‖B‖ for every ε ≠ 0 (compiled: `family1_not_weakQS`, `family2_not_weakQS`). Recommended: route (ii) as an explicit vacuum field (finite Dommaschk sum fitted to a QA target, exact by identity) + KAM-certified invariant tori + Boozer angles by one more cohomological equation + certified non-QS ℓ¹ part of ‖B‖. Criterion decided: vacuum version as stated (ratio form) |
| `Q-17` | **A Lean statement of a Grad counterexample** (*re-labelled, contract 30 October 2026: mathematical infrastructure, not design progress*; non-symmetry is a consequence of C1, and both Landreman families carry net toroidal current, Q-18): for Landreman family 1 (and family 2), one theorem giving smooth fields on a toroidal domain with nested toroidal flux surfaces, non-constant pressure, force balance, and no continuous Euclidean symmetry (axial, helical or reflection); then the non-stellarator-symmetric τ-extension of Issan–Citrin–Landreman–Tracey (arXiv:2610.07304) | G-4, N-28 | family 1 verified (`family1_grad_counterexample`); family 2 and τ-extension open | `family1_grad_counterexample`: smooth B, J, p on 𝒰; ∇·B = 0 and force balance with the gradient of p = (2δ − 2ψ)/μ₀; ψ a first integral with compact nested sublevel sets, each level set ψ = c ∈ (0, δ] homeomorphic to Circle × Circle (`torusMap`); p non-constant; no rotation, translation or screw-motion symmetry (`killing_trivial_of_axis`); contrast `axisymmetric_limit_lie_zero` at ε = 0. Not covered: plane reflections; family 1 has ι ≡ 2 (closed field lines), so family 2 (sheared ι) is the stronger target |
| `Q-18` | **Net toroidal current of the Landreman families** (contract C1): compute I_tor(ψ) for families 1 and 2 and compare it with the field-producing current (B₀R₀·2π/μ₀) and with a bootstrap-level bound. If it is not small, the families are tokamak-like under C1 (ι comes from plasma current) | G-1, G-4, Q-16, Q-17 | open; family 2 essentially answered | Family 2: μ₀ I_tor(k₀)/2π = `curK λ (1/4) 4 k₀` (`torCurrent_eq`, current through ζ = 0), with integrand κ(F₁/2 + E/λ²)/2π > 0 by `F1_pos`, `Eint_pos`; so I_tor > 0 for 0 < k₀ < 19/20, and the F₁/2 part does not vanish as λ → ∞ (a positivity corollary and the ratio to the external current are short Lean targets, not yet named declarations). Family 1: not computed (`LandremanEquilibrium.current` is available) |
| `Q-19` | **Bounce-averaged drift / ε_eff for the rational stellarator vacuum field** (contract C2): on the certified surfaces of `RationalStellarator.field (1/4)`, compute (numerically first, as an untrusted oracle) the bounce-averaged radial drift of trapped particles and ε_eff, then decide whether a certified bound is reachable | G-10, G-1 | open | nothing yet; the field has no optimization for omnigeneity, so a large ε_eff is the likely outcome (numerical observation needed). Inputs: the KAM tori and Boozer-angle pipeline of N-27; definitions of Q-21 |
| `Q-20` | **A finite-β current-free equilibrium** (C1 + C4 at β > 0): stepped pressure across the certified torus of the rational field (Q-14), or a finite-β equilibrium near a Dommaschk QA vacuum field, with ‖I_tor‖ ≤ I_max proved | G-4, G-8 | open (research) | Q-14 is the lead (`after-kam.md` §3); stepped-pressure equilibria carry surface currents whose net toroidal part must be controlled |
| `Q-21` | **Definitions and model contracts for C1 and C2** (kernel-level): net toroidal current through a cross-section of a toroidal domain; ι of a field on a family of invariant tori; bounce-averaged radial drift (ψ̇ averaged over a bounce; zero for all trapped orbits iff ∂J/∂α = 0 for the second adiabatic invariant J); omnigeneity; ε_eff (Nemov et al. 1999). Each with the **sanity triad**: (1) axisymmetric ⇒ omnigenous (bounce-averaged radial drift zero); (2) current-free axisymmetric ⇒ ι = 0, hence no confining rotational transform (no confinement); (3) a generic 3-D field (an explicit one) is not omnigenous | G-11, G-10, G-1 | open (specification written) | Normative specifications: `notes/formalization/00-model-contracts.md`, entries `CurrentFreeTransform`, `BounceAveragedDrift`, `Omnigenous`, `EffectiveRippleBound` (not yet in Lean). Adjacent compiled: `WeakQS`, `qsError_rotGen_eq_zero_of_axisymmetric`, `boozerGC_trapped`, `torCurrent` |
| `Q-22` | **Thermal-particle neoclassical transport bounds feeding G-2**: from a C2 bound (ε_eff or bounce-averaged drift), a stated neoclassical scaling (1/ν regime χ ∝ ε_eff^{3/2}, supplied as a model law) giving χ bounds for ions and electrons on stellarator geometry, used in the barrier theorems of Q-15 | G-2, G-10, Q-15 | open | none; the transport barriers exist on cylinder, helical and Solov'ev geometries with supplied χ |
| `Q-23` | **Quasisymmetry ⇒ omnigeneity (the C2 bridge)**: (a) exact: weak quasisymmetry (`WeakQS`) implies zero bounce-averaged radial drift of trapped particles (omnigeneity); (b) quantitative: a quasisymmetry defect ≤ δ gives a bounce-averaged radial drift ≤ C·δ with explicit C, hence a bound on ε_eff and on 1/ν neoclassical transport feeding C5 | G-10, G-2, Q-16 | exact and per-bounce quantitative versions verified in the Boozer GC model (30 October); ε_eff link open | `omnigenousOn_of_exactQS` (exact QS + twist ⇒ ψ returns after every bounce), `approxOmnigenousOn_of_defect_le` / `bounce_psi_drift_le` (‖ξB‖ ≤ δ, B ≥ B_min, twist ι_min ⇒ ‖Δψ‖ ≤ 2H/(‖q‖ B_min ι_min)·δ·τ per bounce; linear in δ, sharp on an explicit counterexample); `exactQA` omnigenous; `reactorQA` worst-case drift ≤ 4182 T m²/s (not a transport estimate). Model scope: Boozer GC equations, orbits and bounce existence supplied; Boozer ξB not yet linked to `WeakQS`. Open: ε_eff and 1/ν, a sharp oscillation bound, the quasi-isodynamic route (N-29) |
| `Q-24` | **Existence of strongly quasisymmetric, non-symmetric fields in a volume** (vacuum or MHS) | Q-16, G-10 | open mathematics (research, not on the critical path) | Unknown in the literature (Constantin–Drivas–Ginsberg arXiv:2009.08860; Burby–Kallinikos–MacKay arXiv:1912.06468; Garren–Boozer suggests non-existence away from the axis). If proved, the validated near-QS route of Q-16 becomes exact; the design path does not depend on it |

### RG.3 Note registry and dependency graph

Status values: exploratory / stated / proof-ready / lean-ready / verified / blocked / refuted /
superseded; mixed notes list the status of their parts. "Lean" names compiled evidence.

| Note | File and title | Addresses | Depends on | Difficulty | Status / Lean readiness | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| `N-1` | `notes/theory/toroidal-min-b-obstruction.md`: min-B / max-J restrictions | G-1 | §1.1 correction | moderate | core verified (`VacuumField.not_strict_local_max_normSq`, `exists_vacuum_strict_interior_min`, `Theory/Fields/CurvatureObstruction`); G conjectured; Hall–McNamara lead | finite-β curvature obstruction (T1 ○) |
| `N-2` | `notes/theory/relative-entropy-dissipation.md`: corrected identity | G-2, G-7, Q-10 | §1.5 | moderate | 1-D verified (`relEnt_pointwise_identity`, `RelEntSetup.rate_eq` with boundary terms, `rate_le_neg_fisher_const_ref`, `rate_le_neg_fisher_steady`; old identity refuted in Lean, `old_identity_false`) | coercivity (𝓕 = 0 ⇒ T/T* constant, H ≤ C𝓕); radial axis term; 2-D/3-D |
| `N-3` | `notes/theory/flux-surface-holonomy.md`: periods, τ, Hodge bounds | G-7 (T10) | §1.2 | moderate | holonomy ↔ ι refuted; 2-form vanishing verified (`magneticTwoForm_flux_surface`); constant-metric τ/energy identity and Hodge period inequality verified (`periodBound_eq`, `energy_ge`, `energy_eq_iff`, `fieldLine_energy_ge`) | non-constant metric (isothermal coordinates, not in Mathlib) |
| `N-4` | `notes/theory/near-axis-quasisymmetry.md`: Garren–Boozer construction, Boozer GC model | G-1, G-6 | sources | hard | construction formal asymptotic; GC identity verified (`boozerGC_trapped_until`, `boozerGC_trapped`) | none pending; feeds N-8, N-17 |
| `N-5` | `notes/theory/stellarator-burn-parameters.md`: ISS04, reactor studies | G-2, Q-13 | Bosch–Hale, ISS04 (supplied) | routine | verified window and obstructions (`Design/BurnWindowStellarator`); parameters published | Q-15 |
| `N-6` | `notes/theory/transport-mhd-coupling.md`: one field for G-1 and G-2 | G-1, G-2, Q-10 | K2 kernel | moderate | verified in budget form (`solovev_one_plasma_actual`, `…_highQ_actual`, `…_ignited_actual`) on the Solov'ev field, **a tokamak model** (contract re-label, 30 October 2026: a model for G-2 and a technique test bed, not a candidate); solution existence and pressure equality open | Q-10; the transfer to a C1 geometry (Q-15, Q-22) |
| `N-7` | `notes/theory/near-qa-trapped-particles.md`: banana-alpha mechanisms | G-6, Q-1 | N-4 | research | mechanisms published; single well proved; superseded for status by N-17 | see N-17 |
| `N-8` | `notes/theory/guiding-centre-averaging.md`: averaging, exact-symmetry alphas | G-1, G-6 | N-4 | hard | verified (`reactor_alpha_confined`, `alpha_trapped_reactorQA_averaged`: passing, 0.19 s) | none; longer near-QA times would need new averaging |
| `N-9` | `notes/theory/first-stellarator-rung.md`: exact rational vacuum field (contract: satisfies C1 in vacuum; C2 unknown, Q-19) | G-1, G-5, Q-19 | — | moderate | verified (`Design/RationalStellarator`, `rationalStellarator_confined`: 95 transits) | superseded by N-10 for all-time |
| `N-10` | `notes/theory/kam-route.md`: KAM route to all-time confinement | G-1 | N-9 | research | verified (`rationalStellarator_confined_forever_exists`); the C1 + C4 evidence for the vacuum field | state ι ≥ ι_min on a nested family of certified tori (C1 in the form of G-1); supply surfaces for Q-19 |
| `N-11` | `notes/theory/kam-k3-plan.md`: explicit KAM theorem plan | G-1 | N-10 | research | superseded (K3 done, Phase 10) | none |
| `N-12` | `notes/theory/finite-beta-stellarator.md`: routes to finite β (contract: the Landreman families carry net toroidal current, Q-18, so they are C3/C4 test beds; the current-free route is Q-14 → Q-20) | G-4, Q-14, Q-18, Q-20 | sources (preprints) | research | family 1 verified with `family1_mercier_unstable`; family 2 `family2_mercier_stable_derived`; stepped-pressure route lead | Q-3, Q-14 |
| `N-13` | `notes/theory/after-kam.md`: coil KAM, stepped pressure, GC KAM | G-5, G-6, Q-2, Q-14 | N-10 | research | target 3 verified (N-14); target 1 blocked (Q-2); target 2 lead (Q-14) | — |
| `N-14` | `notes/theory/gc-kam-status.md`: guiding-centre KAM | G-6, Q-4 | N-10, Littlejohn model (supplied) | hard | verified (`alpha_gc_passing_confined_forever`; on-demand `alpha_gc_confined_forever_energy_window`, `alpha_gc_passing_confined_forever_wide`) | Q-4 |
| `N-15` | `notes/theory/robust-alpha-confinement.md`: intervals of ρ, v∥ < 0, μ > 0 | G-6 | N-14 | hard | verified (`alpha_gc_confined_forever_robust`, `alpha_gc_confined_forever_pm`, on-demand `alpha_gc_passing_confined_forever_quarter`) | Q-4, Q-5 |
| `N-16` | `notes/theory/coil-kam-status.md`: coil-field KAM stages | G-5, Q-2 | N-10, N-13 | research | stage-1 tools verified (default build); stage-2 certificate vacuous (on-demand `CoilKamCert`); blocked | stage-1 sharpening (complex sup bound) |
| `N-17` | `notes/theory/trapped-alpha-status.md`: trapped alphas, Phase 12 | G-6, Q-1 | N-4, N-7 | research | partly verified (`reference_kick_osc`, `exactQA_kick_osc`); blocked on the per-bounce remainder; contract: the alpha part of C2 | after Q-21: restate the kick as a bounce-averaged drift defect; then conserved-quantity comparison (route a) |
| `N-18` | `notes/pde-bounds-and-verification-roadmap.md`: Stages 1–7, Milestones A–G | G-1, G-2, G-7 | — | research | Milestone A verified (T1); others stated | link stages to Q-7–Q-11 |
| `N-19` | `notes/bkm-regularity-and-perelman-burn-bounds.md`: corrected evolution specification (§11) | G-7, Q-7–Q-10 | §1.3, §11 | research | E1 verified (`quasisymmetry_not_pde_symmetry`, `lieBracket_gradient_of_contDiffAt`); conditional Riccati verified; rest stated | Q-7 (first theorem, §11.3) |
| `N-20` | `notes/microturbulence-and-available-energy.md`: available energy, Â | G-2, Q-15 | sources | research | kernel lemmas verified (`Theory/Kinetic/AvailableEnergy`); opposite-sign claim refuted; Â bound stated | extract the Helander–Mackenbach Â formula (§1.5) |
| `N-21` | `notes/holomorphic-bundles-kym-wick-rotations.md`: exploratory geometry (T10) | G-7 | §1.2, §1.4 | research | exploratory; flux degree corrected to 0; refuted contract sketches fenced | verdict note before any Lean (T10 rule) |
| `N-22` | `notes/goals/` (overview, probabilistic, deterministic, milestones) | G-3 | §12 | research | stated (proposals); D/K cross-references unresolved | choose one N1 observable |
| `N-23` | `notes/design/vacuum-demonstrator.md`: tolerance-aware vacuum fixture | G-5, G-8 | — | routine | verified fixture (`Design/VacuumPair`, `Design/VacuumTolerance`) | none |
| `N-24` | `notes/formalization/00`–`09`: model contracts and topic specifications | all, G-11, Q-21 | — | — | active specifications (00 contracts is normative); C1/C2 entries added 30 October 2026 (`CurrentFreeTransform`, `BounceAveragedDrift`, `Omnigenous`, `EffectiveRippleBound`; not yet in Lean) | Q-21: Lean definitions and the sanity triad |
| `N-25` | `notes/Stellerator.md`: original design basis | G-8 | — | — | historical (illustrative distances are not universal limits) | none |
| `N-26` | `notes/theory/orbit-existence.md`: existence of the orbits the confinement theorems quantify over | G-1, G-6, MA-M1, MA-M2 | N-8, N-14; `FieldLineExistence` | hard | Lorentz part verified (`lorentzOrbit_exists`, `reactor_alpha_born_confined`, `reactor_alpha_confined_nonvacuous_35MeV`); Boozer part: band of births to 0.05 s and an explicit 1.5 μs horizon for the original class (`alpha_band_orbit_exists_005`, `alpha_orbit_exists_explicit`); proved obstructions `Dpsi_gt_psiStart`, `band_empty_Tav` | coordinates through the axis (user decision); uniqueness |
| `N-27` | `notes/theory/quasisymmetric-solution.md`: routes to a quasisymmetric solution (Q-16; re-aimed at C1 + C2 by the contract) | Q-16, G-1, G-10, G-4, G-6 | N-4, N-12; Landreman `field_axis` theorems; KAM pipeline | research | stated; route (iii) a proved barrier (`family1_not_weakQS`, `family2_not_weakQS`, with `WeakQS`/`qsDefect` in `Theory/Fields/WeakQuasisymmetry`) | first priority under the contract: Dommaschk QA fit (current-free by construction) with torus, ι and Boozer/ε_QS diagnostics; the same Boozer pipeline for Q-19 on the rational field |
| `N-28` | `notes/theory/grad-conjecture.md`: Grad's conjecture and the 2026 counterexamples (contract re-label: mathematical infrastructure, not design progress) | G-4, Q-14, Q-16, Q-17 | N-12, N-27; `LandremanEquilibrium.family1` | routine (synthesis) | stated | Q-17 for family 1; τ-extension; stepped pressure source [ELP] for Q-14 |
| `N-29` | `notes/theory/omnigeneity-bridge.md`: quasisymmetry ⇒ omnigeneity in the Boozer GC model | Q-23, G-10 | N-4, N-27; `helicalMomentum_conserved` | hard | exact and per-bounce bounds verified | ε_eff / 1/ν link; oscillation bound; link Boozer ξB to `WeakQS` |

Main dependency edges: N-9 → N-10 → N-14 → N-15 → (Q-4, Q-5); N-10 → N-13 → (N-16 → Q-2, Q-14);
N-4 → (N-8, N-7 → N-17 → Q-1); N-12 → (Q-3, Q-14, Q-16) → G-4; N-4 → Q-16 → G-6; N-2, N-6 → Q-10 → G-2, G-7;
N-19 → Q-7 → Q-8 → Q-11 → G-8.
Contract edges (30 October 2026): Q-21 → (Q-19, Q-16, Q-18) → G-10, G-1; N-9 → N-10 → Q-19 → G-10;
Q-14 → Q-20 → G-4; G-10 → Q-22 → Q-15 → G-2; (G-1, G-4, G-10) → G-8.

### RG.4 Strict audit status

The canonical first command is `start` (skill `plasmalean-audit-domain`). Previous code is in scope.

| Audit | Value |
| --- | --- |
| Audited commit | `cda8bd0` (first strict audit, 30 October 2026): kernel, repository and model-definition parts complete |
| Scope | full startup audit: all six kernel modules; repository scans; headline-claims trace; note-to-code links; certificate soundness |
| Kernel coverage | every kernel declaration reviewed (52: 28 definitions, 11 laws with 48 fields, 3 predicates, 10 theorems), record [`notes/audit/2026-10-30-kernel-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-kernel-audit.md) |
| Commands run | `lake build --no-build PlasmaLean` (current), `lake env lean scripts/check_axioms.lean` (122 entry points, standard axioms only), single-module builds of the new sanity modules, then `lake build PlasmaLean` (zero warnings) |
| Open findings | kernel: 1 medium (F-1), 9 low; repository: 0 critical, 1 high (H-1), 5 medium; see below and [`notes/audit/2026-10-30-repository-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-repository-audit.md) |
| Missing sanity checks | added: 58 kernel theorems in `PlasmaLean/Sanity/Audit{Equilibrium, ThermalSlab, Vacuum, Transport, Fusion}.lean` and 54 model theorems (plus 7 definitions) in `PlasmaLean/Sanity/AuditModel{GuidingCentre, Stability, Transport}.lean` (triad, risk-specific and regression checks), all in the default build; model record [`notes/audit/2026-10-30-model-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-model-audit.md) |

**Strict-audit findings (30 October 2026).**

- **H-1 (high, resolved by the model audit):** the model definitions behind the headline claims (`LittlejohnOrbit`, `LorentzOrbit`, `BoozerGCOrbit(On)`/`BoozerField`, `mercierIndex`/`MercierStable`, ballooning `P`/`Q`/`LineData.Stable`, `coefF`/`coefG`/`ModeStable`, `NewcombReduction`, `BoschHaleFine`, `ConfinementLaw`/`SteadyScaling`, `FluxGeometry.Laws`, `IsSolovevGeometry`/`IsHelicalGeometry`, `IsFieldLine`) were re-derived against their sources (Littlejohn, Boozer, Landreman–Jorge, the ballooning equation, Newcomb/Freidberg, Bosch–Hale, IPB98) and match. Findings:
  - **MA-M1 (medium, resolved as far as the ψ > 0 chart allows, 30 October):** orbits exist on the full horizon for a band of births further out (`alpha_band_orbit_exists_short`: 2.75 ≤ ψ₀ ≤ 5.5 for 8e-4 s; `alpha_band_orbit_exists_005`, `alpha_band_nonvacuous_005`: 4 ≤ ψ₀ ≤ 4.3 for 0.05 s), and for the original class ψ₀ ≤ psiStart on an explicit horizon of about 1.5 μs (`alpha_orbit_exists_explicit`). Proved limits: no band reaches ψ₀ ≤ psiStart (`Dpsi_gt_psiStart`) and none survives for T ≥ 0.06 s (`band_empty_Tav`); the full 0.19 s horizon for the original class needs coordinates through the magnetic axis (a change of the model statement, user decision). Earlier: local existence proved (`boozerGCOrbitOn_exists_local`; `alpha_trapped_reactorQA_averaged_nonvacuous` gives a constructed orbit satisfying the hypotheses on some 0 < T ≤ 0.19 s, N-26). Existence on the full horizon needs an off-axis bound and cannot hold for the whole class born at ψ₀ ≤ psiStart. Original finding: `BoozerGCOrbitOn` requires the orbit to stay off the magnetic axis (ψ > 0), so the near-QA results (`alpha_trapped_reactorQA_averaged*`, `alpha_trapped_reactorQA`, `reference_kick_osc`, `exactQA_kick_osc`) exclude axis-crossing orbits, and no such orbit is shown to exist for `reactorQA`. Scope now stated on the slides.
  - **MA-M2 (medium, resolved 30 October):** `reactor_alpha_born_confined` proves that 3.5 MeV alpha orbits born in the core exist for all time and all stay confined; `reactor_alpha_confined_nonvacuous_35MeV` gives an explicit witness at exactly 3.5 MeV; `reactor_alpha_orbit_exists_label` makes the alpha conjunct of `solovev_one_plasma_*` non-vacuous (N-26). Original finding: `reactor_alpha_confined` (the alpha conjunct of `solovev_one_plasma_*`) quantifies over all Lorentz orbits; non-vacuity is shown only by an alpha at rest, and no 3.5 MeV orbit is constructed (an ODE existence theorem would close this). Scope now stated in README.
  - **MA-L2–L9 (low):** motionless Littlejohn orbits through the `(B*_∥)⁻¹` totalization; `BoozerField` allows G = 0 and B ≤ 0; no sign constraints on Mercier data; `LineData` does not require k ⊥ B; `ModeStable` does not include force balance (`stable_all_modes` should restate `RadialBalance`); `NewcombReduction` vacuous on an empty admissible class; `FluxGeometry.Laws` admits ⟨|∇ψ|²⟩ ≤ 0; `tau` = 0 at P = 0. Each has a regression theorem.
- **F-1 (medium, fixed 30 October):** `PhysicalPlasma` now carries `composition : QuasineutralComposition p` (fuel plus impurity species with charges ≥ 1: quasineutrality, the definition of Z_eff and the ion ratio); `Zeff_ge_one`, `fuel_le_ions`, `ions_le_one` became theorems; the old counterexample is now `inconsistentPlasma_not_physical`; `m2Plasma` proved carbon-consistent (no numeric result changed). Original finding: `PhysicalPlasma` accepts inconsistent composition (fuel fraction 1 with Z_eff = 2), which overstates alpha heating. `m1Plasma` and `stellarisPlasma` are proved carbon-consistent; `m2Plasma` is not. Proposed fix: a quasi-neutral composition field in the law (changes a kernel law; user decision).
- **M-1 (fixed):** README claimed both signs of v∥ over the whole B₀R₀ interval; v∥ < 0 is proved only at the design B₀R₀.
- **M-2 (fixed):** "6 GB target met" contradicted the 6.17 GB peak (README, slides 0 and 32).
- **M-3 (fixed):** "all-mode" screw-pinch stability is for m ≠ 0, with Newcomb's reduced form supplied.
- **M-4 (fixed):** the heavy axiom script now fails on non-standard axioms and covers `CoilKamCert`. Originally: `scripts/check_axioms_heavy.lean` only prints and never fails; `CoilKamCert` is in no axiom script.
- **M-5 (open):** legacy `decide +kernel` lines (268 default, 1,797 on-demand code lines).
- **E-1 (resolved):** all 14 `ForceBalance` users tie the force to a real pressure gradient with the Ampère current; seven via a named `pressureGrad` with a separate derivative lemma, now restated with `gradient p` in `Design/ForceBalanceGradient.lean`. **MA-L6 (fixed):** `stable_all_modes_equilibrium` adds `RadialBalance` for the same profiles. The last 3 plain `by decide` in the default build were replaced.
- **Kernel low findings (scope, recorded):** E-1 `ForceBalance B J (J×B)` holds for any B, J (meaningful only when g is proved to be ∇p; Solov'ev, Landreman family 1 and the helical design do this, 14 other users unchecked); S-1 negative slab pressure allowed; T-1 zero slab thickness; V-1 `VacuumField ∅ B`; R-1 zero-duration transport solutions; R-2 solutions may leave `Tdom`; R-3 D ≡ 0 allowed; F-2 n = 0 power balance; F-3 totalized division. Each has a regression theorem. R-4 (plain `decide` in `Sanity/Transport`) is fixed.
- **Repository low findings:** 7 plain `decide` and 13 `maxHeartbeats 0` in the default build; misleading name `alpha_trapped_reactorQA_averaged` (a passing-alpha result); stale note names and docstrings; README coil and family-2 scope (fixed).

Known open findings, carried from the logs (severity provisional):

1. **Resource** (resolved 30 October): `LandremanFamily2MercierStable` (6.74 GB measured, from two whole-checker `decide +kernel` rejection fixtures) is split: the fixtures are rebuilt as explicit certificates (`oned_cert`, a new `f2_arc_cert` for the outer arcs, `fiv_cert`) assembled by `cellCheck_eq_of_pieces`; peaks now 1.40 GB (main), 2.74 GB (`…StableA`), 2.65 GB (`…StableB`); public names unchanged.
   `NearAxisQAAveraged` (6.16 GB before stage 9) is now split into four modules, all of which
   built in that rebuild; its conversion to explicit certificates is still open.
2. **Build state** (resolved): the ~204 modules left stale after stage 9 were rebuilt one at a
   time and in bounded parallel on 26 October (191 modules, no failures, no warnings); the full
   default build passed and `scripts/check_axioms.lean` (122 entry points) showed standard axioms
   only, before commit `2d620d2`.
3. **On-demand trust** (medium): the on-demand families (Ew1–4, Mu2–Mu5, MuQuarter, CoilKam*) are
   spot-checked, not rebuilt on the laptop, and are stale after stages 8–9 (Workstation.md, Next
   Commands).
4. **Legacy proof policy** (medium): `decide +kernel` lines (297 default, 2,114 overall) remain against the
   no-`decide +kernel` policy (Q-12). (`decide_cbv`, a kernel-checked proof-producing evaluation,
   is permitted for medium checks; see the lean-proofs skill.)
5. **Documentation** (low): the module docstring of `Certificates/EvalCert.lean` still says the leg
   checks are left to `decide +kernel`; `family2_mercier_stable` keeps the caveat of hand-derived
   flux labels, superseded by `family2_mercier_stable_derived` (claims should cite the latter).
6. **Notes** (low): the §12 cross-references D0–D4, K0–K6 and §12.10 remain unresolved.
7. **Scope, recorded** (not defects): supplied hypotheses in headline results: transport solutions
   (`solovev_one_plasma_*`), the Littlejohn guiding-centre model, ballooning reductions, the
   Landreman–Jorge Mercier index, field-line existence for the coil results, vacuum model field.

### RG.5 Work selection

- **Interactive** (default): after each work unit, report compiled results, unformalized arguments,
  conjectures and barriers, then offer a few ready items from RG.1–RG.3 plus free discussion
  (`work on G-…`, `Q-…`, `N-…` or a topic).
- **Autonomous** (`keep working`): choose the highest-value ready item whose established
  prerequisites are compiled, preferring work that unblocks several items, closes a validity gap
  (RG.4 findings first), tests a risky conjecture cheaply, or yields reusable theory; keep G-1 and
  G-2 both moving. Continue without waiting; stop for a user decision, missing authorization, a
  resource budget question, or when nothing useful is ready.

**Priority order under the stellarator contract (30 October 2026, user-approved).** Current-free
and omnigenous candidates come first, ahead of further non-axisymmetry results:

0. **The quasisymmetry ⇒ omnigeneity bridge** (Q-23, G-10): the exact bounce-average theorem and the quantitative defect bound in the Boozer guiding-centre model; it turns a certified small QS defect (Q-16) into a C2 bound, so it is a prerequisite for every C2 claim.
1. **Dommaschk QA fit** (Q-16, N-27 route ii): an explicit vacuum field (C1 by construction) fitted
   to a quasi-axisymmetric target, with certified tori, ι ≥ ι_min and Boozer/ε_QS diagnostics
   (workstation numerics first, untrusted oracle; then certificates).
2. **C2 diagnostics on the rational field** (Q-19): bounce-averaged radial drift and ε_eff on the
   certified surfaces of `RationalStellarator.field (1/4)`; decide whether it can satisfy C2 or is
   only a C1 demonstrator.
3. **Net toroidal current of the Landreman families** (Q-18): the positivity corollary of
   `torCurrent_eq` for family 2 and its ratio to the external current; family 1. Cheap, and it
   settles the families' status under C1.
4. **The definitions** (Q-21, G-11): net current, ι on a family of tori, bounce-averaged drift,
   omnigeneity, ε_eff in Lean, with the sanity triad.
5. Then: Q-20 / Q-14 (current-free finite β), Q-22 (thermal neoclassical bounds for G-2), and the
   C3 technique work (Q-3) to be transferred to a current-free equilibrium.

Lower priority than before: further non-axisymmetry or Grad-counterexample results (Q-17 family 2,
τ-extension), passing-alpha widening (Q-4, Q-5) and Solov'ev refinements, unless they serve one of
the items above. Validity work (RG.4 findings) and the laptop-budget work of G-9 (Q-6, Q-12) keep
their place as maintenance.

Earlier ready choices (29 October 2026, superseded by the order above): the startup strict audit
(RG.4, step 2, done); Q-6 (profile one `tipCell`); N-2 → formalize the 1-D relative-entropy
identity (done); Q-7 (Pizzocchero–Tassi Proposition 4.3); Q-4 on the workstation.

---

## 0. The two goals, and where we are

> **Historical status (14 October 2026).** The table below records the status when the plan was
> fixed and is not updated. For the current status see the phase log (§9), the phases after Phase 10
> (§10), the continued implementation log (§13) and the dated reports in `progress/`.

The project goal has two parts, and each needs its own chain of certificates:

| Goal | Chain of certificates | Status on 14 Oct |
| --- | --- | --- |
| **(G1) Confinement.** Field lines and particles stay inside, and the equilibrium is MHD stable. | vacuum/coil field → equilibrium → field-line barrier (KAM/first integral) → orbit confinement → MHD stability (local and all-mode) | Exact symmetric equilibria (Solov'ev, helical). Field lines and full orbits confined for all time in those equilibria. Suydam criterion proved both ways; Newcomb certificates for the screw pinch with \|m\| ≤ 6. Coil Biot–Savart field satisfies the Maxwell identities. Nothing yet for a coil-produced 3-D field. |
| **(G2) Hot for long enough.** The core temperature stays above an ignition/burn threshold over [0, T_burn] (or forever), and stays below wall limits. | energy balance (0-D) → radial transport PDE on the equilibrium geometry → comparison/barrier certificates → diffusivity bounds from turbulence/neoclassical theory → yield | **Essentially absent.** The kernel has no transport law, no fusion power and no radiation. `ThermalSlab` is an engineering slab, not plasma transport. |

**Strategic consequence:** G1 has momentum. G2 needs new kernel concepts and its first theory now. The cycles below interleave the two goals, so that every model rung advances both.

---

## 1. Corrections to the notes (do these first; formalizing them as written would be unsound)

Several statements in the newer notes are false or vacuous. Each correction gets a sanity theorem or a counterexample in Lean.

1. **Subharmonic means no interior *maximum*, not no interior minimum.** Both [PDE §2.2](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/pde-bounds-and-verification-roadmap.md) and [microturbulence §4, check 3](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/microturbulence-and-available-energy.md) say that \|B\|² subharmonic rules out a strict interior local minimum of \|B\|. That is backwards: \|x\|² is subharmonic with a minimum at 0, and minimum-B mirror fields (Ioffe/baseball coils) are vacuum fields. The correct statement is that \|B\| has **no strict interior local maximum** in vacuum. The real obstruction to min-B and maximum-J in *toroidal* vacuum fields is a different theorem; find the source (e.g. Hall–McNamara, Bernardin–Moses–Tataronis) and state it precisely. Lean: `vacuum_normSq_no_strict_interior_max`, plus a counterexample showing that a vacuum field can have an interior minimum of \|B\|.
2. **The magnetic 2-form vanishes on flux surfaces.** B is tangent to Σ_ψ, so ω_B restricted to Σ_ψ is zero. The line bundle on a flux torus is therefore **flat (degree 0)**, and `flux_degree > 0` in the [holomorphic note](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/holomorphic-bundles-kym-wick-rotations.md) is physically wrong. `holomorphicSectionDim` is also true by definition, so it checks nothing. Further correction (24 October): a flat connection's periods encode fluxes; its holonomy at one surface does not determine the rotational transform. The latter requires an oriented derivative ratio of fluxes across surfaces. Fix cycle orientations before identifying those derivatives. Re-target on periods, the conformal modulus τ(ψ), and the Hodge inequality in §11.6 (compare `Challenge6_ConformalTorusModulus`).
3. **2-D ideal MHD global regularity is open.** [BKM §2.2](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/bkm-regularity-and-perelman-burn-bounds.md) claims that helically symmetric MHD is globally regular. The planar 2-D fully viscous/resistive problem has global regularity; a helical reduction needs its own theorem and hypotheses. Quasisymmetry alone is not a PDE symmetry (§11.4). The Riccati law dY/dt ≤ −νY + CεY² is a heuristic, not a theorem. Keep only the *conditional* statement: if the differential inequality holds, then Y stays bounded below the threshold. Mark the inequality itself as research (R3).
4. **Vacuous kernel contracts.** `FutakiObstructionCertificate` is correct but needs ⟪μ x, u⟫ constant over **all** x. All the physics is in proving that hypothesis for an MHD ansatz family. `CommutedWallClearanceCertificate` is an arithmetic inequality with no link to any PDE. Each contract must come with a theorem that *produces* it from model hypotheses, or it stays out of the library.
5. **Unchecked identities.** These need derivation and sympy checks before Lean: the relative-entropy dissipation identity (BKM §3.1), the Helander–Mackenbach Â formula (extract it exactly from MPH 2022/2023), and the Klainerman–Sobolev step H² ↪ L∞ (commuting only with u and b controls *tangential* derivatives, so an elliptic-regularity step across surfaces is required).

The skills' adversarial-review step (§3, lane E) is how we stop this kind of error from recurring.

---

## 2. Three interacting layers

```
 THEORY (theorems about PDE/ODE/geometry)  ──►  TECHNIQUES (sound checkers, certificate formats)
        ▲                                                   │
        │ obstruction / missing lemma                       ▼
        └──────────────  MODELS (ladder M0…M6: concrete fields, profiles, parameters)
```

- **Theory** produces general theorems with hypotheses phrased as *certificate predicates*: Picone, Nagumo comparison, maximum principle, radii polynomial, Grönwall, KAM.
- **Techniques** turn each predicate into finite data plus a kernel-checked decision procedure: polynomial interval checker, Taylor models, SBP and M-matrix checkers, ℓ¹_ν convolution bounds.
- **Models** instantiate both on concrete realistic data. Every failed instantiation is classified as: weak bound (improve the technique), wrong representation, or genuine obstruction (new theory task, or a recorded counterexample).

### 2.1 Kernel extensions (minimal, typeclasses only, no axioms)

| New kernel file | Content | Sanity checks |
| --- | --- | --- |
| `Kernel/Vacuum.lean` | `VacuumField Ω B`: open Ω, C², div = 0, curl = 0. Promote this from `Theory/Fields/Maxwell` so that filament fields become instances. | Constant field; a filament field away from the source is an instance; \|B\|² subharmonic; a field with nonzero curl is not an instance. |
| `Kernel/Transport.lean` | `RadialHeatTransport V' χ S L T`: T(ψ,t) satisfies the flux-surface-averaged heat equation, with an axis regularity condition and an edge Dirichlet condition. `χ` is supplied and bounded as χ_min ≤ χ ≤ χ_max. | Constant T with S = L is a steady state. With no sources, ∫V'T is nonincreasing. Uniform χ on a slab reduces to the classical heat equation. |
| `Kernel/Fusion.lean` | `DTPowerBalance`: P_α = (E_α/4)n²⟨σv⟩(T), bremsstrahlung P_br = C_br n² Z_eff √T, and losses W/τ_E. `⟨σv⟩` enters only through a typeclass `ReactivityEnclosure` holding rational upper and lower bounds on keV windows (Bosch–Hale data, cited). | Zero density gives zero power. P_α increases with T on [5,60] keV. The Lawson triple-product threshold is recovered as a corollary. |
| `Kernel/LinearMHD.lean` (later) | Linearized ideal MHD ρξ̈ = F ξ, with F symmetric on a stated Hilbert-space pair (extends `AbstractEnergy`). | Energy conservation; a neutral mode is an instance with δW = 0. |

Every kernel change is recorded in the module docstring and in the assumption ledger.

---

## 3. Running a cycle (one "run" in the sense of domain-libraries.md)

Each cycle has five lanes. Lanes A–D run as **parallel sub-agents** using the project skills. To avoid build clashes, each agent owns separate new module files and a separate namespace. Use `isolation: "worktree"` only for refactors that touch shared files, because every worktree rebuilds Mathlib's `.lake`.

| Lane | Skill | Output |
| --- | --- | --- |
| **0 Audit** (main agent) | `plasmalean-audit-domain` | `lake build`, axiom check, status review, choice of 3–5 targets (at least one for G2) |
| **A Theory discovery** | `plasmalean-discover-theory` | `notes/theory/<topic>.md`: precise statements, informal proofs, sympy/numeric counterexample search, status tag (`proved informally` / `conjectured` / `refuted`) |
| **B Formalization** | `plasmalean-formalize-theory` | Lean modules for the statements lane A validated (or sourced theorems), with corollaries, degenerate cases and docstrings |
| **C Techniques** | `plasmalean-certify-numerics` | Checkers with soundness proofs; valid *and* invalid fixtures; `decide +kernel`, never `native_decide` |
| **D Models** | `plasmalean-design-stellarator` (and `-model-materials` for walls/coils) | Instantiations on the current ladder rung with realistic SI parameters |
| **E Review** (fresh agent) | `plasmalean-audit-domain` | Adversarial pass on new statements: vacuity, hypotheses that cannot be satisfied, wrong quantifiers, physically meaningless parameters. Each finding is fixed or recorded. |

> **Historical.** Lane C's "`decide +kernel`" predates the Phase 16 policy; new code now uses no `decide` of any kind (explicit certificates, skill `plasmalean-lean-proofs`). Lanes map onto the skills routed by `plasmalean-develop-theory`.

Sequencing inside a cycle: A and C start at once. B takes A's outputs from the previous cycle, plus any sourced theorems. D uses whatever B and C have merged. E runs last. The cycle closes with a progress report, `status.json`, slideshow, `README.md`, site regeneration and `check_site.mjs`.

Recommended size: 4–6 sub-agents per cycle (within the workflow guideline of fewer than 10).

---

## 4. Theory tracks (with technique companions)

Status legend: ✅ done · ◐ partial · ○ not started.

> **Historical status.** The marks below were last updated in the October phases and are not maintained; the current status of open items is in the Research graph (RG.1–RG.4) and the logs (§9, §10, §13).

| Track | Theory targets | Technique companion | Feeds |
| --- | --- | --- | --- |
| **T1 Elliptic/vacuum** (Milestone A) | Bochner: Δ\|B\|² = 2\|∇B\|² for vacuum fields ✅. Weak maximum principle for C² subharmonic functions on bounded open sets in ℝ³ (elementary ε\|x\|² proof using Mathlib's `laplacian`) ✅. Boundary-to-interior bound for \|B\|² and \|B₁−B₂\|² ✅. Corrected min/max obstruction (§1.1) ✅ (no *strict* interior local max of \|B\|² or \|B\|: `VacuumField.not_strict_local_max_normSq`, `VacuumField.not_strict_local_max_norm`; interior-min counterexample `exists_vacuum_strict_interior_min`, all in `Theory/Fields/Subharmonic.lean`); toroidal curvature obstruction ∇⊥B = Bκ ✅ (vacuum; finite-β ○). | 2-D surface cover with proof-term checker ✅ (volume error from face samples) | Coil error fields: the volume error follows from the surface error; M5/M6 |
| **T2 Sturm–Liouville** (Milestone B) | Picone, Riccati, Jacobi ✅. Ballooning operator with weight W and Barta certificate ✅. Sturm necessity: contrapositive ✅, constant-coefficient iff ✅, conjugate point ⇒ no supersolution ✅. Mercier criterion: cylindrical ⇔ Suydam ✅, general index (supplied, Landreman–Jorge) reduces to Suydam ✅; helical equilibrium Mercier-unstable (a = 0 proved); Solov'ev exact index certified on all surfaces ✅ (validated quadrature). Newcomb uniformly in m ✅ (screw-pinch example: all integer (m,n), m ≠ 0). Infinite-line ballooning with asymptotic tails ✅ (tail ⇔ −1/4 threshold, sharp). | Polynomial interval checker ✅. Piecewise and Taylor-model checker with sqrt/exp enclosures ○ | MHD stability of M2–M5 |
| **T3 Parabolic comparison** (Milestone D, core of G2) | Nagumo first-crossing lemma (the sanity check in PDE §4.2) ✅. Weak comparison for the quasilinear radial transport operator, with an axis condition and edge Dirichlet data ✅ (semilinear; quasilinear D(T) ○). Steady lower/upper barriers bounding T(ψ,t) for all t ✅. Time-dependent barriers ◐ (core lemma allows them); two-sided quasilinear bands ✅ (K2: D(ψ,T)). Relative-entropy dissipation: corrected identity derived (notes/theory) ◐. | Barrier checker: N[T_sub] > 0 on [0,1] via the interval checker. Rational barrier profiles produced by a solver oracle. | G2 directly: M1–M5 |
| **T4 ODE invariants** | Invariant intervals for 0-D power balance dW/dt = P_α(T) + P_aux − P_br − W/τ_E, with thermal-stability and ignition window theorems ✅. Grönwall consequences (`Mathlib.Analysis.ODE.Gronwall`) ✅. Burn-yield lower bound (BKM §3.2, conditional) ✅. | Root isolation for the cubic-like balance curve; exact Bosch–Hale enclosures | M1 and the T3 sources |
| **T5 Discrete energy** (Milestone C) | SBP identity giving discrete energy ✅ (all N). FEEC d∘d = 0, hence discrete div B = 0 ○. M-matrix discrete maximum principle for the transport scheme ✅ (linear scheme). Consistency estimate linking discrete and continuum barriers ○. | `decide` on rational matrices | T3 (verified discretization), M2 |
| **T6 Functional-analytic validation** (Milestone G) | Contraction and radii inequalities ✅. ℓ¹_ν Banach algebra with convolution bounds ✅. Radii polynomial for ODE BVPs ✅ (generic validated BVP); 1-D (slab) Grad–Shafranov with exponential profile validated ✅ (classical C², kernel ForceBalance), then 2-D Grad–Shafranov fixed boundary, then a 3-D near-axis/DESC equilibrium ○. | Exact computation of Y₀, Z₁, Z₂ with tail estimates (truncation in ν-weighted norms) | M3–M5 equilibria |
| **T7 Field-line Hamiltonian** (Stage 5) | First-integral barriers ✅. Approximate-first-integral confinement for the exact rational stellarator field ✅ (95 toroidal transits, certified). Pendulum island-width bound with explicit remainder ○. Chirikov non-overlap ○. A posteriori KAM ✅ (verified explicit-constant KAM theorem; exact invariant torus of the rational stellarator field; all-time field-line confinement). Converse KAM / Greene residue as an obstruction certificate ○. | Fourier coefficient enclosures for b_{m,n} | M4/M5 confinement |
| **T8 Guiding centre and kinetics** (microturbulence note) | Guiding-centre equations; finite-time full-orbit versus guiding-centre error (R6) ✅ (crude, constant 1); Boozer GC model, gyro-Noether identity and iterated averaging lemma ✅; rigorous amplitudes for near-axis QA ✅ (passing alphas 0.19 s); trapped: single well and non-resonant bounce sums ✅, kick form ○. Bounce action J_∥ and the ∂_ψ identity (careful endpoint differentiation) ○. Min-B ⇒ max-J (sanity check 1) ✅ (for the integral expression; = ∂J/∂ψ ○). Available-energy kernel lemmas ✅ (note's opposite-sign claim refuted). Integral Â bound under precession dominance ○. Omnigeneity implies zero bounce-averaged radial drift ○. | Quadrature with remainder for bounce integrals (√ endpoint singularity) | Alpha confinement (3.5 MeV obstruction), and χ upper bounds for T3 |
| **T9 Hyperbolic energy** (Stage 6, holomorphic §4) | Elsässer energy and cross-helicity identities ✅ (conservation under skew transport). Null-structure identity ⟨(z∓·∇)z±, z±⟩ = 0 for divergence-free tangent fields ○. Abstract commuted-energy Grönwall theorem in Hilbert space, with the commutator bound as hypothesis ○. Sobolev step stated as an explicit interface (§1.5). | none | Long-time linear bounds, M5 |
| **T10 Exploratory geometry** (holomorphic/KYM/BKM) | Discovery only until vetted: oriented flux periods and Hodge bounds (§1.2, §11.6); Futaki-type obstruction for a *specific* near-axis QS ansatz (an honest test: does it reproduce the Garren–Boozer O(r³) obstruction?); conditional BKM continuation. Each needs a verdict note before any Lean code. | none | Possibly T6/T7 |

---

## 5. Model ladder (each rung proves characteristics under both G1 and G2)

| Rung | Model | G1 characteristics to prove | G2 characteristics to prove | Gate |
| --- | --- | --- | --- | --- |
| **M0** | Exact symmetric equilibria: slab, screw pinch, Solov'ev, helical | Force balance; all-time field-line and orbit confinement; Suydam; Newcomb \|m\| ≤ 6 | none | P3/P4 (idealized) |
| **M1** | 0-D burning D-T plasma at reactor scale (n ≈ 10²⁰ m⁻³, B = 5 T, V ≈ 1000 m³) | none (uses M0's geometry only for the volume) | **Invariant temperature window** [T_lo, T_hi] ⊂ [10, 30] keV for all t ≥ 0, given τ_E ≥ τ* and an auxiliary-power range. Ignition threshold. Burn yield over T_burn. Explicit statement of when thermal runaway is impossible. | first G2 result |
| **M2** | 1-D radial transport on the **exact Solov'ev and helical geometries** (V′(ψ) taken from the M0 fields), with χ ∈ [χ_min, χ_max] supplied | Mercier/ballooning certificates along field lines of the helical and Solov'ev equilibria (T2) | **Lower barrier:** T_core ≥ 10 keV for all time. **Upper barrier:** edge heat flux below a wall limit. Margins against χ uncertainty. Discrete scheme with a verified maximum principle (T5). | P5 local; P6 partial |
| **M3** | Validated (radii-polynomial) toroidal Grad–Shafranov equilibrium with realistic non-polynomial profiles; Newcomb for all m | Existence near the oracle; Mercier; ballooning; nested surfaces | Transport barriers on the validated geometry | P4 (validated) |
| **M4** | Near-axis quasisymmetric stellarator (Garren–Boozer to 2nd order, explicit ε_QS) | Guiding-centre confinement time ∝ 1/ε_QS for 3.5 MeV alphas (closes the 14 Oct obstruction); island widths; max-J on a stated pitch-angle set; Â bound | χ upper bound derived from Â and neoclassical theory (as an explicitly supplied scaling law with stated validity); burn window | P3/P6 for a genuine stellarator class |
| **M5** | Coil-produced 3-D field (filament Biot–Savart, existing) plus a DESC-validated finite-β equilibrium | Boundary-to-interior field error (T1); KAM/islands (T7); ballooning on validated field lines; commuted-energy long-time linear bound (T9) | Transport barriers with geometry from the validated equilibrium | P2 → P5 |
| **M6** | Integrated candidate: coils + equilibrium + stability + transport + engineering margins | One decoded candidate with common witnesses (`Bridge/Contracts`) for all uncertainty states | Burn window robust to every declared uncertainty | P8 |

Physical honesty rule (from domain-libraries.md): every rung is labelled *idealized*, *synthetic data* or *sourced data*. A rung does not claim practical confinement unless its model assumptions are justified.

---

## 6. Cycle schedule

Each cycle is a run. The targets are listed in priority order; anything left over carries to the next cycle.

### Cycle 1: kernel for G2, corrections, quick wins
- **Lane 0:** apply the §1 corrections to the notes. Add `Kernel/Vacuum`, `Kernel/Transport` and `Kernel/Fusion`, with sanity modules.
- **A:** (i) Nagumo/comparison proof for the radial operator, with the exact axis-regularity hypothesis. (ii) 0-D power-balance invariant-window theorem. (iii) The correct toroidal min-B obstruction, from the literature.
- **B:** Elsässer identities; SBP energy identity; available-energy kernel lemmas; Bochner identity and weak maximum principle (T1).
- **C:** Bosch–Hale ⟨σv⟩ rational enclosures on keV windows; extension of the interval checker to rational functions and √ enclosures.
- **D:** M1 instance: an ignition window at reactor parameters.
- **Acceptance:** at least one theorem of the form "T(t) ∈ [T_lo, T_hi] for all t ≥ 0" for a supplied 0-D solution under cited reactivity bounds; T1 boundary-to-interior theorem compiled.

### Cycle 2: radial transport barriers and ballooning (M2)
- **B:** Nagumo and weak comparison in Lean; steady and time-dependent barrier theorems (T3). Ballooning Barta certificate with weight; Sturm necessity (T2).
- **C:** barrier checker; M-matrix/discrete maximum principle checker (T5).
- **D:** compute V′(ψ) exactly for the Solov'ev and helical fields; lower and upper barriers with χ ∈ [χ_min, χ_max]; ballooning and Mercier certificates along their field lines.
- **A:** Newcomb uniform in m (asymptotic argument); relative-entropy identity check (§1.5).
- **Acceptance:** a compiled theorem "every classical solution starting above T_sub stays above T_sub, which is ≥ 10 keV on the core region" for the M2 geometry.

### Cycle 3: guiding centre, near-axis QS, alphas (M4 start)
- **A/B:** guiding-centre reduction error over finite time (R6, restricted smooth regime); bounce action and the ∂_ψ identity; min-B ⇒ max-J; omnigeneity ⇒ zero radial bounce drift.
- **D:** first-order near-axis QS field as an exact analytic field, with an ε_QS defect bound; alpha confinement time.
- **C:** bounce-integral quadrature with remainder.
- **Acceptance:** 3.5 MeV alpha guiding-centre confinement for a stated time in a stated QS model, or a precise obstruction.

### Cycle 4: validated equilibria (M3)
- **B/C:** ℓ¹_ν Banach algebra; radii polynomial for ODE BVPs, then 2-D Grad–Shafranov; tail bounds.
- **D:** a validated toroidal equilibrium with realistic profiles; transport barriers and Mercier on it.
- **B:** abstract commuted-energy Grönwall theorem (T9).

### Cycle 5: 3-D field lines and coils (M5)
- Island-width pendulum bounds with remainder; Chirikov margin; the T1 boundary-to-interior bound applied to the existing coil fixtures; first steps towards a four-coil dataset (VD1).

### Cycle 6 and later: integration (M6) and research problems
- Compose certificates on one candidate. Then target R1/R2/R4/R5 as their prerequisites mature. A T10 exploratory verdict is produced in every cycle in the background.

**Re-planning trigger:** at every audit, if a rung's acceptance criterion failed twice, either downgrade the claim (for example to a finite time, or a restricted mode class) or open a lane-A obstruction study. Do not keep re-running the same approach.

---

## 7. Sub-agent prompt template (lane A or B)

> Use the skill `<skill>`. Context: PlasmaLean at commit `<sha>`; read `notes/implementation-plan.md` §`<track>` and `<source note>`.
> Target: `<precise statement with all hypotheses>`.
> Deliver: `<notes/theory/x.md | PlasmaLean/Theory/X.lean>` only, in namespace `PlasmaLean.<X>`. Do not edit other files.
> Requirements: no `sorry`/`axiom`/`native_decide`; docstrings; at least 3 sanity corollaries (a degenerate case, a special case, a non-vacuity witness); `lake build PlasmaLean.Theory.X` passes.
> If the statement is false, or needs stronger hypotheses, produce a counterexample or the corrected statement instead of forcing a proof.
> Report: declarations, assumptions, what failed, suggested next target.

---

## 8. Definition of done for each cycle

- `lake build` clean; `scripts/check_axioms.lean` reports standard axioms only; no `sorry`/`native_decide`.
- New definitions come with characterizing and degenerate-case theorems. New certificates come with both valid and invalid fixtures.
- Lane E review findings resolved or recorded.
- Progress report `progress/<date>-progress.md`, `status.json`, `slideshow.json`, `README.md` summary; `generate_handbook.mjs` and `check_site.mjs` pass.
- Claims are labelled honestly: a compiled theorem, a synthetic fixture, supplied physical data or planned work, each called by its name.

---

## 9. Progress log

### Phase 1 (Cycle 1), 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-2.md)

- **Done:**
  - Kernel files `Fusion`, `Transport` and `Vacuum`, with sanity modules.
  - T1 Milestone A: Bochner identity, weak maximum principle, boundary-to-interior field-error bound, corrected min/max counterexample.
  - T3: first-crossing lemma and comparison theorems (strict, margin and non-strict versions; lower, upper and two-sided).
  - T4: ODE barriers and burn yield.
  - **M1:** T ≥ 10 keV for all t ≥ 0 at reactor scale, with fuel dilution, P_aux ≥ 40 MW, τ_E ≥ 3.5 s at T ≤ 10 keV; margin +5.5 MW.
  - T5 SBP identity (4-point). T8 available-energy lemmas and min-B ⇒ max-J (integral form). T9 Elsässer identities and conservation.
  - §1 corrections applied to the notes; theory notes in `notes/theory/`.
- **Acceptance (Cycle 1):** met. "T(t) ∈ [T_lo, T_hi] for all t ≥ 0" is proved (`m1_burn_window`), with the upper side under a supplied τ_E-degradation hypothesis. The T1 boundary-to-interior theorem is compiled.
- **Findings that change the plan:**
  - With constant τ_E the 0-D model runs away above 30 keV, so the upper barriers need a confinement-degradation law. Add to T4: derive the τ_E hypotheses from a supplied IPB98(y,2) scaling.
  - The comparison principle needs only D ≥ 0, plus R one-sided Lipschitz for the non-strict version.
  - The relative-entropy identity in the notes is false for non-constant T*.
  - The holonomy idea (T10) is not useful as stated.
- **Carried to Phase 2:**
  - M2 barrier instance on an exact geometry, using a rational barrier checker.
  - Ballooning/Barta and Mercier (T2).
  - M-matrix maximum principle and general-N SBP (T5).
  - C² of filament fields; the toroidal curvature obstruction.
  - IPB98-derived τ_E hypotheses.

### Phase 2 (Cycle 2), 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-3.md)

- **Done:**
  - **M2:** all-time core-temperature barrier (T ≥ 10 keV on ψ ≤ 0.3) in an idealized cylinder, using a degenerate-axis comparison theorem and a 16-piece exact margin certificate.
  - **M1 upgraded:** τ_E hypotheses derived from IPB98(y,2); the nominal-H obstruction and an unstable ignition point are proved; the Bosch–Hale class is shown non-vacuous by a proof-term window certificate.
  - **T2:** Barta ballooning certificate; constant-coefficient iff; cylindrical Mercier ⇔ Suydam; screw-pinch Newcomb stability for **all** modes with m ≠ 0.
  - **T1/T8:** filament fields C^∞; curvature obstruction (no closed vacuum field line with transverse min-B), with a witness.
  - **T5:** M-matrix backward-Euler comparison; SBP for all N.
- **Acceptance (Cycle 2):** met in an idealized cylinder. The plan asked for the "M2 geometry" (Solov'ev/helical); that version is carried to Phase 3.
- **Findings that change the plan:**
  - The kernel's D ≥ D_min > 0 is incompatible with ψ ∝ r² coordinates. Phase 3 relaxes the kernel.
  - At nominal H the 0-D flat-profile model cannot hold 10 keV, so profile peaking matters. That argues for M2-type (1-D) burn results over 0-D ones.
  - ISS04 at the suggested stellarator scale needs H ≈ 1.9 (numerical observation). Stellarator burn needs either a larger device or a better confinement assumption, and this should be explicit in M4.
- **Carried to Phase 3:**
  - Kernel relaxation.
  - M2 on helical geometry with pedestal χ(ψ), and a sharper upper barrier.
  - M3: ℓ¹_ν radii polynomial.
  - M4: guiding centre and near-axis QS.
  - Infinite-line ballooning.

### Phase 3 (Cycle 3), 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-4.md)

- **Done:**
  - **3.5 MeV alphas confined for all time** in a realistically scaled exact Solov'ev equilibrium (any pitch, born in the inner quarter of the flux; 1.5% margin). The 14 October obstruction is closed for this axisymmetric equilibrium.
  - **Transport kernel relaxed** (D ≥ 0, regular or degenerate axis).
  - **Core barrier on the helical equilibrium** (T ≥ 10 keV on s ≤ 0.3, axis pressure consistent).
  - **Stellaris-scale ISS04 burn window,** with the measured-f_ren obstruction proved.
  - ℓ¹_ν, the radii polynomial and a validated nonlinear BVP.
  - Guiding-centre reduction bound, Boozer GC model, gyro-Noether identity, iterated averaging lemma, and 0.8 ms passing-alpha trapping in a near-axis QA model.
  - Infinite-line ballooning (sharp −1/4 tail) and Sturm necessity.
- **Acceptance (Cycle 3):** "3.5 MeV alpha confinement in a stated model, or a precise obstruction" is met, with both. All-time confinement holds in the symmetric equilibrium; for near-QA the result is 0.8 ms together with a quantified obstruction for the linear argument.
- **Findings that change the plan:**
  - Exact symmetry plus a realistic B_pol confines alphas, so near-symmetric confinement now hinges on rigorous iterated averaging.
  - Stellarator burn in 0-D needs f_ren above measured values, so 1-D barriers with profile effects on stellarator geometry are the G2 path.
  - Transport and MHD must be coupled: barrier pressure ≤ equilibrium pressure.
- **Carried to Phase 4:**
  - Interval-bounded iterated averaging for near-axis QA.
  - 1-D Grad–Shafranov validated equilibrium with C² regularity.
  - Transport–MHD consistent profiles.
  - Mercier/ballooning for the Solov'ev and helical equilibria.
  - Coil error fields via the maximum principle.

### Phase 4 (Cycle 4), 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-5.md)

- **Done:**
  - **Passing 3.5 MeV alphas confined 0.11 s** in reactor-scale near-axis QA, 137× the Phase 3 bound, via 3-fold rigorous averaging.
  - **First validated plasma equilibrium:** slab Grad–Shafranov with an exponential profile, classical C², kernel force balance.
  - **Fourier regularity.**
  - **General Mercier index:** helical equilibrium unstable; Solov'ev q ≥ 2.02 proved.
  - **Volume coil-error certificates** from boundary samples.
  - **Coupling design:** a single consistent plasma needs an upper barrier and D(ψ, T).
- **Acceptance:** M3 has a validated plasma equilibrium (slab, not yet toroidal). M4 near-QA passing alphas are within ≈ 4× of slowing down.
- **Findings that change the plan:**
  - The helical equilibrium is MHD-unstable, so the Solov'ev family becomes the primary consistent G1+G2 rung, and stellarator-specific stable geometry must come from near-axis QA / validated 3-D equilibria.
  - The upper barrier needs kernel extension K2.
  - Large certificates must use the proof-term pattern to keep builds fast.
- **Carried to Phase 5:**
  - K2 and `solovev_one_plasma`.
  - Certified Solov'ev Mercier index and ballooning.
  - The build-cost fix.
  - Near-QA beyond 0.11 s and trapped alphas.
  - 2-D Grad–Shafranov validation.

### Phase 5 (Cycle 5), 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-6.md)

- **Done:**
  - **`solovev_one_plasma`:** one Solov'ev field with force balance, all-time 3.5 MeV alpha confinement, a two-sided transport band (T ≥ 10 keV in the core) and pressure ≤ equilibrium + offset. The geometry class is supplied; the parameter set is driven (Q ≈ 5.5).
  - **Kernel K2** (D(ψ, T)) and the cylinder two-sided band.
  - **Certified Mercier stability** of the reactor Solov'ev equilibrium.
  - **Near-QA passing alphas 0.19 s,** with the build cut from 349 s to 59 s by proof-term certificates.
  - **Trapped-alpha lemmas.**
- **Process finding:** one sub-agent report claimed declarations that did not exist. Integration now grep-checks every cited declaration.
- **Carried to Phase 6:**
  - Prove `IsSolovevGeometry` for the actual field (in progress).
  - An ignited one-plasma set.
  - Ballooning on Solov'ev surfaces.
  - The trapped-alpha kick form.
  - 3-D / near-axis validated equilibria.

### Phase 6, 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-7.md)

- **Done:**
  - `solovev_one_plasma_actual`: the transport geometry is proved for the actual Solov'ev field, so only the coarea step is stated.
  - High-Q (Q ≈ 40, 17.5 MW) and ignited (Δ = 90 kPa) one-plasma versions, using fine reactivity windows.
  - Ideal ballooning on four near-axis Solov'ev surfaces (reduction supplied).
  - **First exact stellarator field:** rational vacuum, 2 periods, stellarator-symmetric, elliptic axis.
  - Defect-confinement theorem.
  - Trapped-alpha turning points and kick form for periodic references.
- **Not achieved:** a trapped-alpha confinement time (non-resonance open; a real resonance exists in the band).
- **Carried to Phase 7:**
  - Rational-stellarator certified confinement and its coil approximation.
  - Trapped-alpha non-resonance.
  - Ballooning on all surfaces.
  - The coarea formalization.

### Phase 7 part 1, 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-8.md)

- **Done:**
  - **Certified field-line confinement in an exact non-axisymmetric vacuum stellarator field:** ≥ 95 toroidal transits from a tube of radius ≈ 0.023 R₀ around the axis.
  - **Coarea formalized:** the one-plasma geometry is fully derived; only the transport model, data and solutions are supplied.
- **In progress (part 2):** trapped-alpha non-resonance; ballooning on all surfaces.
- **Next:** a coil approximation within the defect budget; longer confinement (higher order or KAM).

### Phase 7 part 2, 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-9.md)

- **Done:**
  - Ideal ballooning on **every** surface of the reactor Solov'ev equilibrium (axis to edge, reduction supplied), with a 3× faster proof-term certificate.
  - Coil chain for the rational stellarator: a certified TF filament, plus error ⇒ transits through the maximum principle.
  - Trapped-alpha non-resonance and reference periodicity in exact QA.
- **Open:**
  - A certified helical frontier bound (in progress).
  - The trapped-alpha remainder (phase shear).
  - A proof-term rewrite of the trapped cell checks.

### Phase 8, 20 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-20-progress-10.md)

- **Done:**
  - **First finite-β non-axisymmetric toroidal equilibrium:** Landreman family 1, with kernel force balance, a flux function, closed confined field lines, a non-planar axis and a 5 T instance. Zero shear, idealized.
  - **Invariant-torus trapping (K0–K1):** all-time confinement of the rational stellarator field follows from any invariant radial-graph torus.
- **In progress:** K2 (validated approximate torus); a certified helical coil set.
- **Long pole:** K3, an explicit-constant KAM theorem.

### Phase 9 part 1, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress.md)

- **Done:**
  - **K2:** a validated approximate invariant torus of the rational stellarator field, with residual ≤ 1.2×10⁻²³, proved to be a radial graph around the axis.
  - **K3a:** the Diophantine certificate (γ = 0.1374) and the cohomological equation with explicit estimates.
- **In progress (K3b):** weighted error, frame and twist, the sequence lemma, and ℓ¹(ℤ²).
- **Remaining (K3c):** Newton step and limit.

### Phase 9 part 2, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-2.md)

- **Done:**
  - **First coil-produced stellarator field with certified confinement:** 1 transit, polygonal filaments, zero margin.
  - **KAM sequence and limit lemmas;** the ℓ¹(ℤ²) Banach algebra; composition and inverse bounds.
- **Remaining for all-time confinement:**
  - Weighted error and frame/twist (in progress).
  - The flux-average lemma.
  - The Newton step and the limit.

### Phase 9 part 3, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-3.md)

- **Done:**
  - All quantitative KAM inputs for torus A: the weighted error at r = 0.1257, frame bounds, and twist ≥ 3/10.
  - Landreman family 2 with proved shear.
- **In progress:** K3d, the Newton step, limit and all-time confinement.

### Phase 9 part 4, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-4.md)

- **Negative finding:**
  - Landreman family 1 is Mercier-unstable on every surface (proved).
  - Family 2 is Mercier-unstable numerically (conditional theorem).
- **Plan change:** a stable finite-β stellarator rung must come from the stepped-pressure-on-KAM-torus route, or from stable parameter regions.

### Phase 10, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-5.md)

- **Done: all-time field-line confinement in an exact non-axisymmetric stellarator field**, via a verified explicit-constant KAM theorem (smallness margin ≈ 900). Independently reviewed: sound.
- **Remaining caveats:** field-line existence is assumed; the field is the vacuum model.
- **Next:**
  - Coil-produced all-time confinement.
  - Field-line existence.
  - Stepped-pressure finite β across the exact torus.
  - Particle confinement.

### Phase 10 addendum, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-6.md)

- Field-line existence proved: the all-time confinement theorem (`rationalStellarator_confined_forever_exists`) has no remaining hypotheses.

### Infrastructure, 21 October 2026

- **Generic KAM:** the KAM Newton step and iteration now take an abstract `FlowField` (`Design/KamFlow*`). The field(1/4) results are re-derived as an instance, and the regression theorems are byte-for-byte unchanged.
- **Guiding centres:** the Littlejohn equations are supplied as a model (`Theory/Kinetic/GuidingCentreLittlejohn`). For μ = 0, guiding-centre orbits are reparametrized field lines of the divergence-free field B + ρ_s∇×b, and confinement transfers to them.
- **Next (from `notes/theory/after-kam.md`):** KAM for the guiding-centre field, aiming at all-time confinement of passing alphas in the exact stellarator field. After that, coil-produced KAM confinement.

### Coil certificate and GC groundwork, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-7.md)

- **Coil-produced field:** confinement certified for **52 transits** (cubic interpolation certificate; reviewed sound).
- **Groundwork:** generic KAM `FlowField`; Littlejohn guiding-centre transfer; inverse-square-root expressions.
- **In progress:** guiding-centre KAM.

### Guiding-centre torus and coil-KAM status, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-8.md)

- **Exact invariant torus of the guiding-centre field** for 3.5 MeV alphas at B₀R₀ ≈ 69 T·m (smallness margin ≈ 1470). The trapping and alpha corollary are in progress.
- **Coil-produced all-time confinement is blocked:** the certified residual is ≈ 10⁹ vs ≈ 10⁻³⁰ needed. This is paused as research.

### Alpha guiding centres, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-9.md)

- **Done:** all-time confinement of passing 3.5 MeV alpha guiding centres (μ = 0, v_∥ > 0, B₀R₀ ≈ 69 T·m, Littlejohn model) in the exact stellarator field. Reviewed: sound. This is a measure-zero set of alphas.
- **Next:** a parameter family over ρ_s (robustness in energy and B₀R₀); v_∥ < 0; μ > 0.

### Both signs of v∥, and μ > 0 identity, 21 October 2026

- **`alpha_gc_confined_forever_pm`:** passing μ = 0 alpha guiding centres are confined for all time for **both** signs of v∥ at B₀R₀ ≈ 69 T·m. Each sign has its own torus: ι_A for v∥ > 0, ι_B = (161−√5)/1178 for v∥ < 0.
- **`GuidingCentrePassing`:** for μ > 0, passing orbits are field lines of B + ∇×(ρ_{E,μ}b), with the grad-B drift absorbed exactly. The KAM torus for this field is not yet done.
- **In progress:** a Chebyshev-in-ρ family certificate for an interval of B₀R₀.

## 10. Phases after Phase 10 (plan of record, 21 October 2026)

> **Historical plan of record.** Kept as written on 21 October 2026; the open problems it lists are now tracked as goals and questions in the Research graph (G-4–G-6, G-9, Q-1–Q-6, Q-12).

- **Phase 11, robust alpha confinement (in progress):**
  - a Chebyshev-in-ρ torus family over an interval of B₀R₀, then over all energies 0–3.5 MeV;
  - μ > 0 passing particles (the field-line identity is done; the KAM torus is pending).
  - Heavy certificates (several CPU-hours) are kept out of the default build and checked on demand.
- **Phase 12, trapped particles:** finite-time and adiabatic-invariant (J) bounds for trapped alphas; the per-bounce remainder (phase shear) is open.
- **Phase 13, coil-produced all-time confinement (research):** sharp complex coil bounds with filament cancellation, a torus-adapted neighbourhood and anisotropic strips; more certified transits meanwhile.
- **Phase 14, a stable finite-β stellarator:**
  - route B: validated search for Mercier-stable regions of the Landreman families;
  - route A: stepped pressure across the exact KAM torus.
- **Phase 15, workstation offload (infrastructure):** heavy numerics and first builds of large certificates run on a workstation through `scripts/workstation/run.sh` (see `Workstation.md`); results are pushed to a `workstation/*` branch, then pulled and re-checked on the laptop with `--verify-only`.
  - **Constraint:** the merged Lean must build on the laptop: ≤ 6 GB per process; ≤ 60 CPU-min for the default build, ≤ 240 CPU-min for an on-demand top module. The workstation's job is to find *smaller* certificates, not bigger proofs.
  - **Convention:** after each phase, update the workstation tasks (`scripts/workstation/tasks/`) if the phase added or changed heavy numerics or certificates.
  - **Workstation state (25 October 2026):** Lean, the Mathlib cache and the library build are set up by hand; `run.sh` only installs the Python packages.
  - **Tasks to register:** the energy-window (ρ, λ) family (±3 eV, then ±1%), the family-2 ballooning certificate (3-D function over surface × ℝ), wider λ cells, and the coil-KAM refinement.
- **Phase 16, proof-term certificates (infrastructure):** replace every `decide +kernel` (≈ 28,700 uses in 813 files) by proof terms built as in `PlasmaLean/SubsetSum.lean`: inductive certificate predicates whose constructors are local steps, soundness by induction, `meta` builders, leaves that are kernel `Nat` facts (GMP) closed by `Eq.refl` built directly (no elaborator evaluation). Order: KAM-family Kronecker checks (bulk of the uses) → Maj/Adm and chain glue → coil, ballooning and trapped-orbit cells → `QPoly.checkOn` fixtures. Budget: no regression in peak memory (≤ 6 GB) and at most modest CPU growth; generators updated with each family.
- **Later:** the integrated stellarator candidate (M6) and engineering constraints.

### Phase 11 part 1, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-10.md)

- **Done:**
  - Alpha guiding centres (μ = 0) confined forever for every B₀R₀ ∈ [67.95, 69.99] T·m (a positive-measure range), reviewed sound.
  - Both signs of v∥.
  - The μ > 0 passing identity.
  - Trapped-alpha bounce period and reference orbits.
- **Negative:** the re-anchored trapped-alpha bound cannot close with absolute amplitudes.

### Phase 14 route B, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-11.md)

- **Done:** a Mercier-stable band (k ∈ [0.7, 0.9]) of Landreman family 2 at λ = 200 (low β); reviewed sound.
- **Caveat:** the flux labels and area element are hand-derived (change of variables unformalized).
- **Trapped alphas:** kick bound 0.0816; the long-time result is parked as research.

### Phase 11 part 2, 21 October 2026 — [report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-21-progress-12.md)

- **Done:**
  - μ > 0 passing alpha guiding centres confined forever for pitch angles with λ ∈ [0, 1/16] (positive measure in pitch angle; one energy and B₀R₀); reviewed sound.
  - Family-2 Mercier labels derived from the field; shear and hill certified.
- **Next:** a wider λ range, energies below 3.5 MeV and a joint B₀R₀ range, toward positive measure in 3-D velocity space.

### Positive measure in 3-D velocity space (technicality), 21 October 2026

- **`alpha_gc_confined_forever_velocity_set`:** all-time confinement for a set of initial velocities of positive Lebesgue measure in ℝ³: pitch angles λ ∈ [0, 1/16], v∥ > 0, and energies in [(1 − 2⁻⁷⁸)²K, K].
- **Caveat:** the energy window has relative width ≈ 7×10⁻²⁴ (≈ 2×10⁻¹⁷ eV), so this is a technicality, not physical robustness.
- **Physically meaningful widths** need a genuine 2-D (ρ, λ) Chebyshev family: ≈ 3 CPU-hours for ±3 eV, ≈ 10 CPU-hours for ±1%, plus new evaluate-and-interpolate infrastructure (`notes/theory/gc-kam-status.md` §8).

### Phase 14 route B: ballooning on the family-2 band, 25 October 2026

- **Done (infrastructure):** a general 3-D surface ballooning framework (`Theory/Stability/BallooningSurface.lean`: transported eikonal family, completeness over all θ_k, surface-certificate ⇒ energy ≥ 0) and its instantiation on family 2 with line data built from the actual field (`family2_stable_of_cert`: stability of every line and θ_k reduces to one pointwise inequality on surface × ℝ). Ballooning reduction supplied.
- **Numerics (untrusted):** ballooning-stable on k = 0.70–0.90 at the physical pressure and at twice it; the limiting long-line tail goes unstable only at pressure × 2.36 (k = 0.70) to × 9.39 (k = 0.90), marginal at k ≈ 0.54, consistent with the Mercier threshold k_c ≈ 0.53.
- **Open:** the certificate itself. Certificates linear in the secular variable fail numerically; a working one needs a 3-D function resolving the sharp tip structure of |∇ψ| and a large interval cover.

### Phase 15: workstation pipeline, 25 October 2026

- **Done:** `scripts/workstation/run.sh` (setup: elan, Mathlib cache, Python venv from `scripts/requirements.txt`, `lake build PlasmaLean`; per task: numerics → Lean emission → per-module build with wall/CPU/peak-memory measurement → axiom check → results and laptop verdict in `workstation/results/<task>/<stamp>/` → commit and push to `workstation/<tasks>-<stamp>`), a `--verify-only` laptop mode, a task template and a `smoke` task. Instructions in `Workstation.md`. Tested locally (verify mode, and the full git path in a throwaway clone).
- **Next:** register the energy-window and family-2 ballooning tasks, and run `smoke` on the workstation.

### Phase 11: energy window (genuine energy × pitch family), 25 October 2026

- **Done:** `alpha_gc_confined_forever_energy_window`: at the fixed design B₀R₀, every passing alpha guiding centre with |E − 3.5 MeV| ≤ 0.4 eV and λ ∈ [0, 1/16], starting on the axis or inside the torus, stays inside and passing for all time (Littlejohn model, vacuum model field). `alphaEwVel_volume_pos` gives the positive-measure velocity set (energy relative width ≈ 1.2e-7, 3×10¹⁶ times wider than the frozen-torus box). Method: λ-families certified at four ρ nodes, kernel-checked combination norms, and interpolation in ρ with a Cauchy remainder (`Theory/KAM/ParamInterp.lean`, in the default build).
- **Build:** on-demand top module `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily` (343 modules, ≈ 70 CPU-min; axioms in `scripts/check_axioms_heavy.lean`). **Over the laptop memory target:** 36 node check modules peak at 6–8.8 GB per process (the existing `…MuCheckH*` peak at 6.9 GB the same way); it builds here only one module at a time.
- **±3 eV not reached:** the torus family moves ≈ 30·Δρ; wider windows need the low-resolution chain re-certified with larger admissibility balls and new window constants. This is the workstation route (`scripts/workstation/tasks/energy-window.sh`, currently fixed at EW_DELTA = 0.4), with the goal of smaller-memory check modules.

### Phase 11: second pitch cell, 25 October 2026

- **Done:** the pitch cell λ ∈ [1/16, 1/8] (`Mu2.rationalStellarator_gc_mu_confined_forever`) and `alpha_gc_passing_confined_forever_wide`: passing alpha guiding centres with μ ∈ [0, E/(8B₀)] (λ ∈ [0, 1/8]) are confined forever (one energy and B₀R₀; staying passing is proved, λ|B| ≤ 3/8). Chebyshev degree 12, e₀ = 5.3e-21, KAM smallness 0.158.
- **Build:** on-demand top module `lake build PlasmaLean.Design.RationalStellaratorGCMuWide` (97 modules, 31 CPU-min; axioms in `scripts/check_axioms_heavy.lean`). 10 check modules peak above 6 GB (7.8 GB max).
- **Correction:** the cell [0, 1/16] already in the default build peaks at 8.8 GB (`RationalStellaratorGCMuCheckH1`), not the 5.5 GB recorded earlier, so the default build itself exceeds the 6 GB laptop target; it still builds here one module at a time. Reducing kernel-check memory (smaller digit-sum blocks do not help; see gc-kam-status §9–§10) is an open infrastructure item.
- **Workstation task:** `scripts/workstation/tasks/lambda-cell.sh` (LAM_LO, LAM_HI, LAM_TAG); cells ending above 1/8 need a higher Chebyshev degree, and λ ≤ 1/4 is required by the passing argument.

### Phase 14 route B: ballooning certificate search, 25 October 2026

- **Done (Lean, default build):** the exact secular part of the ballooning certificate. `BallooningSecular.jpar_transport` (B·∇J∥ = 2μ⟪B×∇ψ,κ⟫/|B|² for a general 3-D equilibrium) and `eikLine_stable_of_secularCert`: with Φ = (c₀ − J∥)s + F, stability follows from a condition free of the secular drive; family-2 instance `family2_stable_of_secular_cert` with J∥ in closed form. Exactness is necessary: s → ±∞ forces the s-coefficient to satisfy B·∇a = q₁ exactly.
- **Search (untrusted):** B-spline × rational-in-s certificate, SOCP (Clarabel) with active-set rounds. The s → ∞ condition is feasible with margin (k = 0.7 and 0.9); the full problem at k = 0.9 fails the dense check at laptop resolution, and whether the basis can work is open.
- **Cost estimate:** one surface 10–20 CPU-h and 30–60 GB per solve; the band 100–200 CPU-h. The Lean kernel checker (not written; ≈ 8,000 boxes per surface) would be 2–11 CPU-h per surface, beyond the laptop budget for a band. Workstation task `family2-ballooning.sh` runs the search and emits data only; it produces no theorem until the checker exists.

### Phase 11: pitch cells beyond 1/8, 25 October 2026

- **Workstation run [1/8, 3/16] failed** in the numerics (`node invalid`): `lam_maj.py` bounded the three inverse-square-root nodes by one uniform g, which needs g²(1 − λ₁·mQQ·g²) ≥ 1, impossible for λ₁ > 1/(4·mQQ) ≈ 0.157. An artifact of the bound, not of the field.
- **Fix:** per-node majorants (`Theory/KAM/PolyExprSMajQG.lean`, default build; `scripts/gc_kam/lamcell/maj_g.py`); only λ₁·mQQ·gE·gE4 < 1 is needed (0.47 at λ₁ = 1/4). The cheap node check passes for [1/8, 3/16] and [3/16, 1/4] (C₂ = 1.11e11 and 1.42e11, vs 9.67e10 for the certified cell). `lambda-cell.sh` now uses it, with a fail-fast check.

### Infrastructure: low-memory kernel checks, 25 October 2026

- **Diagnosis:** the KAM-family check modules' memory is in the kernel (whnf caches keep every intermediate big number until the declaration is checked), not elaboration (0.7 GB) or literals.
- **Fix:** sign–magnitude integers, per-row masks placed by divide and conquer, row block sums by two multiplications (`Certificates/KronLowMemCompute.lean`, `KronBallLowMem.lean`; emitter `scripts/gc_kam/lowmem/lowmem_emit.py`). The bridge lemmas re-prove the original statements, so chains and theorems are unchanged.
- **Migrated:** Mu, Mu2, Ew1–4 and Fam families. Peak per process **8.8 → 4.3 GB** (default build and on-demand modules alike); check CPU ≈ halved (Mu H 554 → 329 s, Ew H 2596 → 1437 s). The 6 GB laptop target now holds everywhere. `energy-window.sh` and `lambda-cell.sh` emit the new format.
- **Open:** the checks still use `decide +kernel` (one kernel evaluation per check). Proof terms with `rfl` leaves would put 12–24 MB intermediates into the oleans; `Nat.le_of_ble_eq_true rfl` doubles time and memory (elaborator evaluation). Policy decision pending.

### Phase 11: third pitch cell, 25 October 2026

- **Generator bug found and fixed:** `lam_emit_kam.py` substituted template literals one after another, so a new value equal to a later template literal was replaced again (Mu3: az0 = 1629/10⁴ became 1623/10⁴, a false bound in `Mu3Adm`). Now one regex pass with digit boundaries, and `scripts/gc_kam/lamcell/validate.py` checks every emitted bound and constant in exact arithmetic against the emitted Lean lists before writing. The generated Adm bound facts use `decide_cbv` (no `decide +kernel`).
- **Done:** the cell λ ∈ [1/8, 3/16] (`Mu3.rationalStellarator_gc_mu_confined_forever`), reproduced and built on the laptop in the low-memory format (peak 4.4 GB). On-demand; a combined [0, 3/16] theorem (like `MuWide`) is still to be written.

### Phase 16: Kronecker ball checks as proof terms (prototype), 25 October 2026

- **Done (default build):** `Certificates/KronProof.lean`: certificate predicates `SCert` (signed image: atoms with their sign as a kernel fact, equal/opposite-sign sums with `Nat.ble m₂ m₁` leaves, negation, difference, product, shift, constant multiple, the `evS` tree steps with `ExN.sgn` leaves; magnitudes are expressions over the data `def`s, never literals) and `PCert` (digit reading split into halves down to blocks of 2^9 rows whose sums are `Eq.refl` kernel facts with small literals); `SCert.sound`, `PCert.sound`, `chebKV_le_of_cert` (gSel leaf, final `Nat.ble tot Kb`). Tactics `kron_proof` (meta witness: signs, comparisons, block sums; raw `mkAppN` terms, no elaborator evaluation) and `kron_lt` (ℓ¹ checks). Prototype `Design/RationalStellaratorGCMuCheckPH1.lean`: the same statements as `…MuCheckH1` (namespace `ProofTerm`), standard axioms.
- **Measured (old `decide +kernel` → proof term):** MuCheckH1 5.9 → 8.5 s CPU, 4.26 → 4.31 GB, private olean 3.6 → 34 KB; MuCheckH14 3.1 → 4.3 s, 2.29 → 2.38 GB; MuCheckH64 15.0 → 17.2 s, 2.76 → 2.87 GB, 8.9 → 119 KB. Kernel time is unchanged; the extra is the meta witness (≈ 0.5× the kernel time: the image products must be evaluated once more) and ≈ 0.1 s of imports. Splitting a check over several declarations cannot lower the peak: ≈ 80% of it is the signed image `Nv`, which every part would need (no literals allowed).
- **Migration per family** (emitter `scripts/gc_kam/proofterm/proofterm_emit.py`, statements unchanged so bridges and chains are untouched): (1) `proofterm_emit.py PRE TAG --only K` writes `<PRE>CheckP<TAG>K` side by side, measure; (2) `proofterm_emit.py PRE TAG --inplace` rewrites `<PRE>Check<TAG>*`; (3) build the check modules one at a time, then `<PRE>LowMem<TAG>`, the chain and the axiom audit. Cost ≈ 1.15–1.45× the current check CPU (Mu H ≈ 330 → ≈ 430 s), oleans +≈ 25 KB per node/centre check. Not yet covered: the bridges' `nodeDims3N` side conditions (`by decide +kernel`, small), and families still in the old `nodeK`/`centerK` format (Torus, NegTorus: run `lowmem_emit.py` first).

### Phase 16: split between laptop and workstation, 25 October 2026

- **Laptop:** the default-build families (Mu, Fam) and the bridges; new certificate designs for the remaining `decide +kernel` families (coil, ballooning and trapped-orbit cells, Torus/NegTorus, `QPoly.checkOn` fixtures).
- **Workstation:** the on-demand families (Ew1–4, Mu2, Mu3; ≈ 75% of the rewritten modules) via the task `proofterm-migrate`. The review spot-checks on-demand results (measurements, axioms, grep, a sample of modules built on the laptop) instead of rebuilding them in full; the full laptop build is deferred until needed (user decision).
- **Migrated, 25 October 2026 (default build):** Mu (H, L) and Fam (H, L): check modules (`kron_proof`/`kron_lt`), bridges and chains (`kernel_fact`, `Certificates/KernelFact.lean`). Check CPU Mu 497 → 667 s, Fam 304 → 440 s; peak Mu 4.25 → 4.31 GB, Fam 3.96 → 4.06 GB; bridges and chains Mu 80 → 94 s, Fam 57 → 68 s; standard axioms for `alpha_gc_passing_confined_forever` and `alpha_gc_confined_forever_robust`. The prototype `…MuCheckPH1` is removed. On-demand families (Ew1–4, Mu2, Mu3) go through the workstation task `proofterm-migrate.sh` (`PT_FAMILIES`); new cells from `lambda-cell.sh` and `energy-window.sh` are emitted as proof terms directly. Still `decide +kernel` in Mu/Fam: the Rel, Env, Out, Adm, Maj and Forever modules (568 uses).

### Phase 11: fourth pitch cell (workstation), 25 October 2026

- **Done:** λ ∈ [3/16, 7/32] (`Mu4.rationalStellarator_gc_mu_confined_forever`), computed and built on the workstation (24 CPU-min, peak 4.1 GB), merged after a laptop spot check. The full cell [3/16, 1/4] had failed KAM smallness (2.64); the half-width cell passes. Pitch cells now cover λ ∈ [0, 7/32] in four on-demand pieces; a combined theorem (like `MuWide`) is still to be written. Mu4 is in the legacy low-memory format and is queued for `proofterm-migrate`.

### Phase 11: fifth pitch cell (workstation), 25 October 2026

- **Done:** λ ∈ [7/32, 1/4] (`Mu5.rationalStellarator_gc_mu_confined_forever`), workstation (24 CPU-min, peak 4.1 GB), spot-checked on the laptop. The five on-demand cells Mu, Mu2–Mu5 now cover λ ∈ [0, 1/4], the limit of the passing argument (λ|B| < 1 on the tube). **Next:** a combined theorem over λ ∈ [0, 1/4] (extending `MuWide`), and proof-term migration of Mu4 and Mu5.

### Phase 16: default build, second stage, 25 October 2026

- **Done:** Mu/Fam auxiliary modules (568 uses, `kernel_fact`), Torus/NegTorus (4,356 uses; new `Certificates/KronProof2D.lean` with `kron2_proof` and the `PCert2` digit-reading certificate for the older `nodeK`/`centerK` format), and 28 smaller default-build modules. Default build: 9,079 → 3,961 `decide +kernel`; CPU ≈ 1.0×, peak ≤ 5.8 GB; all main theorems on standard axioms. Generators updated.
- **Not yet in the spirit of the policy:** many `kernel_fact` leaves are still one big `Eq.refl` on a whole Boolean checker or ℚ value (`Ex.allV … = true`, `farAll … = true`, `l1Kron` in the Star checks). They are not `decide`, but are as opaque as it. Each needs a per-checker certificate predicate (SubsetSum pattern), as for `SCert`/`PCert`.
- **Remaining default-build families:** BallooningCells, PolygonCoil lines/cells, NearAxisQA oscillation rows, Landreman Cert*, ValidatedBVP/Slab (need `∀ x ∈ Finset`), NearAxisQAAveraged and LandremanFamily2MercierStable (memory already near or above 6 GB).

### Phase 16: third stage (opaque leaves, coil cells), 25 October 2026

- **New certificate modules (default build):** `Certificates/BoolCert.lean` (`BCert b v`: one constructor per local step of a Boolean checker: `&&`/`||`/`!`, `if`/`bif` branches with the certificate of the condition, `decide (p ∧ q)`/`decide (p ∨ q)`, and comparison leaves; `BCert.sound` by induction; tactic `bool_cert`, which unfolds the checker one definition or matcher at a time, so its recursion over cells/rows/elements becomes one `and_tt` step per item; `bool_cert?` also checks every leaf in `meta` code and counts leaves and *collapsed* leaves) and `Certificates/DigitSumCert.lean` (`DCert`: the divide-and-conquer digit reading of `l1Kron`, halves as expressions over the stated image, blocks of `2^9` digits as kernel facts; tactic `l1kron_cert`). KronProof, KronProof2D and KernelFact are unchanged.
- **Converted:** PolygonCoil cubic cells (`PolygonCoilCubicCells0–3`, 676 rows + 24 side conditions, `decide +kernel` → `bool_cert`/`kernel_fact`; CPU 99 → 95 s, peak 2.2 GB unchanged; `cubic_emit.py` updated); the `Ex.allV` leaves of the Mu/Fam Rel modules (306, `lam_emit_lean.py`/`fam_emit_lean.py` updated; CPU unchanged); the Boolean-checker leaves of 14 modules (`pieceCheck*`, `QPoly.checkOn`, `signCheck`, `farAll`, `dataOK`, `vertFar`, BoschHale windows, fixtures; ≈ 100 uses, CPU 0.95–1.4×); the `l1Kron` checks of the GC Star checks (4, CPU 12.5 → 20.2 s and 10.5 → 16.6 s: the witness needs the image once more in `meta` code). Default build `decide +kernel`: 3,961 → 3,269.
- **Open:** checkers whose comparison leaves still contain a whole ball or polynomial evaluation (Ballooning `cornerOK`/`hessOK`, Landreman `signCheck`/`cellCheck`, NearAxisQA `legAOk`, PolygonCoil `lineOut4 … = data`): they need a per-term evaluation certificate (one constructor per node of the term tree, intermediate balls as literals or shared expressions, one ball operation per leaf), not yet written; the Kronecker-image equalities `Kv… = famPack…` of the chains; `fieldAP_fixture` (an `Option` computation).

### Phase 16: fourth stage (evaluation certificates), 26 October 2026

- **New:** `Certificates/EvalCert.lean`: `ECert e v` ("the closed term `e` evaluates to the value `v`"), one constructor per node of the term tree: `lit`; operation nodes `op₁`/`op₂`/`op₃` (children certified, then one kernel leaf `f v₁ … vₖ = v` on values, e.g. the outward-rounded ball sum of two balls), `leaf`/`arg` for other arities, `unfold` (`eq_def` of a recursive definition: cell sums, Horner/list recursion), `ite_t/f`, `dite_t/f` (only the branch taken). `ECert.sound` by induction; with a checker's soundness theorem the certificate gives the per-cell inequality. Tactic `eval_cert [f₁, …]` (extra leaf operations); `Certificates/EvalCertFIv.lean`: `fiv_cert` with the `FIv` operations as leaves. Intermediate values are shared: every evaluated subterm is entered once in a table (value + certificate), so it is one node of the proof DAG and is checked once by the kernel (prefix sums reused by the next cell, cell records read for several fields). Fixtures accepted/false/rejected; standard axioms (none).
- **Builder compiled to native code:** the `meta` builder is in `PlasmaLeanMeta/EvalCert.lean`, a new library `PlasmaLeanMeta` with `precompileModules = true` (`lakefile.toml`; depends only on Lean; lake builds its dylib and loads it for importing modules). Interpreted, the builder cost as much as the kernel check (osc leg check: 3.2 s builder + 4.2 s kernel vs 4.5 s for `decide +kernel`); compiled, 0.3 s. Leaf values come from an untrusted fast path (Lean integer arithmetic, a native mirror of the `isqrtAux` Newton iterations), else the kernel's `whnf`.
- **Converted (default build):** NearAxisQA oscillation final checks `finalOk` (16 `…TrappedOscRows*` modules) and the Landreman final combinations `cellCheckOf` (7 `…Cert*` modules): 158 `decide +kernel` → `fiv_cert` (≈ 300 nodes each). Rows05 CPU 79.7 → 81.0 s, peak 3.25 → 3.11 GB, private olean 0.10 → 0.79 MB; Cert1 205 → 203 s, 4.23 → 4.08 GB. Generator `scripts/trapped_reanchor/osc_gen.py` updated (the Landreman cert modules have no generator in `scripts/`). Default build `decide +kernel`: 3,269 → 3,111 (overall, lines: 18,560 → 18,402).
- **Main obstacle: certificate size.** The certificate has one node per operation, ≈ 300–400 bytes per node in the `.olean`. Measured: osc leg check `legAOk` (65k nodes, 40k leaves): CPU 80 → 112 s (1.4×) and peak 3.3 → 5.5 GB per module are within budget, but the private olean grows from 0.1 MB to **340 MB per module** (25 checks); Ballooning `cornerOK` 10k nodes, 3.1 MB per check (≈ 300 MB per Cells module). So leg checks, `oneD`/`outerArc` quadratures, Ballooning cells, PolygonCoil lines and `pieceCheck*` were **not** converted. Coarser leaves (a cell function such as `bottomCellO` as one leaf) were tried and are worse: the leaf's value then needs the kernel's `whnf` on a whole cell and the build did not finish in 12 min.
- **Open:** (1) a decision on olean size vs leaf granularity (ball operation per leaf = hundreds of MB for the heavy groups; per-cell leaves need a value oracle that does not go through `whnf`, e.g. per-checker native mirrors); (2) `ℚ` values (`Rat.mk'` with proof fields) for the `pieceCheck*` band checks and `QPoly`; (3) the Kronecker-image equalities and ValidatedBVP/Slab (not started).

### Phase 16: decision on heavy evaluation certificates, 26 October 2026

- **User decision:** the heaviest remaining checks (near-axis leg checks, Solov'ev ballooning cells, polygon-coil lines, band piece checks) become fully explicit evaluation certificates (`ECert`, one node per ball operation), accepting private oleans of ≈ 300–340 MB per module (≈ 10–15 GB of local build files; not in git, not loaded by importers) and ≈ 1.4× build CPU. No `decide +kernel` exception.

### Phase 16: fifth stage (heavy evaluation certificates), 26 October 2026

- **Builder (`PlasmaLeanMeta/EvalCert.lean`, new functions only):** `ℚ` values in normal form (`mkRatVal`: `Rat.mk' n d` with the proof fields `Nat.succ_ne_zero (d-1)` and `Eq.refl 1`, i.e. one kernel `Nat.gcd` per value), `readRat?`, and the untrusted fast path `fastQ?` (numerals, `OfScientific` literals, casts, `+ - * / ⁻¹`, `^ n`, `max`/`min`, comparisons on `ℚ`); `Inv.inv` and `OfScientific.ofScientific` are leaf operations; constructor nodes no longer evaluate proof fields (they were evaluated before, which failed on `Rat.mk'`). Without the fast path a `QPoly.checkOn` fixture timed out in `whnf`; with it, 7.6k nodes in 1.6 s.
- **New module** `Design/SolovevBallooningEvalCert.lean`: `bl_cert` (`eval_cert` with the `Bl` ball operations as leaves), fixtures accepted/rejected.
- **Converted (all `decide +kernel` → `ECert`, one node per ball/interval/rational operation; zero warnings):**
  - NearAxisQA oscillation legs `legAOk`/`legBOk` (262 uses in `…TrappedOscRows01–16`, `fiv_cert`) and the 5 fixtures of `…TrappedOscCells`; `osc_gen.py` updated. CPU per module ≈ 80 → 100–118 s (1,753 s in total for the 16 modules, uncontended runs), peak 3.1 → 5.2–5.4 GB, private olean 0.8 → 300–314 MB per module (4.87 GB in total). `osc_cover`: `propext`; `reference_kick_osc`: standard axioms.
  - Solov'ev ballooning corner tests `cornerOK` (1,413 uses in `SolovevBallooningCells00–15`, `bl_cert`, ≈ 6.9k nodes per corner); `solovev_ballooning_oracle.py` updated. Cells00 13 → 35 s, 0.97 → 2.46 GB; all 16 modules 781 s, peak ≤ 3.45 GB, private olean 1.4 MB → 3.64 GB in total (140–266 MB per module). `cover_all`: `propext`; `reactor_ballooning_all`: standard axioms.
  - Solov'ev band `pieceCheckL` / `QPoly.checkOn` / label checks (39 `bool_cert` → `eval_cert` in `SolovevBand`, `…HighQ`, `…Ignited`): CPU 30 → 46 s, 56 → 91 s, 52 → 95 s; peak 2.6 → 3.0, 3.5 → 4.6, 3.6 → 4.8 GB; private olean 4.8 → 108, 5.5 → 191, 3.3 → 212 MB. Main theorems on standard axioms.
  - **Disk:** ≈ 9.0 GB of new private oleans (`.lake/build/lib/lean/PlasmaLean/Design` is now 11 GB).
- **Not converted: PolygonCoil lines (`lineOut4 … = data`).** One grid line is 1.18·10⁶ nodes (7.8·10⁵ leaves; mostly `Nat.mul`/`Nat.add` of the Biot–Savart vertex sums and the `sqrtUpFrom` Newton steps): 268 s CPU and 5.9 GB peak for one line, ≈ 400 MB of olean. For the 690 lines that is ≈ 50 CPU-hours and ≈ 280 GB, and a module of more than one line would exceed 6 GB. Files and `cubic_emit.py` are unchanged (still `decide +kernel`). This needs a different certificate (e.g. per-vertex records as data with local leaves, or a per-corner leaf with a native value mirror), not finer splitting.
- **Counts (lines containing `decide +kernel`, HEAD → now):** default build 3,093 → 1,407; overall 7,359 → 5,673.
- **Open:** (1) PolygonCoil lines (above); (2) `ballooning_cover` still closes `hessOK` by one `Eq.refl` per box (opaque, though not `decide +kernel`), as do `box_accepted`/`axisOK_needs_positive` (`kernel_fact`); (3) the `QPoly.checkOn` fixtures in `Certificates/PolyInterval`, `Theory/Stability/Ballooning*`, `ScrewPinchModes`, `LandremanFamily2` can now use `eval_cert` (ℚ supported), but changing `PolyInterval` rebuilds much of the default build; (4) Kronecker-image equalities `Kv… = famPack…` and ValidatedBVP/ValidatedSlabData (`∀ x ∈ Finset`, `Finset.sum` inside the definitions: the builder needs `Finset`/`Multiset` (quotient) support or list-form restatements): not started; (5) the module docstring of `Certificates/EvalCert.lean` still says the leg checks are left to `decide +kernel` (not edited, to avoid rebuilding every `eval_cert` module); (6) the builder change rebuilds every `eval_cert`/`fiv_cert` module once, including the Landreman `…Cert*` modules (≈ 200 s each), not rebuilt here.

### Phase 11: all pitch angles up to λ = 1/4, 26 October 2026

- **Done:** `alpha_gc_passing_confined_forever_quarter` (on-demand `RationalStellaratorGCMuQuarter`): passing alpha guiding centres with μ ∈ [0, E/(4B₀)] (λ ∈ [0, 1/4]) are confined for all time, at one energy and B₀R₀ (Littlejohn model, vacuum model field). Combines the five cells Mu–Mu5; staying passing is proved (`quarter_passing_margin`: λ|B| ≤ 3/4). λ = 1/4 is the limit of the current passing argument with the bound |B| ≤ 3B₀. Built on the laptop from Mu2–Mu5 compiled on the workstation and copied with `oleans.py` (first cross-platform use).

### Phase 16: sixth stage (per-segment line certificates, small checks), 26 October 2026

- **PolygonCoil cubic lines converted (all 677 `lineOut4 … = data`, default build).** New module `Design/PolygonCoilCubicLineCert.lean`: certificate predicates that follow the checker's own recursion. `FV`/`AV` give one leaf `vertStep c v g = r` per filament vertex (cold starts: `coldStart c v = g` first). `SW`/`AW` give one leaf pair per block of up to three segments, `segStep (segStep (segStep acc …) …) … = acc'` and the matching `remStep` fold; `W`/`AW0` handle corners without a cell. `corner_some`/`corner_none` assemble `cornerEval4` with one `cornerFinalV` leaf. `LC` walks the corners through `lineStep` (one iteration of `lineGo4`, `lineGo4_cons`), with leaves for `cornerXYZ4`, `helAt`, `remP4`, `rwC`, `rtC`; `MC` covers `faceHC4`. Soundness theorems are proved once by induction. Leaves are non-recursive arithmetic functions on literals; the only bounded iterations inside a leaf are the fixed Newton counts of `coldStart`/`sqrtUpFrom`. The `meta` builder `line_cert` (interpreted) runs the checker's own functions on native values for the leaf values (untrusted) and takes the filament subterms from the body of `filsDL`. Standard axioms (`propext`, `Quot.sound` per line).
  - **Prototype numbers (one line, `lC0_0`):** decide +kernel 2.2 s, 0.21 MB. Generic coarse-leaf `eval_cert [vertStep, segStep, remStep, …]` 13 s, 44.8 MB (128k nodes, mostly list plumbing). Dedicated certificate, one segment per leaf: 1.9 s, 12.0 MB. Blocks of 2: 8.8 MB. **Blocks of 3 (adopted): 1.7 s, 7.7 MB.** The olean shares structurally equal terms, so only distinct values count; the size is the per-segment `Acc`/remainder snapshots (9 + 3 numbers) and the vertex records.
  - **Family:** Lines00–19 CPU 1,587 s in total (old, measured on Lines00/Lines10: 71 → 64 s, 76 → 84 s, i.e. ≈ 1.0–1.1×); peak 1.2–1.3 → 2.9 GB; private oleans 117 MB → **5.89 GB**. Cells0–3/Cover unchanged (rebuilt). `coil_stellarator_confined_concrete_N`: standard axioms. `cubic_emit.py` emits `line_cert`.
- **Group 3 (`∀ x ∈ Finset`, `∑ x ∈ Finset.Icc`):** new module `Certificates/IccListCert.lean`, which restates integer-interval and `range` sums and bounded quantifiers as list computations (`sum_Icc_eq_list`, `sum_range_eq_list`, `forall_Icc_of_all`, `forall_range_of_all`, `ite_mem_Icc`); tactic `icc_cert [defs]` = `simp only` + `eval_cert`; fixtures accepted/rejected. The builder is unchanged. `ValidatedBVP` (5 checks): 5.8 → 6.2 s, 1.39 → 1.40 GB, 1.5 → 4.6 MB. `ValidatedSlabData` (10 checks): 22.8 → 28.5 s, 3.95 → 3.08 GB, 1.1 → 99.5 MB. `validated_bvp`, `validated_slab_equilibrium`: standard axioms.
- **Group 2 (opaque leaves):**
  - `fieldAP_fixture` (`CoilKamSeg`): `eval_cert` (57k nodes); olean 1.9 → 21 MB, CPU 9 s.
  - `gridL1` a-priori bounds and `check_c0D` (`KamTorusAWeightedCheck`, 4 `decide +kernel`): `eval_cert` (95k–148k nodes); 51.7 → 63.2 s, peak 5.06 → 5.58 GB, olean 0.03 → 127 MB. The `wcheck_*` Kronecker checks of that module are still `decide +kernel`.
  - **`hessOK` (ballooning boxes): tool written, not applied.** `Design/SolovevBallooningBoxCert.lean` adds `ballooning_box "Q:…"/"Z:…"`, which proves `Cover.leaf2/axis2` with `hessOK … = true` by `bl_cert`. Measured: 5.6 MB of olean per box, ≈ 1.2 s; 825 boxes ≈ 4.6 GB, over the remaining disk allowance. Cells still use `ballooning_cover`; a conversion script is ready (generator: `solovev_ballooning_oracle.py` line 618).
  - **Kronecker-image equalities `Kv… = famPack…` (20 in the default build): not converted.** `eval_cert` stops at a compiled `Nat.rec` inside the slice packing, and the intermediates are multi-kilobyte integers. They need their own certificate, e.g. digit-block sums as in `DCert`.
- **Not done:** the docstring of `Certificates/EvalCert.lean` (its dependents were not rebuilt). The older bilinear `PolygonCoilCert00–05` (211 `checkChunk` lines) would need the same certificate for `lineOut` plus `checkLines`; at ≈ 7 MB per line evaluation (≈ 1,000 evaluations) that is ≈ 7 GB, over budget. `filsDL_eq` (Data; changing it rebuilds all Lines modules).
- **Counts** (lines containing `decide +kernel`, `PlasmaLean/` tree; default = modules reachable from `PlasmaLean.lean`): default **1,407 → 690**, overall **3,224 → 2,507**. These stage-6 figures are the current ones; earlier entries count differently (uses of `decide +kernel` rather than lines containing it, and different trees: before or after generated or on-demand modules were added or removed), so the series is not monotone across entries and the older numbers are kept as recorded. Private oleans of `Design/` now ≈ 17 GB on disk, of which ≈ 15 GB is the new explicit certificates of stages 5 and 6: the approved ceiling is reached.

### Phase 16: disk budget raised, 26 October 2026

- **User decision:** the budget for private certificate oleans is raised from about 15 GB to about 40 GB. Convert the ballooning `hessOK` boxes (≈ 4.6 GB) and the older bilinear polygon-coil cells (≈ 7 GB) as designed; keep looking for compact designs for the rest (the remaining ≈ 2,500 `decide +kernel` lines, the Kronecker-image equalities). Memory stays ≤ 6 GB per process.

## 11. Proposed extension: verified plasma evolution and geometric contribution paths

**Prepared 24 October 2026 against c46501d9. Status: proposed work; no new MHD evolution theorem is claimed.**
This extension complements the existing confinement and burn tracks. Sections 0–10 retain their
historical status. The corrected scientific specification is
[BKM, symmetry, thermal bounds and evolution](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/bkm-regularity-and-perelman-burn-bounds.md).
Contributor entry points and a result-card template are in
[CONTRIBUTING](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/CONTRIBUTING.md).

### 11.1 Research objective and success statement

Choose a coil geometry, operating parameters, a compatible equilibrium or approximate evolution,
and a nontrivial set of initial perturbations. Certify a stated interval on which the selected
plasma model exists and stays within specified error, stability, thermal and geometric bounds.
Use one candidate/witness throughout. An all-time result is a later target when the same estimates
close globally; a finite operating interval with explicit margins is already useful.

The intended chain is:

1. Certify the external vacuum field and its coil realization.
2. Construct or validate the finite-pressure state for the **total** field, with equation of
   state, boundary data and pressure matching.
3. Re-evaluate quasisymmetry and confinement after plasma response.
4. Bound a full evolution residual and prove existence/continuation for a neighbourhood of
   initial data.
5. Prove perturbation stability, core-temperature and yield bounds as distinct conclusions.

Vacuum quasisymmetry alone does not make step 2 automatic. A pointwise upper bound
`p_thermal <= p_eq` is a pressure-budget screen, not equality in force balance.
All-time bounds for supplied solutions do not establish their global existence.
Positive measure in velocity space should be accompanied by a physically meaningful energy
and pitch range, rather than used as a replacement for a robustness margin.

### 11.2 Work packages and evidence gates

All proposed module names below are targets, not existing implementations.

| Work package | Deliverable | Acceptance evidence |
| --- | --- | --- |
| E0 — Repair and expose assumptions | Correct README and active BKM note; add result cards, a physical-assumption index, and an audit import manifest. Replace contradictory live formulas in the other discovery notes. | Every advertised result names its candidate, model, quantifiers, existence status and supplied reductions. Default and optional audit coverage are separate. |
| E1 — Symmetry test | Prove the Lie-derivative/gradient commutator and the local zero-QS-error counterexample in the corrected note. State a genuine isometric-invariance theorem. | A proposed ansatz preserves equations, domain, boundary and constitutive data, or has an explicitly bounded reconstructed PDE residual. No inference from scalar QS error to zero stretching. |
| E2 — Periodic evolution benchmark | Formalize the fixed-model energy and bilinear estimates, scalar comparison, and Pizzocchero–Tassi Proposition 4.3. | Exact solution existence and an Hs error bound follow from certified data. A comparison theorem alone is labelled as such; no desired PDE conclusion is a certificate field. |
| E3 — Certified trajectory | Produce a small Fourier/time-polynomial benchmark and exact residual, initial-error, Hs and Hs+1 enclosures. | Include discarded nonlinear modes, interpolation error and continuous-time bounds. A deliberately omitted high-frequency mode makes the checker fail. |
| E4 — Toroidal-domain continuation | Formalize harmonic flux sectors, boundary cancellations and Hodge coercivity; extract the Kozono–Shimizu–Yanagisawa small-data theorem with its exact hypotheses. | Identify a nonempty admissible parameter set and nondimensional constants. Do not silently transfer a flat-torus or small-background theorem to a reactor-strength field. |
| E5 — Thermal existence and compatibility | Add local existence/continuation for the radial transport model, then a steady pressure-matched state or controlled coupled response. | Treat the degenerate axis and edge conditions. The pressure entering force balance is the thermodynamic pressure, or the actual mismatch is bounded in a suitable derivative norm. |
| E6 — Entropy and invariant operating bounds | Formalize the corrected relative-entropy identity with all source/reference/boundary terms; retain the existing two-sided temperature barriers. | State the sign and coercivity hypotheses, exhibit failure outside them, and certify core temperature, fuel-density and reactivity ranges over the interval. |
| E7 — Compatible numerics | Verify a constrained-transport update, an equilibrium-preserving fixture, and one admissible-state/entropy estimate. | Separate divergence preservation, positivity, entropy, helicity, and continuum error. Each claim has its own hypotheses and proof. |
| E8 — Integrate a useful candidate | Apply the completed evolution and thermal chain to a shared candidate already used by the confinement work. | Publish explicit parameter/initial-data uncertainty, time horizon, error margins, fuel/heating assumptions, and unresolved model bridges. Only mark a gate complete after the producer theorems are discharged. |

Dependencies: E0 and E1 can proceed immediately; E2 precedes E3; E4 changes the geometry/model
and therefore requires new analytic estimates; E5 and E6 can proceed alongside E2–E4;
E8 requires the relevant earlier gates and the coil/confinement chain. E7 provides useful
oracles and discrete guarantees, but does not replace E2/E4's continuum analysis.

### 11.3 The concrete first theorem to implement

Use the flat periodic benchmark exactly as in
[Pizzocchero–Tassi, Proposition 4.3](https://arxiv.org/html/1905.13722v1):
divergence-free, zero-mean fields on `(R/2pi Z)^3`, smooth initial data and approximation,
Sobolev order `s>5/2`, and the stated viscosity/resistivity coefficients.

Let `epsilon_s` bound the **full** PDE residual, `delta_s` the initial discrepancy,
and `D_s,D_(s+1)` the approximation norms. First prove a checked nonnegative control function
satisfies

$$
R'\ge-\mu R+
(\widehat G_sD_s+\widehat K_sD_{s+1})R+
\widehat G_sR^2+\epsilon_s,\qquad R(0)\ge\delta_s,
$$

where `mu=min(nu,eta)` in this normalization. Then prove the PDE bridge yields existence
and `||U-U_a||_{H^s}<=R` before the control horizon. Certify a horizon strictly greater
than `T_burn` to cover the requested closed interval without an endpoint gap.

The abstract scalar lemma is an early deliverable. The full source theorem additionally needs
local well-posedness, continuation, bilinear estimates and norm conventions. Keep those gaps
visible. With a smooth finite Fourier approximation, the full nonlinear residual has explicitly
computable modes outside the truncation: no hypothetical bound on an unknown true solution's
Fourier tail should be substituted for the residual theorem.

For the bounded-domain route use
[Kozono–Shimizu–Yanagisawa (2025)](https://doi.org/10.1007/s00208-025-03223-5).
Their small harmonic background and small perturbation conditions are not a reactor-scale
certificate. First derive explicit geometry-dependent constants or a validated estimate for
a particular domain. The background flux lives in a harmonic subspace, so the magnetic
Poincaré inequality must be stated on its complement.

### 11.4 Tests for a symmetric or approximately symmetric plasma ansatz

Before numerical optimization or Lean implementation, write the ansatz in the full equations
and calculate the residual.

An exact positive fixture is the standard Alfvénic class on the flat three-torus:
`a(x,t)=a_0(x+t b_0), v=a, b=b_0+a`, with constant `b_0`, smooth periodic
divergence-free `a_0`, and constant total pressure. Direct substitution gives a global
smooth ideal solution and BKM integral `2T ||curl a_0||_infty`.
For nonzero `b_0` and mean-zero `a_0` this lies outside the zero-mean magnetic-field
hypothesis of the Pizzocchero–Tassi benchmark. Formalize it separately, with the absence of
toroidal-vessel confinement, thermodynamic closure, and transverse perturbation stability
explicit. It tests the ansatz mechanism without claiming a stellarator construction.

- A genuine Killing generator preserving all coefficients and boundary conditions is a useful
  benchmark. Symmetry of initial data is preserved only after the equation and uniqueness
  hypotheses have been supplied.
- Quasisymmetry of magnetic strength is generally a guiding-centre property. It does not make
  the pressure gradient, Laplacian or force operator commute with its generator.
- The local example `B=e_z, X=(1+y)e_x, p=y` has zero scalar QS error but
  `[X,grad p]=-e_x`. Include it as a negative sanity target.
- Approximate invariance needs norms of `L_X g`, coefficient/background derivatives, and boundary
  mismatch or, preferably, a complete reconstructed residual. Do not posit a Riccati estimate
  whose nonlinear coefficient is only the scalar QS error.
- Exact 2-D, helical and axisymmetric ansätze are different reductions. A theorem inside one
  invariant class does not prove stability against perturbations outside that class.
- Field-line KAM confinement is an ODE statement for a static field. It does not control
  MHD current-sheet formation, bulk instability, kinetic turbulence or a moving interface.

The earlier elliptic-profile idea remains an optional field-construction test:
study the real periodic branch of `y^2=[psi-(x-1)^2](2-x)`, then solve or obstruct the
separate embedded Maxwell/coordinate compatibility problem. Do not assume that an elliptic
curve or a prescribed strength function already supplies a realizable three-dimensional field.
Recheck any earlier claimed obstruction with its exact axis, coefficients and hypotheses.

### 11.5 Perelman-inspired work: a testable functional programme

The target is a physically derived estimate with useful coercivity. Start with existing
energy/relative-entropy identities rather than assuming that a Ricci-flow formula transfers.

For any candidate functional:

1. Specify the evolution, unknowns, domain, boundaries, forcing and reference state.
2. Differentiate it exactly, retaining reference-profile, boundary, reaction and compression
   terms. Record all signs and regularity assumptions.
3. Test it against explicit solutions and thermal-runaway examples.
4. Prove which norm or operating quantity it controls, including constants.
5. Check scaling and whether concentration can leave the functional bounded.
6. Only then test whether its dissipation controls a continuation criterion.

Two immediate outputs are the corrected thermal entropy identity in
`notes/theory/relative-entropy-dissipation.md` and a core-yield lower bound from verified
temperature/fuel/reactivity bands. Total heat alone does not prevent a cold core. A generic
entropy inequality does not bound current or vorticity suprema. Nonnegative ideal-MHD energy
does not imply coercivity in all displacement directions: neutral/relabeling modes require a
specified quotient or constraint.

Use [Tao's 2007 discussion](https://terrytao.wordpress.com/2007/03/18/why-global-regularity-for-navier-stokes-is-hard/)
and [Perelman's original paper](https://arxiv.org/abs/math/0211159) for the methodological
question, not as a missing MHD theorem. The counter-propagating Alfvén-wave structure has
already supported a GR-inspired stability theorem in
[He–Xu–Yu](https://arxiv.org/abs/1603.08205); its spatial-separation estimates on Euclidean
space need replacement in a bounded toroidal geometry.

### 11.6 Concrete entry points for topology, differential geometry and complex geometry

**Topology.** Prove the following bridge from the pointwise kernel.
If sufficiently smooth divergence-free fields `B,J` satisfy `J×B=grad p`, then on each
compact connected regular pressure-level component without boundary they give a tangent
frame. Curling force balance gives `[B,J]=0`. The component is a torus.
State compactness, regularity and connectedness componentwise; this says nothing about critical
levels or the magnetic axis. A second target is flux/harmonic-sector bookkeeping for E4 and E7.

**Differential geometry.** Prove the gradient commutator, a genuine symmetry-preservation theorem,
and a dictionary between Euclidean fields and supplied flux coordinates. Extend current coarea
bridges to a clearly specified family. For near-axis QS, distinguish formal compatibility from
convergence and embedded global realization. Use negative examples as acceptance tests.

**Complex analysis and geometry.** The most direct quantitative target is already identified:
actual-coil KAM bounds in `notes/theory/coil-kam-status.md`.
Develop anisotropic holomorphic strips, a torus-adapted complex neighbourhood, cancellation-aware
bounds for groups of Biot–Savart segments, and certified lower bounds on the toroidal component.
Compare the new residual bound with the exact current KAM threshold; report a failed bound as a
failed certificate, not as nonexistence of an invariant torus. Existing modules
`BiotSavartComplex`, `StripPaleyWiener`, `CauchyTwoVar`, `FourierSumHolo` and
`AnalyticComposition` provide starting points.

For a smaller Hodge/complex-torus task, take `Im tau>0` and a smooth real closed one-form
on `C/(Z+tau Z)`, with periods `a,b` along the canonical cycles `1,tau`. For the flat
metric, or any metric in its conformal class, prove:

$$
\int |\alpha|^2\,dA \ge \frac{|b-a\tau|^2}{\operatorname{Im}\tau},
$$

with equality if and only if the form is its harmonic representative. Identify physical periods only after fixing
orientations. The current flux-holonomy note needs a sign audit:
if `sigma=h dtheta wedge dphi`, then
`i_B sigma=h(Btheta dphi-Bphi dtheta)`. A point of the Jacobian alone does not recover the
rotational transform. A magnetic two-form restricted to a flux surface vanishes, so it does
not provide a positive-degree line bundle there.

**Optional new benchmark.** Audit the 21 October 2026
[López preprint](https://arxiv.org/html/2610.29921v1) on an exact nonsymmetric vacuum field
from a Weierstrass/algebraic construction. Its proposed nested tori and closed lines with
constant rational transform are interesting formalization targets. This is a newly posted
construction to check, not an established QS, coil-realization, stability or robust-confinement
result; its computer-assisted root/embedding conditions need independent review.

### 11.7 Numerical methods and a reproducible contribution workflow

Use existing methods as untrusted candidate generators and formalize the properties needed.

- Constrained transport/compatible elements: [Li–Zhang–Zheng](https://arxiv.org/abs/2008.09244).
  Prove `D C=0` and its preservation by the actual update; retain flux sectors.
- Equilibrium-preserving discretization: [Fambri et al.](https://arxiv.org/abs/2305.06497),
  including their Solov'ev benchmark.
- Entropy-stable resistive MHD: [Bohm et al.](https://arxiv.org/abs/1802.07341).
  Include nonconservative and boundary terms; certify any transcendental evaluations.
- Positivity-preserving reconstruction and flux limiting:
  [Deppe et al.](https://arxiv.org/abs/2306.04755). Borrow the numerical invariants;
  laboratory stellarator modelling does not require general-relativistic gravity.

For each target provide a short ordinary-mathematics theorem and proof, exact Lean declaration,
positive and negative examples, one command to check a small fixture, data/seed hashes, pinned
numerical dependencies, regeneration instructions, and an observed resource budget.
Separate scientific/model review from formal proof review. Publish the import/audit scope.
A numerical observer, an analyst, and a Lean contributor can work on the same target without
each mastering all three roles.

**Stop conditions:** if physical hypotheses cannot be met, the residual bound misses the
threshold, the symmetry reduction fails, or a functional is noncoercive, record the obstruction
and change the target. Do not mark an implication complete by adding its conclusion as an
assumption. No completion marks or dated scientific-progress claims are added by this plan.

## 12. Proposed extension: model adequacy and probabilistic goals (G3)

**Added 26 October 2026 from the AI review notes of 24 October (`notes/goals/`). Status: proposed;
no new Lean results are claimed.** The deterministic goals G1 (confinement and stability) and G2
(thermal performance) remain the core. A targeted programme G3, model adequacy and useful
refinements, is added. Statistical criteria are developed only where they answer a practical design
question.

- **Probabilistic work (P1–P4):** finite-time particle loss and wall deposition under a specified birth
  distribution; justified uncertainty in inputs (coil errors, profiles), with deterministic
  uncertainty sets preferred when no law is justified; reliable computation of these quantities
  (Monte Carlo with certified error bounds). A new stochastic physical equation is conditional work.
  These labels are local and distinct from the older formalization roadmap's P0–P9 gates.
- **Deterministic additions (N1–N3):** N1 quantifies the effect of one selected omitted term on a
  design observable (exact projected error equation, residual bounds, observable transfer); N2 adds
  one minimal correction only when activated; N3 is shared decision infrastructure (evidence record,
  decision margin, failure classification). Modified energies and driven relative entropy are
  methods that also serve G1/G2.
- **Out of scope:** a complete microscopic particle-to-MHD derivation. A particular estimate from
  that literature is eligible when it resolves a named problem.
- **Details:** [overview](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/goals/plasmalean-goals-overview.md),
  [probabilistic goals](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/goals/probabilistic-goals-and-techniques.md),
  [deterministic goals](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/goals/deterministic-goals-and-techniques.md),
  [milestones](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/goals/implementation-milestones.md).
- **Unresolved cross-references:** the companion notes cite work packages "§12 D0–D4", "§12 K0–K6"
  and "§12.10" of a plan version that was not among the supplied files. Section 11.2 defines the
  evidence gates E0–E8; the D/K references stay unresolved until that section is supplied or
  reconstructed.

## 13. Implementation log (continued)

New dated phase entries are appended here. The entries above, from 25 October 2026 on, belong to
section 10's log and are kept in place.

### Phase 16: seventh stage (ballooning boxes, bilinear polygon-coil chunks, literal filament data), 26 October 2026

- **Ballooning `hessOK` (825 boxes, `SolovevBallooningCells00–15`):** `ballooning_cover` → `ballooning_box` (`Design/SolovevBallooningBoxCert`, `bl_cert` per box); `solovev_ballooning_oracle.py` emits it. Wall time of the 16 modules 781 → 788 s (CPU 1,287 s), peak 2.5–3.5 → 4.8–5.6 GB per module, private oleans 3.63 → **7.64 GB**. `cover_all`: `propext`; `reactor_ballooning_all`: standard axioms. Nothing in `ballooning_cover` is evaluated by `Eq.refl` any more except the plan assembly.
- **Bilinear polygon-coil chunks (all 211 `checkChunk … = true`, `PolygonCoilCert*`):** new modules
  - `Design/PolygonCoilChunkCert.lean`: `WR`/`AWR` (segment walk with the cell remainder `segStep … r`, blocks of three segments), `corner_of` (`cornerEval`, one `cornerFinal` leaf; vertex steps reuse `FV`/`AV` of `PolygonCoilCubicLineCert`), `LCB`/`lineStepB`/`lineB_of` (`lineOut`, leaves `cornerXYZ`, `rhOf` = `cellRC`, `helAt`), `CO` (`cellsOK`, one leaf per cell), `CLines`/`chunk_of`, `DT` (`(grid.drop k).take n`, one step per list cell); builder `chunk_cert hfils hface`. Statements of `cert_F_i` unchanged.
  - `Design/PolygonCoilFilsCert.lean`: `fils_cert`, literal filament data = `((zip RK RV).flatMap orbit).map (mkFil o)`: `ORB` (one leaf per vertex image), `CP` (one `mkSeg` leaf per segment, closing segment included), `mkFil_of`, `fils_of`. Expected values are taken from the literal; the kernel checks every leaf.
  - `Design/PolygonCoilDataL.lean`: literal `filsDLB` (generated by evaluating `filsD`), `filsDLB_eq` (`fils_cert`, `propext`), `faceChk0–3` (`bool_cert`).
  - One module of 34 chunks needed 5.7 GB peak and a 761 MB olean, so each `Cert0k` was split in half: `PolygonCoilCert06–11` hold the second halves (`Cert(k+6)` imports `Cert k`); `PolygonCoilCover` imports 06–11. Before: Cert00 (34 chunks) 168 s, 2.08 GB, 24 KB. After: 12 modules of 17–18 chunks, 76–87 s wall (91–99 s CPU) each, 951 s wall in total, peak 3.43–3.68 GB, 369–382 MB each, **4.54 GB** in total. `cert_0_6`: `propext`; `coil_stellarator_confined_concrete`: standard axioms. `polygon_emit.py` emits `chunk_cert filsDLB_eq faceChkF` and imports `PolygonCoilDataL` (`emit_certs` is generic in `nfiles`; the stage-7 split was done by moving halves, not by re-running it: the grid pickles are not in the repository).
- **Cubic data and checks:** `filsDL_eq` (`PolygonCoilCubicData`) → `fils_cert` (4 s); `filsC_shape`, `filsC_ok` (`PolygonCoilCubicFrontier`) and `vertFarC_all` (`PolygonCoilCubicConfined`) → `bool_cert`. `cubic_emit.py` updated. Rebuilt downstream in the default build, one module at a time: Lines00–19 58–76 s each (peak ≤ 2.9 GB, oleans unchanged at ≈ 290–300 MB), Cells0–3, Cover, CoilField*/CoilKamSeg/Torus/Point/Lip/Residual. The on-demand `CoilKamData/Grid/Pts0–7/Rows/Num/Cert` depend on `PolygonCoilCubicData` and were **not** rebuilt. `coil_stellarator_confined_concrete_N`: standard axioms; `filsDL_eq`, `vertFarC_all`: `propext`; `filsC_ok`, `filsC_shape`: no axioms.
- **Not done (time):** item 3, the Kronecker-image equalities `KvXX … = famPack …` (≈ 20, closed by `kernel_fact`). Design sketch: the right-hand side is `famPack` → `slicePack` → `bsplit` (`Nat.rec` divide and conquer) → `rowV` → `rpack`/`rpackR`. A certificate following that tree with literal intermediates costs O(size × depth) of multi-kilobyte integers. Cheaper: state the image digit-wise, i.e. certify `famTB … − famO … = Σ_rows rowV(j)·2^{bWj}` through the existing `SCert`/`PCert` digit machinery by blocks of rows, with leaves `rowV … j = v_j` (each a small `rpack` tree on one row) and one digit-sum certificate for the shifted sum; `famTB`/`famO` (the fast side) stay as `Nat` leaves. Also not done: `wcheck_*` (`KamTorusAWeightedCheck`, 117 dependent modules) and other low-level modules (`PolyInterval`, `ValidatedTrig*`, `KronExpr`), whose change rebuilds large parts of the default build; `RationalStellaratorForeverCert` (its dependents include Mu2–Mu5 and MuQuarter); `NearAxisQATrappedTimeCells` fixtures (dependents include the 16 OscRows modules, ≈ 30 min); `LandremanFamily2.Pcoeffs_check` (`eval_cert` should work; rebuilds the 7 `…Cert*` modules).
- **Counts** (lines containing `decide +kernel`): default **690 → 475**, overall **2,507 → 2,292**. The default-build lines left are mostly in the KAM/Landreman/near-axis certificate families (`LandremanFamily2Cert1–7` 177, `ScrewPinchModes` 28, `KamTorusA*Check` 59, `SolovevMercierQuadrature` 22, `RationalStellaratorCoilsGrad` 17, `NearAxisQATrappedTimeRows` 17, `ValidatedTrig*` 26, …) plus docstring mentions. `kernel_fact` leaves: 7,469 (default), 20,937 (overall). Private certificate oleans (files > 50 MB) now ≈ **24.2 GB** (of the 40 GB allowance); `.lake/build/lib/lean/PlasmaLean` is 25 GB.

### E1 and §1 sanity theorems, 26 October 2026

Gate E1 (§11.2, §11.4) and the "sanity theorem or counterexample" promised in §1. All results use the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `decide` of any kind.

- **Lie-derivative/gradient commutator** (`Theory/Fields/LieGradient.lean`): `lieBracket_gradient` (Hessian symmetry as a hypothesis) and `lieBracket_gradient_of_contDiffAt` (`f` of class `C²`) prove `∇(X f) − [X, ∇f] = (DX + DXᵀ) ∇f` with `X f = ⟪X, ∇f⟫` and Mathlib's `VectorField.lieBracket`. This is the Euclidean case of `[X, grad f] = grad(Xf) − (L_X g)^♯ grad f`. Also `isSelfAdjoint_fderiv_gradient`, `hasFDerivAt_gradient`, `dualToSpace`, and the Killing sanity case `lieBracket_gradient_of_killing`. The Cartesian `[X·∇, Δ]` formula is not formalized.
- **Quasisymmetry is not a PDE symmetry** (`Sanity/QuasisymmetryNotSymmetry.lean`): for `B = e_z`, `X = (1+y) e_x`, `p = y`, `qs_scalar_error_zero` gives `div B = div X = 0`, `[X, B] = 0`, `X|B| = 0` and `X × B = ∇(−y − y²/2)` (`qs_cross_eq_gradient`); `qs_X_pressure` gives `X p = 0`. Nevertheless `qs_lieBracket_X_gradP` gives `[X, ∇p] = −e_x`. The packaged statement is `quasisymmetry_not_pde_symmetry`, and `qs_strain_term` identifies the obstruction as `(DX + DXᵀ)∇p = e_x`.
- **Conditional Riccati comparison** (`Theory/Stability/RiccatiComparison.lean`): `riccati_le_initial` proves that `Y' ≤ −νY + CεY²` on `[0, T)` (right derivatives), `0 ≤ Y(0)` and `CεY(0) < ν` give `Y ≤ Y(0)` on `[0, T]`. `riccati_exp_decay` adds `Y ≥ 0` and `Cε ≥ 0` and gives `Y(t) ≤ Y(0) e^{−(ν − CεY(0))t}`. `riccati_hyp_exp` shows the hypotheses are satisfiable. The differential inequality is a **hypothesis** (R3) and is not proved for MHD.
- **Magnetic 2-form on flux surfaces** (`Theory/Fields/FluxSurfaceTwoForm.lean`): `magneticTwoForm B u v = ⟪B, u × v⟫` (`= ⟪B × u, v⟫`, `magneticTwoForm_eq_cross_inner`). The identity `triple_smul_eq` gives `magneticTwoForm_eq_zero_of_orthogonal`, and from it `magneticTwoForm_flux_surface`: if `∇ψ(x) ≠ 0`, `B·∇ψ = 0` and `u, v ⟂ ∇ψ(x)`, then `ω_B(u, v) = 0`. Sanity checks: `magneticTwoForm_basis` (`ω_{e_z}(e_x, e_y) = 1`) and `magneticTwoForm_tangent_example`.

### Phase 16: eighth stage (`kernel_fact` audit, family-image certificates, quadrature and box checks), 26 October 2026

- **Audit of the `kernel_fact` leaves (new `scripts/audit_kernel_fact.py`).** For each module that uses `kernel_fact`, the script runs a small Lean program on the built `.olean`. The program walks the proof terms, finds the leaves `@id P pf` (`pf` = `Eq.refl`, `Nat.le_of_ble_eq_true`, `lt_of_ble_succ`, `Nat.ne_of_beq_eq_false`) and classifies each statement `P` by the PlasmaLean definitions it unfolds: their number, the longest unfolding chain, and their literal bits. The classes are: **a**, no PlasmaLean definition (literal facts); **a-data**, data definitions with no recursion (`NLM ≤ 2^ddLM`, `List.getD` of a literal list); **b**, a recursive PlasmaLean definition is reached. With `--time`, each class-b leaf is also checked on its own (`Environment.addDeclCore`) and timed. Results go to `.lake/kernel_fact_audit.jsonl`; `--report-only` prints the summary. No profiler is used.
  - **Default build:** 7,532 source uses in 61 modules; 62,443 leaves (the forall/list expansions multiply the uses): a 9,388, a-data 46,921, **b 6,134**. Kernel time of the b leaves: < 1 ms 2,250; 1–10 ms 3,423; 10–100 ms 427; 0.1–1 s 20; ≥ 1 s 14 (≈ 56 s in total). The b leaves are mostly `nodeFin`/`normFin` of `toEx` trees (434; degree and box conditions, 1–30 ms each), `famL1` of the stored families (462), `box3`/`wt` of the trees, and the ℚ majorants of the Maj modules. **Heaviest leaves (opaque, ≥ 0.1 s):** `mu_C2Z`/`mu_C2R` (`MuMaj`, `mD2Q … ≤ C2Q`, 4.2/3.6 s); `gc_C2Z`/`gc_C2R` (`FamMaj`, `TorusMaj`, `NegTorusMaj`, ≈ 2 s each); `corr_majQ` (`BoxPert`, 6 × 1.7 s + 3 × 0.38 s); `allNodes_res`, `nodesOK_eY`, `gc_maj_E_aTQ`, `mu_maj_E/Q`, `maj_eBm_le` (0.25–0.31 s each); `box_accepted` (`SolovevBallooning`, 0.39 s) and `noProfile_rejected` (0.11 s).
  - **Overall:** 21,180 uses in 109 modules; 249,148 leaves: a 27,920, a-data 202,674, **b 18,554**; 98 b leaves take ≥ 0.1 s, 47 take ≥ 1 s (487 s). The largest are the 48 `Kv… = famPack…` equalities of the on-demand Ew1–4 and Mu2–5 H chains (8–16 s each), not converted (those families are frozen), and the 16 of the Mu2–5 L chains (0.4–0.6 s).
- **Family-image certificate (new `Certificates/FamPackCert.lean`), all 20 `Kv… = famPack…` equalities of the default build** (`MuChainL/H`, `FamChainL/H`; the Torus and NegTorus chains have none). Contents:
  - `RowsEq f s n vs`: one kernel fact `rowF … sd t = v` per row. This is `rowV` of one row, a small `rpack` tree on the fields of that row.
  - `FPCert … k l v`: one step per stored coefficient, consisting of `Nat.ble (2 M_j + 1) (2^dr)`, the rows, and the placement at `D ± k` (`placeF`). The value `v` is an expression over the row literals (`rowsVal`, a Horner sum), not a literal image.
  - Soundness: `famPack_eq_of_cert` (via `bsplit_eq`) and `eq_famPack_of_cert`.
  - Tactic `fampack_cert`: kernel `whnf` reads the stored coefficients and the meta code computes the row values. The remaining leaf is `lhs = v`, which compares the fast offset image `famTB − famO` with the assembled rows, as designed in stage 7.
  - Fixtures: `RowsEq.fixture`, `famPackCert_fixture`.
  - Measurements (before → after):

    | Module | CPU (s) | Peak (GB) | Private olean (MB) |
    | --- | --- | --- | --- |
    | `MuChainL` | 24.9 → 29.9 (incl. lake) | 2.54 → 2.46 | not recorded before → 5.03 |
    | `FamChainL` | 18.4 → 20.5 | 2.24 → 2.13 | 3.85 → 4.01 |
    | `MuChainH` | 72.1 → 67.1 | 3.84 → 3.86 | 2.75 → 6.07 |
    | `FamChainH` | 44.0 → 45.5 | 3.39 → 3.31 | 2.11 → 4.70 |

    One L equality: `kernel_fact` ≈ 0.7 s → certificate ≈ 0.6 s.
  - Rebuilt in the default build: `Fam/Mu` `OutL/H`, `Adm`, `Exact`, `Forever`, `Confined`, `Family`, and `Box*`. `kderLM_A`, `kderHM_LRx`, `kderLF_A`, `kderHF_thZe`, `alpha_gc_box_confined_forever`, `alpha_gc_confined_forever_robust` and `rationalStellarator_gc_mu_confined_forever` use only the standard axioms.
  - Generators: `lam_emit_lean.py` and `fam_emit_lean.py` emit `fampack_cert`, and `proofterm_emit.kernel_fact_text` adds the import. The on-demand Ew*, Mu2–5 and MuQuarter modules are downstream of `MuChainL/H` and must be rebuilt when they are next built. Their sources are unchanged.
- **`decide +kernel` → explicit evaluation certificates:**
  - `ScrewPinchModes`: 36 `QPoly.checkOn` checks (28 lines), `eval_cert`. CPU 55 → 115 s, peak 2.94 → 4.35 GB, private olean 4.1 → 252 MB. `ScrewPinchModesHighM` rebuilt. `stable_uniform` and `stable_open_family` use only the standard axioms.
  - `NearAxisQATrappedTimeRows`: 16 `timeBoxOk`, `fiv_cert`. CPU 37 → 57 s, 2.36 → 2.96 GB, 0.05 → 101 MB. Its 4 dependents were rebuilt. `time_grid` depends on `propext`; `reference_kick_osc` uses only the standard axioms.
  - `SolovevMercierQuadrature`: 18 cover cells and 2 rejected fixtures (`cellCheck`, `fiv_cert`). CPU 19.7 → 26.1 s, 1.88 → 4.65 GB, 1.9 → 28.4 MB. Its 21 dependents were rebuilt, including `LandremanFamily2Cert1–7`. The oracle docstring is updated.
  - `NearAxisQATrappedCellsRows1–3`: 24 `boxOkI` leaves, `fiv_cert`. Rows1 CPU 15.9 → 23.9 s, peak 2.28 → 2.51 GB; private oleans 7 KB → 52/53/55 MB. The 8 dependents (`…Resonance` … `…OscCover`) were rebuilt. `boxLeaf_0_8_0_16` uses no axioms. `SolovevMercierQuadrature.normalized_well_dominance`, `LandremanFamily2Cert.family2_mercier_stable` and `reference_kick_osc` use only the standard axioms. Zero warnings.
  - None of these four modules has a generator in `scripts/`. `solovev_mercier_quadrature_oracle.py` only proposes cells; its docstring is updated.
- **Tried, not converted:**
  - `LandremanFamily2Cert*` `oneD`/`outerArc` quadratures: `fiv_cert` did not finish one `oneD 128` check in 10 min.
  - `NearAxisQAAveraged` with `eval_cert`: the build failed (evaluation depth exceeded on `amp3Lit_eq`, "sides evaluate to different values" on `S3pos/neg_eq`, a `whnf` timeout on the cover) and peaked at 8.5 GB, so it was reverted. Note that the unchanged module already peaks at **6.16 GB**.
  - `RationalStellaratorCoilsGrad`: `eval_cert` gets stuck at `Pz` and at `zipL add1`.
  - The Maj leaves `mD2Q … ≤ C2Q` via `of_decide_eq_true (eval_cert [aTQ, mvQ])`: the builder emits an ill-typed `Fin.ofNat._proof_1` application (kernel type mismatch on `NeZero (5+1)`). This is a bug in `PlasmaLeanMeta/EvalCert` (`Fin` numerals with an instance-implicit proof argument).
- **Counts** (lines containing `decide +kernel`): default **475 → 381**, overall **2,292 → 2,198**. `kernel_fact` source uses: default 7,532, overall 21,180, of which the default build has 6,134 opaque (class-b) leaves and 34 of ≥ 0.1 s (overall 18,554 and 98). Certificate oleans: about +0.55 GB this stage (≈ 24.8 GB of 40 GB).
- **Open problems:**
  1. The Maj ℚ majorants and `corr_majQ` (≈ 30 s of opaque kernel time in the default build) need the `Fin.ofNat` fix in the `eval_cert` builder, or a dedicated tree certificate for `mQ`/`mDQ`/`mD2Q`.
  2. `nodeFin`/`famL1` leaves: thousands of small (1–30 ms) recursive evaluations. They could become `FPCert`-style per-node certificates.
  3. The fast side `famTB − famO` is still evaluated in one leaf per equation.
  4. The KAM `wcheck_*`, `LandremanFamily2Cert*` quadratures, `NearAxisQAAveraged` (peak over budget) and `ValidatedTrig*` remain.

### Phase 16: ninth stage (`eval_cert` builder fixes, Maj majorants, weighted K2 readings, quadratures), 26 October 2026

- **Builder fixes (`PlasmaLeanMeta/EvalCert.lean`; behaviour unchanged on terms that were already certified, since each fix only acts where the old builder failed or emitted an ill-typed term):**
  - *Dependent arguments* (`depPositions`, `filterDep`): an argument on which a later binder type or the result type depends (`n` in `Fin.ofNat n [NeZero n] a : Fin n`, `val` in `Fin.mk val isLt`) is replaced by its value only if the abstraction `fun x => e[x/a]` is a well-typed non-dependent function (`Meta.check`); otherwise it is left unevaluated. This was the ill-typed `Fin.ofNat._proof_1` term of stage 8. `decide` and matchers are not filtered.
  - *Proof arguments* are never evaluated (`nonVals`), *recursors and quotients* (the cast `h ▸ v` of `Fin.cases`, `Quot.lift f h (Quot.mk r a)`) take one `whnfCore` step, `Quot.mk r a` is a value (Finset/Multiset sums), and partial applications of operations or recursive definitions (`zipL add1`, `Int.add` passed as data) are values. This unblocked `RationalStellaratorCoilsGrad` (stage 8: "stuck at `Pz`", "`zipL add1`").
  - New tactic **`eval_decide [f₁, …]`**: a decidable closed proposition as `of_decide_eq_true` of the certificate of its `decide`; **`fiv_decide`** (`EvalCertFIv`) is the same with the `FIv` operations as leaves.
  - Regression fixtures (`Certificates/EvalCert.lean`): `evalCert_finOfNat_fixture` (`(Fin.ofNat 6 3).val = 3`), `evalCert_finTab_fixture` (lookup through `Fin.cases`), `evalDecide_fixture`; `fivDecide_fixture` (`EvalCertFIv`).
- **Maj ℚ majorants** (`TorusMaj`, `NegTorusMaj`, `FamMaj`, `MuMaj`): `mD2Q … / 2 ≤ C2Q` (`mu_C2Z/R`, `gc_C2Z/R`), `mQ aTQ 0 … ≤ m…Q` (`gc_maj_E_aTQ`, `mu_maj_E/E4/Q`, `maj_eBm_le`) → `eval_decide`; `allNodes_res`, `nodesOK_eY` → `eval_cert` (one leaf per rational operation; the shared subtrees of the trees are evaluated once). `BoxPert.corr_majQ` (9 conjuncts, one certificate) → `eval_decide`. One `mu_C2Z`: builder 2.6 s, kernel 4.1 s (`kernel_fact` leaf 4.2 s). Generators `gc_maj.py`, `neg_maj.py`, `fam_maj.py`, `lam_maj.py` updated (Mu4/Mu5 Maj untouched).

  | Module | CPU (s) | Peak (GB) | Private olean (MB) |
  | --- | --- | --- | --- |
  | `TorusMaj` | 10.0 → 20.0 | 2.17 → 2.28 | 3.5 → 18.6 |
  | `NegTorusMaj` | 5.7 → 14.5 | 2.07 → 2.18 | → 15.6 |
  | `FamMaj` | 6.6 → 14.6 | 1.98 → 2.17 | → 15.5 |
  | `MuMaj` | 14.6 → 29.6 | 2.58 → 2.73 | → 30.5 |

  ("Before" is `lake env lean` on the HEAD file, "after" is `lake build`, which adds ≈ 1–2 s.)
- **SolovevBallooning fixtures** `box_accepted`, `noProfile_rejected`, `axisOK_needs_positive`: `kernel_fact` → `bl_cert`.
- **KAM `wcheck_*`** (`KamTorusAWeightedCheck`, 6 theorems, 10 bounds): `decide +kernel` → `kron2_proof` (`Certificates/KronProof2D`: reading certificate `PCert2`, blocks of 8 rows as kernel facts, final comparison). `kron2_proof` now accepts the scaled form `wl1KronP … * c ≤ Kb` (`wl1KronP_mul_le_of_cert`, fixture `kron2Proof_scaled_fixture`) and falls back to the kernel's `whnf` (`kNat`, `kInt`, `kNatFun`) when compiled evaluation is not available (definitions of the current module). CPU 68.5 → 83.8–92.6 s, peak 5.23 → 4.91–5.51 GB, olean 127.3 → 127.5 MB.
- **`ValidatedTrig`, `ValidatedTrigFast`** (fixtures, 26 lines; `atanTabN_check`): `fiv_decide`, `eval_cert`. CPU 4.5 → 6.2 s and 22.8 → 30.6 s (incl. lake), peak ≤ 1.8 GB, oleans 2.07 → 2.73 MB and 2.89 → 7.41 MB.
- **`RationalStellaratorCoilsGrad`** (17 lines): `gAij_eq`, `len4_all` → `eval_cert`; the 8 Taylor-shift covers → `cover_cert` (local macro: `eval_cert` with `trunc3`, `shiftAx`, `lenOK`, `leafOK` as leaves; the plan recursion is unfolded, ≈ 1,700 nodes per cover instead of 8·10⁵ without the leaf operations). CPU 23.9 → 66.2 s, peak 4.77 → 4.30 GB, olean 4.4 → 62.8 MB. `grad_cert.py` updated.
- **Landreman `oneD` quadratures** (34 lines in `LandremanFamily2Cert1–7`): new macro `oned_cert` (`LandremanFamily2Quad`): the `fiv_cert` leaves plus `FIv.asinFast`, `FIv.coshSmall`, `FIv.divInt`, `Ycell`, `Wcell` as kernel leaves, so that the fast enclosures are no longer unfolded into their `Nat` arithmetic; the six integrands share `evc`, `evsig`, `evh`, … at `±Y` through the builder's table. One `oneD 128`: 19,240 nodes, builder 0.7 s, kernel 4.2 s (stage 8: `fiv_cert` did not finish in 10 min). `Cert1`: CPU 207 → 201 s, peak 4.19 → 4.33 GB, olean 0.75 → 35.4 MB.
- **`NearAxisQAAveraged` split** (peak 6.16 GB) into `NearAxisQAAveragedModel` (model, amplitudes, enclosures, `CoverCert` and its builder), `…Amp3` (`amp3Lit`, `amp3Lit_eq`), `…Stage` (`S3pos/neg`, `S3pos/neg_eq`) and `NearAxisQAAveraged` (covers, global bounds, main theorem, fixtures); statements and names unchanged. Not converted (no time to rebuild and measure; see open problems).
- **Counts** (lines containing `decide +kernel`): default **381 → 297**, overall **2,198 → 2,114**. `kernel_fact`: −25 source uses in the default build; all 34 class-b leaves of ≥ 0.1 s listed in stage 8 (the Maj majorants, `corr_majQ`, `allNodes_res`, `nodesOK_eY`, `box_accepted`, `noProfile_rejected`) are converted.
- **Audit** (`audit_kernel_fact.py --time`, re-run on the rebuilt `TorusMaj`, `NegTorusMaj`, `FamMaj`, `KamTorusAWeightedCheck`: 120 leaves, all class a-data; the converted `MuMaj`, `BoxPert`, `SolovevBallooning` leaves are removed from the stage-8 data, as these modules were not rebuilt): default build **6,098** class-b leaves (stage 8: 6,134), **0** of ≥ 0.1 s (34), ≈ 20 s of opaque kernel time (56 s); overall 18,518 class-b leaves, 64 of ≥ 0.1 s, 33 of ≥ 1 s (all in the frozen Ew/Mu2–5 chains), ≈ 540 s.
- **Axioms:** `evalCert_finOfNat_fixture`, `evalCert_finTab_fixture`, `evalDecide_fixture`, `kron2Proof_scaled_fixture`, `wcheck_RR`, `wcheck_grid`, `gA10_check`: `propext`; `fivDecide_fixture`: none; `fixture_arctan_one`, `atanTabN_check`, `pderivZ_bounds`, `c0_oneD`, `gc_C2Z`, `allNodes_res`: standard axioms.
- **Rebuild state (important).** The builder change makes every importer of `PlasmaLeanMeta`/`Certificates.EvalCert` stale, and the `KronProof2D` change every `kron2_proof` user (the Torus/NegTorus/Mu check modules). Rebuilt and current: the certificate modules, `KamTorusAWeightedCheck` … `KamTorusAExact`, `RationalStellaratorGCTorusCommon`, `TorusMaj`, `NegTorusMaj`, `FamMaj`, `CoilsGrad`, `SolovevMercierQuadrature`, `LandremanFamily2Quad`, `LandremanFamily2Cert1`. Not yet rebuilt: the rest of the default build downstream of these, including `MuMaj`, `BoxPert`, `LandremanFamily2Cert2–7`, `SolovevBallooning`, the four `NearAxisQAAveraged*` modules, and the Torus/NegTorus/Mu check modules (204 modules, list in `.lake/stage9_stale.txt`). A `lake build` of a chain module with stale check modules starts them all in parallel (14 processes, near-thrashing on this laptop): build them one at a time in the order of `.lake/stage9_chain.txt` (`.lake/queue.sh` does this, checks `lake build --no-build` on every direct import and waits while `memory_pressure` is below 40 % free).
- **Open problems:**
  1. Rebuild the stale default-build modules one at a time (above), then re-run the audit and `#print axioms` of the top theorems (`alpha_gc_box_confined_forever`, `rationalStellarator_gc_mu_confined_forever`, `family2_mercier_stable`, `reactor_ballooning_all`, `alpha_trapped_reactorQA_averaged`).
  2. `LandremanFamily2Cert*` outer arcs (`outerArc`, 4 per cell, ≈ 135 lines): with the `oned_cert` leaves plus `atanFast`, `sinhSmall`, one arc did not finish in 10 min, even on a `(1, 1, 1)` grid, so some definition of the inner cells (`coreEval`, `zEval`, `spCell`, `cpPt`, `evenCell`) is still unfolded into a large or repeated computation. Next: profile a single `tipCell` with `eval_cert?` and add its heavy operations as leaves.
  3. `NearAxisQAAveraged`: split but not rebuilt or converted; measure the peak of each part. Converting `amp3Lit_eq` and `S3pos/neg_eq` needs `LiePoly` operations as leaves (stage 8 hit the depth limit and different values; the latter may have been the bugs fixed here), and the covers' `all_goals decide +kernel` leaves need `eval_decide` with `evalT`/`rectOK` leaves.
  4. Leaves evaluated by the builder through `Kernel.whnf` re-evaluate shared subterms of structured results (`Prod`, `List` fields): `CoilsGrad` builder time is ≈ 16 s per cover. A memoizing normalizer (or compiled evaluation where the data module is `meta`-imported) would help.
  5. As before: `nodeFin`/`famL1` leaves, the fast side `famTB − famO`, `RationalStellaratorConfinedMain`/`Cover` checks, `KamTorusACheck`/`SurrogateCheck`/`FrameCheck` (52 lines).

### Orbit existence (N-26), 30 October 2026

- **Done (default build):** a general continuation theorem `ODEGlobal.exists_global_of_apriori` (C¹ field on an open set plus a compact a-priori bound on every finite horizon gives a global solution); `Kinetic.lorentzOrbit_exists` (C¹ field everywhere: Lorentz orbits exist for all time from every x₀, v₀); for the reactor Solov'ev field (singular on the vertical axis) `reactor_alpha_orbit_exists`, `reactor_alpha_orbit_exists_label`, `reactor_alpha_born_confined` and the explicit 3.5 MeV witness `reactor_alpha_confined_nonvacuous_35MeV`. This closes audit finding MA-M2: the alpha-confinement theorems are about orbits that exist.
- **Partial:** near-QA Boozer guiding-centre orbits exist locally off the axis (`boozerGCOrbitOn_exists_local`, `reactorQA_orbit_exists_local`, `alpha_trapped_reactorQA_averaged_nonvacuous` on some 0 < T ≤ 0.19 s). Full horizon open (MA-M1); uniqueness not stated.

### Relative-entropy identity, 1-D (N-2), 30 October 2026

- **Done (default build):** `Theory/Transport/RelativeEntropy.lean`: the corrected 1-D identity pointwise (`relEnt_flux_identity`, `relEnt_pointwise_identity`, including the cross term log s·F*′ and the source term (1 − T*/T)Q) and integrated on [a, b] with explicit boundary terms (`RelEntSetup.integral_identity`, `rate_eq`: rate = −𝓕 + 𝓒 + 𝓡 + 𝓑); dissipation rate ≤ −𝓕 ≤ 0 for a constant reference and for a steady reference (`rate_le_neg_fisher_const_ref`, `rate_le_neg_fisher_steady`); the old identity without the cross term is false (`old_identity_false`, T* = 1 + x², T = 1 + x). Sanity: `Sanity/RelativeEntropy.lean`. Advances gate E6 (Q-10) for G-2 and G-7.
- **Open:** coercivity, the radial axis term, differentiating H itself under the integral, 2-D/3-D.

### Near-QA orbits on longer horizons (MA-M1, N-26), 30 October 2026

- **Done (default build):** forward continuation (`ODEGlobal.exists_forward_of_apriori`, `boozerGCOrbitOn_exists_of_region`, `boozer_bootstrap`); a two-sided band estimate for passing alphas |ψ(t) − ψ₀| ≤ D(t) ≈ 2.593 + 26.07 t T m² (`band_estimate`); existence on the full horizon for births in a band (`alpha_band_orbit_exists_short`: 2.75 ≤ ψ₀ ≤ 5.5 for 8e-4 s; `alpha_band_orbit_exists_005` with witness `alpha_band_nonvacuous_005`: 4 ≤ ψ₀ ≤ 4.3 for 0.05 s); for every birth with 0 < ψ₀ ≤ psiStart an explicit horizon of about 1.5 μs (`alpha_orbit_exists_explicit`, `alpha_trapped_reactorQA_averaged_explicit`).
- **Proved obstructions:** the band cannot reach ψ₀ ≤ psiStart because the orbit-width term exceeds psiStart (`Dpsi_gt_psiStart`), and no band survives for T ≥ 0.06 s (`band_empty_Tav`). Passing alphas born that close to the axis can reach it, so the ψ > 0 chart is the obstruction; route (iii), coordinates through the axis, would change the model statement (user decision).

### Torus Hodge identity (N-3), 30 October 2026

- **Done (default build):** `Theory/Geometry/TorusHodge.lean`: on a flat torus with constant metric (E, F, G) and modulus τ (`latticeMetric_tau`), the harmonic 1-form with periods (a, b) has energy |b − aτ|²/Im τ (`periodBound_eq`, `energy_constForm`, invariance `periodBound_shift`); every closed periodic form with those periods has energy at least this, with equality iff it is constant (`energy_ge`, `energy_eq_iff`; the cross term vanishes by periodicity). Corollaries: the field-line form has energy ≥ Φ_t′²|ι + τ|²/Im τ (`fieldLine_energy_ge`) and the current form ≥ μ₀²|G − τI|²/Im τ (`currentForm_energy_ge`). Sanity: square torus, strict inequality for a non-constant form.
- **Open:** non-constant metrics need isothermal coordinates (uniformization), not in Mathlib.

### Weak quasisymmetry and the Landreman barrier (N-27), 30 October 2026

- **Done (default build):** `Theory/Fields/WeakQuasisymmetry.lean`: `WeakQS` (Constantin–Drivas–Ginsberg Definition 1, pointwise: ξ ≠ 0, div ξ = 0, B × ξ = −∇ψ, ξ·∇‖B‖ = 0), the defect `qsDefect` (sup of ‖ξ·∇‖B‖‖; exact QS iff zero, `qsDefect_eq_zero_iff`), exact axisymmetry as a special case (`qsError_rotGen_eq_zero_of_axisymmetric`), sanity triad (`weakQS_uniform`, `weakQS_screw`, `not_weakQS_mirror`), and the axis lemma (`WeakQS.normB_const_of_gradient_eq_zero`: ‖B‖ constant on a field line where ∇ψ = 0). `Design/LandremanNotQS.lean`: `family1_not_weakQS`, `family2_not_weakQS` (and `_flux` variants): for ε ≠ 0 neither family is weakly quasisymmetric on a region containing the whole axis with ∇ψ = 0 there. Not excluded: generators vanishing on the axis.

### The stellarator contract: restructuring of the plan, 30 October 2026

- **Decision (user-approved):** the plan is restructured around the stellarator contract (section
  "The stellarator contract" near the top): C1 current-free rotational transform (‖I_tor‖ ≤ a
  bootstrap-level bound, vacuum as the limit; ι ≥ ι_min > 0 from the field), C2 omnigeneity or
  bounded ε_eff for thermal ions and electrons, C3 finite-β MHD stability, C4 existence (nested
  certified surfaces, force balance), and C5 thermal performance on the same candidate (core
  T ≥ burn threshold over [0, T_burn], below wall limits; power balance with Bosch–Hale, bremsstrahlung,
  C2-derived neoclassical losses and a supplied anomalous scaling). Rationale: tokamaks need a large plasma current, with
  current-driven instabilities, disruptions and current drive; C1 excludes them (an axisymmetric
  current-free field has ι = 0), C2 is what a stellarator needs to match tokamak confinement, and
  non-axisymmetry becomes a consequence rather than a goal.
- **Registry changes:** G-1 restated as current-free confinement (C1 + C4); G-2 as clause C5;
  G-4 as finite-β stable current-free equilibrium (C1 + C3 + C4); G-8 as the integrated candidate
  satisfying C1–C5 with common witnesses; new G-10 (omnigeneity for thermal particles, C2) and G-11 (contract
  infrastructure). New questions Q-18 (net toroidal current of the Landreman families), Q-19
  (bounce-averaged drift and ε_eff for the rational vacuum field), Q-20 (finite-β current-free
  equilibrium), Q-21 (definitions and model contracts with the sanity triad), Q-22 (thermal
  neoclassical bounds for G-2). Q-16 re-aimed at C1 + C2 with zero net toroidal current as its
  finite-β criterion; Q-1, Q-3, Q-4, Q-13, Q-14, Q-15, Q-17 re-framed. RG.5 has a new priority order.
- **Re-labels:** Solov'ev results are a tokamak model for G-2; Q-17 and the Grad counterexamples
  are mathematical infrastructure; the rational vacuum field satisfies C1 (current-free,
  KAM-certified torus with ι ≈ 0.137), C2 unknown.
- **Finding recorded while restating (no new Lean):** for Landreman family 2 the compiled
  `torCurrent_eq`, `F1_pos` and `Eint_pos` give I_tor > 0 for every 0 < k₀ < 19/20, so family 2
  carries net toroidal current (positivity corollary not yet a named declaration; Q-18).
- **Specifications:** contract entries `CurrentFreeTransform`, `BounceAveragedDrift`,
  `Omnigenous`, `EffectiveRippleBound`, `ThermalPerformance` added to `notes/formalization/00-model-contracts.md`
  (normative, not yet in Lean). README rewritten to state the aim as the contract and to describe
  progress against C1–C5. No Lean file changed; no verified result or declaration name changed.
