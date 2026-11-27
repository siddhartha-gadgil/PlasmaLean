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
| **C1. Current-free rotational transform** | The net toroidal plasma current vanishes or is small: ‖I_tor‖ ≤ I_max, a stated bootstrap-level bound (vacuum, J = 0, is the limiting case); and each confining surface is an embedded invariant torus on which the magnitude of the field's rotational transform is at least ι_min > 0 | Excludes tokamaks: an axisymmetric current-free field has ι = 0 (its field lines do not rotate poloidally), so it confines nothing. Admits vacuum stellarator fields |
| **C2. Omnigeneity / small neoclassical transport for thermal particles** | For thermal ions **and electrons** (not only 3.5 MeV alphas): the bounce-averaged radial drift of trapped particles vanishes (omnigeneity) or is bounded by a stated amount, or the effective ripple ε_eff is bounded on the confining surfaces **Band form (allowed since 23 November 2026, user decision):** alternatively, for stated species, energy and pitch ranges and a stated birth band of phase space, a certified bound keeping the orbits within a stated radial range through a stated time (N-51). It is weaker than omnigeneity and must state its band, time and model | Quasisymmetry and quasi-isodynamic fields are special cases. An axisymmetric field is automatically omnigenous; a generic 3-D field is not. C2 is what a stellarator needs to match tokamak neoclassical confinement |
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

**Where the project stands against the contract (31 October 2026, honest summary; after the
refresh audit).**

- **C1:** partial, vacuum only.
  - The exact rational stellarator field is a vacuum field (`RationalStellarator.field_vacuum`),
    and a KAM-certified exact invariant torus with ι ≈ 0.137 confines its field lines for all time
    (`rationalStellarator_confined_forever_exists`).
  - The exact Dommaschk NFP-3 field is a vacuum field (`DommaschkQA3.candidate_vacuum`). Its
    certified tori and ι are open.
  - **Audit fix AR-H1/AR-M1 (31 October):** C1 now bounds the Ampère circulation μ₀⁻¹∮B·dl
    around each torus's own poloidal loop (`loopCurrent`, `SurfaceData.current`). The loop must be
    C¹ with B continuous on it and μ₀ > 0, and the transform clause is ι_min ≤ |ι|. The earlier
    section clause was vacuous; regression `Sanity/AuditRefreshContract`
    (`rotY_not_currentFreeTransform`).
  - Witnesses through potentials (`currentFreeTransform_of_potential`):
    `rationalStellarator_currentFreeTransform` and `DommaschkQA3.candidate_currentFreeTransform`.
    The second reduces C1 to certifying tori.
  - **Landreman family 2 fails C1** (`family2_not_currentFreeTransform`: for families containing a
    surface whose poloidal loop is the family-2 loop in its given parametrisation), via the Stokes theorem
    for regular sections `netToroidalCurrent_eq_lineIntegral_div` (`Theory/Contract/SectionStokes`)
    and `family2_loopCurrent_pos`.
- **C2:** partial, in the Boozer guiding-centre model.
  - Omnigeneity (`OmnigenousOn`: exact return of the flux label after each bounce, stronger than
    leading-order omnigeneity, AR-M2) and the bounce-averaged drift are defined.
  - QS ⇒ omnigeneity is proved exactly and per bounce (`omnigenousOn_of_exactQS`,
    `approxOmnigenousOn_of_defect_le`).
    - For `exactQA`/`reactorQA` no trapped bounce is constructed (AR-M3); non-vacuity is the
      `driftMirror` fixture.
  - ε_eff is not in Lean.
  - Neither Landreman family is weakly quasisymmetric on a region containing its magnetic axis
    (for potentials critical on the axis: `family1_not_weakQS`, `family2_not_weakQS`).
  - The rational field's QA defect is a fixed fraction of its first-order variation
    (`rationalStellarator_firstOrder_not_QS`, first order, linearised angles, N = 2).
  - Alpha results are for one species, mostly passing orbits.
- **C3:** Landreman family 2 has a certified Mercier-stable band (`family2_mercier_stable_derived`;
  the Mercier index is supplied) and ballooning reduced to one certificate (Q-3). The family
  carries net section current. The Solov'ev stability results are tokamak results. Nothing at
  finite β for a current-free candidate.
- **C4:** the vacuum fields inside their certified torus. At finite β, only the Landreman families
  and the symmetric models.
- **C5:** shown only for a tokamak model: on the Solov'ev field, for every supplied solution of the
  radial transport model starting in a certified band, the core stays ≥ 10 keV for all time
  (`solovev_one_plasma_actual` and variants; the transport solution is assumed, pressure bounded
  by a budget). On stellarator parameters there are only 0-D windows and proved obstructions at
  measured renormalisation factors (Q-13).

**Update, 23 November 2026 (assessment against the contract; the summary of 31 October above is
kept as history and is out of date where the two differ).**

- **C1 is proved with embeddedness on every Q-36 example.** The rational stellarator has zero
  loop current and transform (75 + √5)/562 on its exact torus A
  (`rationalStellarator_embeddedCurrentFreeTransform`). On the Dommaschk NFP-2 field the exact
  tori C and A are embedded, disjoint and ray-ordered, with zero loop current and |ι| ≥ 0.2386
  on both (`dommaschk_nested_embedded_C1`, on demand). The result covers these individual
  surfaces. A foliation of the intervening volume remains open. For curl-free fields the current
  clause carries no information on a convex cross-section (`CurrentFreeTransform.imax_zero_of_convex`),
  and the circulation is independent of toroidal angle (`FieldTorus.poloidalCirculation_eq_of_curl_eq_zero`).
- **C2 remains open on a physical candidate.** On the same embedded Dommaschk surfaces the
  certified off-QA spectral defect is at most 0.0063 |ι| on C and 0.0090 |ι| on A
  (`dommaschk_Q16_embedded`). Untrusted numerics for the same field: defect ≈ 0.002 |ι|
  and ε_eff ≲ 0.04 % (N-31). The Lean clause `OmnigeneityContract` asks for a Boozer chart of the
  field on a region (`BoozerModelOf`); its only instance is vacuous (audit AV-M7), and a chart over
  a volume is not available for a non-integrable field with two certified tori. The bridge Q-23
  is in the Boozer guiding-centre model with orbits and bounces supplied. N-51 (23 November)
  proves second-order confinement on an annulus of periodic orbits in phase space; it needs no
  chart of the field over a volume, but no physical band has been constructed, and its
  hypothesis (averaged drift tangent to both edges) is of the same kind as what C2 asserts.
  N-56 externally bounds the field and flux on all launches of one candidate strip and continues every field line through ±1/8 radian below both mirror heights. N-57 externally encloses the two simple mirrors and a unique height at the prescribed action on a small cell. N-59 has two radial face inequalities on six phase sectors. N-60 encloses two continuous fixed-action root arcs on each of the two symmetry sectors, separated by more than 0.045 in launch radius. Global winding, physical time and thermal population coverage remain open. By user decision (23 November) C2 may be met in the band form as well as in the chart form.
- **C3, C4 at finite β:** There is no current-free finite-β candidate
  (Q-20); N-44 gives a verified cylinder gap under mode-multiplier hypotheses. N-55 rules out its first-order pressure-step criterion on Dommaschk torus A.
- **C5:** unchanged: tokamak model and 0-D windows only.
- **Balance of recent work.** Between 2 and 23 November the compiled additions were
  infrastructure (the form kernel and its links to TauCeti, N-48; the annulus theorem, N-51) and
  assessments of source notes (N-36–N-47). On 23 November N-52 supplied a general embedding
  theorem and established the strengthened C1 on the rational stellarator and the Dommaschk tori.

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
| `G-1` | **Current-free confinement (C1 + C4)** (restated 30 October 2026): for one candidate, a field with net toroidal plasma current ‖I_tor‖ ≤ I_max (vacuum as the limiting case), nested certified invariant tori on a confining region, each with rotational transform of magnitude at least ι_min > 0 provided by the field; field lines (and guiding centres, with the reduction named) stay inside. *Superseded meaning (legacy G1, 29 October):* "confinement and stability for one candidate", which counted symmetric and tokamak models; stability is now G-4 (C3) and omnigeneity G-10 (C2) | supported by G-5, G-6, Q-16, Q-18, Q-19, Q-21; supports G-8 | active (partial, vacuum) | Satisfies C1 + C4 in vacuum on one torus: `RationalStellarator.field_vacuum` (J = 0), `rationalStellarator_confined_forever_exists` (all-time field lines inside a KAM-certified exact torus with Diophantine rotation number ι ≈ 0.137); C2 unknown (Q-19). Guiding centres: `alpha_gc_passing_confined_forever`, `alpha_gc_confined_forever_robust`, `alpha_gc_confined_forever_pm` (passing alphas, Littlejohn model supplied). *Not candidates under C1:* the Solov'ev results (`reactor_alpha_born_confined`, `reactor_ballooning_all`, `reactor_mercier_stable`) are tokamak models, kept for G-2 and as technique test beds; `stable_uniform` (screw pinch) is a model problem. The Dommaschk pair has a common certified lower bound on the magnitude of ι. A finite-β current-free equilibrium is still needed. *Scope (N-36, claim 7):* zero net toroidal current does not mean j_pl = 0 and does not exclude local current-driven modes at finite β (a C3 question). 20 November: harmonic perturbations of the Dommaschk seed keep two nested tori (N-42 S-10, KAM persistence, unquantified; Q-32). Q-34 (N-50) screens a boundary deformation of the vacuum seed. **23 November 2026.** N-52 proves embedded C1 for the rational stellarator torus A and the exact Dommaschk tori C and A, individually and as the nested Q-16 pair. C4 over a region and physical trapped-particle confinement require additional results. |
| `G-2` | **Thermal performance = contract clause C5** (legacy G2, restated 30 October 2026): on the same candidate that satisfies C1–C4, core temperature above a burn threshold (e.g. T ≥ 10 keV) over [0, T_burn] (or forever) and below wall and material limits, from power balance with Bosch–Hale alpha heating, bremsstrahlung and transport losses; neoclassical losses from C2 (Q-22), anomalous transport a stated supplied scaling (ISS04 or an Â bound). C2 couples into C5: poor omnigeneity (large 1/ν losses) can make burn inaccessible (Q-13) | supports G-8; supported by Q-10, Q-13, Q-15, Q-22, G-10 | active (tokamak model and 0-D only) | `m1_burn_window` (0-D), Stellaris ISS04 window (`Design/BurnWindowStellarator`), `solovev_one_plasma_actual` (two-sided band for every supplied transport solution, pressure budget; **a tokamak model**: the Solov'ev field is axisymmetric and current-carrying, so this is a model for G-2, not a candidate). Needed: barriers on stellarator geometry with χ bounded by C2 (Q-15, Q-22), existence of the transport solution *4 November 2026 (N-36, N-38):* a maintained burn also needs a stable burn point (G′(T*) < 0, Q-26 a) and, for "forever", fuelling and ash removal (finite fuel forbids sustained burn, Q-26 b); compiled results assume full prompt alpha deposition and Maxwellian fuel (AK-1, AK-2); kinetic yield bridge Q-26 c, produced turbulent flux Q-28. |
| `G-3` | **Model adequacy and probabilistic goals** (§12): quantify one omitted effect on a design observable (N1), activation rules (N2), decision infrastructure (N3); probabilistic loss and uncertainty (P1–P4) | supports G-1, G-2, G-8 | proposed | none in Lean; specifications in `notes/goals/`. P1 can weight the complement of an N-49 retained band by birth energy. |
| `G-4` | **Finite-β stable current-free equilibrium (C1 + C3 + C4)** (restated 30 October 2026): an exact or validated finite-pressure equilibrium with net toroidal current ‖I_tor‖ ≤ I_max and ι ≥ ι_min > 0 from the field, with certified Mercier, ballooning and interchange stability at a stated β > 0 (reductions named). *Superseded meaning (Phase 14):* "a stable non-axisymmetric finite-β equilibrium", which did not constrain the current | supports G-8; supported by Q-3, Q-14, Q-18, Q-20 | active (no current-free candidate) | Landreman family 1 force balance and `family1_mercier_unstable` (negative); family 2 `family2_mercier_stable_derived` (band k ∈ [0.7, 0.9], λ = 200, Mercier index supplied); ballooning reduced to one certificate (`family2_stable_of_cert`, `family2_stable_of_secular_cert`). **Both families carry net toroidal current** (family 2: μ₀ I_tor/2π = `curK` > 0 by `torCurrent_eq`, `F1_pos`, `Eint_pos`; Q-18), so they are C3 technique test beds, tokamak-like under C1 unless that current is bootstrap-level. Needed: a current-free finite-β equilibrium (Q-14 stepped pressure across the rational field's torus; or a finite-β Dommaschk/QA equilibrium) and then C3 on it; Q-3 stays useful as technique 20 November: signed cylinder benchmark and toroidal interface criterion (N-44, Q-30, Q-31; cylinder algebra verified). N-55 rules out the N-44 sign test on A. A new interface or a total-energy estimate is needed before screening current and transform at a common step. |
| `G-5` | **Coil-produced confinement** (Phase 13): field lines of the field of a concrete coil set confined for all time (or a long certified horizon) | supports G-1, G-8 | active (all-time: blocked, research) | `coil_stellarator_confined_concrete_N` (52 transits, field-line existence assumed). Needed: Q-2 |
| `G-6` | **Robust alpha confinement** (Phases 11–12): all-time confinement of 3.5 MeV alphas on physically meaningful energy, pitch and B₀R₀ ranges, passing and trapped. Under the contract the trapped part is the alpha component of C2 (G-10) | supports G-1, G-10 | active | `alpha_gc_passing_confined_forever_quarter` (on-demand; λ ∈ [0, 1/4], one energy and B₀R₀), `alpha_gc_confined_forever_energy_window` (on-demand; ±0.4 eV × λ ∈ [0, 1/16]), `alpha_trapped_reactorQA_averaged` (passing, near-axis QA, 0.19 s). Needed: Q-1, Q-4, Q-5 20 November: full-orbit weak-QS corrector and absorbing-core certificate (N-43, Q-29; lean-ready). N-49 proposes a finite-time momentum bound on a regular trapped band. N-51 proves second-order confinement in normalized phase coordinates for an annular space of regular bounce orbits. N-58 gives a finite-time two-face test conditional on a physical action budget. N-93 quantifies the geometric action error on neighboring curves with controlled tangent components. On QA2R, N-116 bounds the dimensionless first-well flight time and N-117 gives open sets of eligible births for compatible cuts. To reach robust alpha confinement, obtain a quantitative radial excursion and survival time on a specified birth population and physical operating envelope. |
| `G-7` | **Verified plasma evolution** (§11): for one candidate, a certified interval on which the selected plasma model exists and stays within error, stability, thermal and geometric bounds | supports G-8; supported by Q-7–Q-11 | proposed (E1 done) | E1: `lieBracket_gradient_of_contDiffAt`, `quasisymmetry_not_pde_symmetry`; conditional `riccati_le_initial`. Needed: gates E2–E8 *4 November 2026:* additive-residual inward-radius lemma and norm-to-observable step (Q-27, N-39). |
| `G-8` | **Integrated stellarator candidate (C1–C5 with common witnesses)** (restated 30 October 2026): one decoded candidate satisfying C1 (current-free ι ≥ ι_min), C2 (omnigeneity or a bounded ε_eff for thermal ions and electrons), C3 (finite-β stability), C4 (nested surfaces, force balance) and C5 (thermal performance, G-2) with the same witnesses, then coils and engineering margins (M6, §11.1). *Superseded meaning:* "coils, equilibrium, stability, transport and engineering margins on one candidate" without the C1/C2 filters | supported by G-1, G-2, G-4–G-7, G-10, G-11 | open | `Bridge/Contracts` (common-witness composition) only *4 November 2026:* acceptance criteria and rejection tests from the kinetic/coil brief in `notes/goals/README.md` (N-22, N-36); a finite-horizon maintained-state goal is recorded there as a proposal only (user decision). N-69 assesses the five conditions on the same candidate and prioritizes C2 and the first pressure deformation. N-210 records how the complete local C2 well certificate and its drift hypothesis affect the five conditions. |
| `G-9` | **Auditable certificates within the laptop budget** (Phases 15–16, auxiliary): every concrete check an explicit certificate, ≤ 6 GB per Lean process, no `decide` of any kind | supports all | active | Certificate tactics in `PlasmaLean/Certificates/`; workstation pipeline. Needed: Q-6, Q-12 |
| `G-10` | **Omnigeneity for thermal particles (C2)** (new, 30 October 2026): on the certified surfaces of a current-free candidate (G-1), the bounce-averaged radial drift of trapped thermal ions and electrons vanishes (exact omnigeneity) or is bounded by a stated amount, or ε_eff ≤ ε_max (a stated value, e.g. the W7-X level of about 1 %); quasisymmetry and quasi-isodynamicity are admissible special cases | supports G-8, G-2 (via Q-22); supported by Q-16, Q-19, Q-21, Q-1 | open for C2, positive trapped reference proved on QA2R | The phase-zero QA2R pilot at u=0.470 has regular first mirrors throughout the closed height band on actual field lines between a common nested pair of tori (N-95–N-100, N-110). All 31,200 original cells prove the first upper-height action comparison (N-101). The joint one-way time lies between 54.98668 and 264 throughout the band (N-116). Height differentiation and inversion are proved in N-104 and N-113. N-114 and N-117 prove positive Cartesian position-height volume and positive trapped-reference mass for compatible support, energy and pitch cuts on each parallel velocity sign. N-122 and N-125 give both signs actual guiding-centre orbits within any positive excursion cap on one common positive local time, with a positive covered fraction for a measurable finite reference and open-positive law. N-130 puts the full 391-row pilot calibration and all eight launches on the same nested embedded tori, including 64 rows each way at u=0.478. N-131 also attaches submirror segments at u=0.523 and 0.531 on the same embedded geometry. N-115 supplies local mirror brackets for u=0.478. N-121 puts all 634 incoming tubes below the lower height and attaches the first 64 each way to the birth. N-127 verifies the ten outer slopes on each side and proves that a joined path reaching the brackets has a full branch of first roots across the band. Next extend the incoming chain to the turning brackets, verify the other seven action comparisons from N-82, and control transverse action variation using N-85, N-87, N-88, N-93 and N-118. A numerical thermal fraction, radial transport estimate and dimensional operating point remain open. N-133 gives a physical interval below mirror strength at each of the four opposite-section births. N-134 reduces the second-radius upper-height action target to the inner 322 signed row pairs. N-136 joins the calibrated pilot and the second original birth, with both profile comparisons through ±5/16 radian. N-138 integrates 1,536 contiguous signed panels on the same actual second-birth line. N-141 grounds the quantified submirror clearance on the 160-pair physical birth trace. N-139 reduces the eight action packets to 67,928 physical enclosure obligations. N-142 grounds a 3,072-panel lower action over a positive height interval at the second birth. N-143 closes the full 89-index outer suffix of the signed two-radius comparison. N-144 joins the two original field lines throughout ±1 radian and proves the secant criterion for their true first wells. N-140 grounds the first coarse action intervals for all four opposite-section births on one pair of tori. N-145 raises the grounded near-upper action floor to 8/25 on the actual 192-pair second birth trajectory. N-148 grounds the 16-panel second-radius launch and proves its physical first-well implication. N-147 gives one positive position-height neighborhood radius along the whole central pilot arc at all band heights. N-146 verifies the two-radius field and arclength comparison on every tube through the last pilot mirror slab. N-150 gives uniform local guiding-centre control on whole compact families of physical trapped births. N-149 attaches the two-radius evidence to both physical births throughout ±3.5 radians and proves a positive interior action bound at the second. N-152 checks signed ODE continuation using shared field derivatives on consecutive physical trial tubes. N-154 proves one local guiding-centre time across all admitted pilot launch phases and their full central arcs. N-158 gives strict physical field clearance on three actual original births alongside the calibrated pilot on the same embedded tori. N-157 admits both original signed frames at the opposite section and provides a bounded continuation campaign beyond each exterior cap. N-156 puts the second physical line above the archived absolute action target at the upper height. N-161 checks the two-line action variation on the original physical births. N-159 bounds the height measure of shallow first mirrors from bracket widths alone. N-160 proves common local guiding-centre control simultaneously on two radial families of physical births. N-162 gives an upper-endpoint radial action secant above 1/2 on the same two physical lines. N-163 supplies a faster checked signed continuation method for the opposite section. N-153 verifies the physical mirror cap data at the four opposite-section launches. N-151 verifies lower first-mirror branches conditional on continued passages at the two outer phase-zero labels. N-155 checks the complete incoming field clearance at every opposite-section endpoint. N-165 gives an equal-height first-well action separation across the entire closed mirror-height band. N-164 applies the area estimate to an actual smooth QA2R field line and to all four opposite-section signed through-passage hypotheses. N-166 accelerates the physical continuation checks at the other two phase-zero radii. N-167 isolates grazing of the first mirror as the only way a capped connected family can miss a bracketed action. N-168 proves normalized probability bounds for height sampling on the second actual line and under a specified change of height law. N-170 enables grouped original signed continuations at all four opposite launches. N-169 supplies the continuum of true initial launches and all eight cap signs. N-171 derives joint continuity and physical endpoint identification on the candidate radial interval. N-174 attaches eight physical signed traces totaling 1,998 slabs to the same tori. N-173 supplies the first 64 widened-tube central ODE defects and a resumable verifier. N-176 identifies the actual interior torus birth at each admissible phase from four universal section checks. N-175 supplies signed physical continuation for every initial point in all four widened balls. N-172 verifies outward growth of squared field strength on every candidate mirror tube. N-177 speeds the central and spatial checks without changing any physical tube or rational budget. N-178 proves joint continuity of the original first mirrors and action on the launch rectangle from the four section checks. N-179 proves the original birth lies in the accessible component of the zero section on every intermediate radius. N-181 discharges all remaining field signs and contact derivatives conditional only on through-going signed trajectories. N-180 proves a connected target level can be selected across the whole phase rectangle without a radial derivative bound. N-182 transfers strict face signs to any full regular field family on the same certified tori. N-183 reduces the candidate sector attainment theorem to the four original through-going trajectories. N-184 obtains one connected set of true birth-centered target wells from the four signed trajectory checks. N-187 reduces the cost of each physical Jacobian proof and measures the limits of cross-radius reuse. N-185 proves a connected essential action level under full-period face bounds. N-186 certifies the signed collars and normalized one-way flight-time bounds over a closed height interval. N-188 gives quantitative action slack of 1/250 for the connected-sector theorem. N-193 extends the common original eight-launch family to 2,590 genuine signed slabs. N-190 identifies the opposite sector where the narrow fixed action strip fails in directed arithmetic. N-189 accelerates the original long signed endpoints with independently checked matrices on each label. N-192 proves connected first-well levels for a quantitative rectangle of prescribed height and action. N-191 supplies an unconditional quantitative passing window on all original launch radii. N-196 verifies original-birth accessibility over two phase sectors of total width 1/8 radian on the wide radial interval. N-194 verifies a common normalized parallel travel time and unique positions for every original radial-sector birth. N-199 gives a quantified first radial exit criterion from actual endpoint actions independently of the long family of intermediate trajectories. N-197 schedules the prerequisites of the four physical trajectories together without increasing measured CPU use. N-195 proves a positive-core action obstruction with exact quadrature and binds the singleton birth to its original tori. N-198 verifies original-birth accessibility across the full phase period on the wide radial range. N-200 gives common signed travel time at least 1941503/1048576 in each direction for the original small-sector births. N-201 relates approximate action targets to uniformly positive radial sampling mass in every admissible phase-height fiber. N-202 verifies the outer-face action derivative and near-upper response independently of any intermediate radial path. N-204 initiates the original opposite-section singleton's signed physical trace and action proof. N-205 closes the entire physical through-cap hypothesis. Connected first-well actions and uniformly positive radial sampling windows now hold unconditionally in the original phase-zero sector (in the script-generated on-demand library `QA2RGenerated`, built and axiom-checked from the repository). N-203 gives a quantitative actual submirror field-line interval around every original wide-strip birth at every real launch phase. N-206 extends the two-face exit test to varying height with a closed action budget of 249/250000. N-210 separates the proved local well structure from the dynamical estimate still needed for thermal C2. N-207 joins the original u=0.523 path to both full-height first-mirror branches at its section. N-212 gives a topological and a first-exit route for a strip with phase-dependent radial faces. *Audit of 25 November 2026:* the C2 results above are field-line statements; band-form instances with an existential horizon (N-125) carry no confinement content (AW-H3). |
| `G-11` | **Contract infrastructure** (new, 30 October 2026, auxiliary): kernel-level definitions of net toroidal current, rotational transform of the field on a family of tori, bounce-averaged radial drift, omnigeneity and ε_eff, each with the sanity triad, and a `StellaratorContract` record composing C1–C5 on a common witness | supports G-1, G-4, G-8, G-10 | active (C1 and C2 predicates in Lean; ε_eff, C3–C5 predicates and the composed record open) | specifications in `notes/formalization/00-model-contracts.md` (C1, C2 in Lean: `Theory/Contract/StellaratorContract`, `BoozerModel`; the rest not yet); adjacent compiled pieces: `torCurrent` (family 2), `iotaK`, `WeakQS`. Needed: Q-21 **23 November 2026.** The embeddedness clause and the reusable theorem `CurrentFreeTransform.embedded_of_irrational` are in Lean. Every Q-36 example now satisfies `EmbeddedCurrentFreeTransform`. `GuidingCentreBand` implements the band form for the static Littlejohn model, with positive reference mass and finite-time control of every partial orbit. Candidate instantiation is open. |

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
| `Q-1` | All-time (or slowing-down-time) confinement of **trapped** 3.5 MeV alphas in near-QA: can the per-bounce remainder (phase shear) be bounded? *Re-framed (contract, 30 October 2026):* this is the alpha component of C2; the per-bounce radial kick is the single-orbit form of the bounce-averaged radial drift, so the definitions of Q-21 and the thermal-particle question Q-19 come first, and a bound here should be stated as an omnigeneity defect | G-6, G-10, N-17 | open (research, parked) | Compiled: `reference_kick_osc` (kick amplitude ≤ 0.0816 T m²), `exactQA_kick_osc`. Barrier: one-bounce remainders (Lipschitz–Grönwall hopeless, `e^{KP} ≈ e^{29000}`), shears, validated bounce-time enclosure, existence of re-anchored references (`trapped-alpha-status.md` §3); re-anchoring with absolute amplitudes cannot close (Phase 11 part 1). N-49 tests whether the leading bounce mean obstructs a periodic correction. N-58 gives a finite-time two-face test conditional on a physical action budget. N-60 supplies a local geometric input on two sectors. Physical time and alpha birth coverage remain open. For QA2R, N-116 supplies a dimensionless first-well time between 54.98668 and 264 throughout the pilot band. N-117 supplies positive reference mass for compatible cuts. The actual radial kick and its cumulative error over successive bounces remain open. |
| `Q-2` | **Coil-produced all-time confinement**: can a KAM torus refitted to `tfField + polyCoilFieldC` meet the smallness budget? | G-5, N-16 | blocked (research) | On-demand `CoilKamCert` proves only a vacuous residual bound (≈ 10⁹ against ≈ 10⁻³⁰ needed). Barrier: sharp cancellation-aware complex sup bound, torus-adapted neighbourhood, anisotropic strips, high-precision refit (≈ 4 CPU-days estimated) |
| `Q-3` | **Family-2 ballooning certificate**: one pointwise inequality on surface × ℝ for Landreman family 2 on the Mercier-stable band. *Re-framed (contract):* family 2 carries net toroidal current (Q-18), so this is a C3 technique result on a tokamak-like test bed, not a stellarator candidate; lower priority than C1/C2 work, but the checker transfers to a current-free equilibrium | G-4 (technique) | open | Reduction compiled (`family2_stable_of_cert`, `family2_stable_of_secular_cert`); numerics stable (tail margin ×2.36–×9.39); linear-in-s certificates fail, the B-spline × rational basis fails the dense check at k = 0.9; checker not written (≈ 8,000 boxes per surface, 100–200 CPU-h for the band search) *17 November 2026: evolutionary-search route proposed (N-41).* |
| `Q-4` | **Wider energy window** (±3 eV, then ±1 %) and a joint B₀R₀ range, with λ up to 1/4. *Re-framed (contract):* passing alphas in the vacuum rational field are a C1-compatible particle result; it does not address C2 (trapped and thermal particles), so it ranks after Q-19 and Q-21 | G-6, N-14 | open (workstation route) | Compiled (on-demand): ±0.4 eV × λ ∈ [0, 1/16]. Barrier: the torus family moves ≈ 30·Δρ; needs re-certified low-resolution chains with larger admissibility balls, ≈ 3 / ≈ 10 CPU-h (`energy-window.sh`) |
| `Q-5` | Passing confinement **beyond λ = 1/4** | G-6 | open | λ = 1/4 is the limit of the passing argument with ‖B‖ ≤ 3B₀ (`quarter_passing_margin`); needs a sharper ‖B‖ bound or another argument |
| `Q-6` | **Landreman `outerArc` certificates**: explicit certificates for the ≈ 135 `outerArc` lines of `LandremanFamily2Cert1–7` | G-9, G-4 | done (30 October) | All 136 outerArc checks in `LandremanFamily2Cert1–7` converted to `f2_arc_cert` (shared module `LandremanFamily2ArcCert`); Cert2/5/6 split (Cert2b/5b/6b) to stay ≤ 5.5 GB; CPU 1.43× (≈ 2025 s); peaks 3.5–5.2 GiB; `family2_mercier_stable(_derived)` on standard axioms; default-build `decide +kernel` lines 266 → 130 |
| `Q-7` | **E2–E3**: Pizzocchero–Tassi Proposition 4.3 on the periodic benchmark, then a certified trajectory with full residual enclosures | G-7, N-19 | open | not started in Lean (§11.3 is the first target) |
| `Q-8` | **E4**: toroidal-domain continuation (harmonic flux sectors, Hodge coercivity, Kozono–Shimizu–Yanagisawa small data) with a nonempty admissible set | G-7, N-19 | open | not started |
| `Q-9` | **Helical MHD regularity** (§1.3): a theorem, with hypotheses, for the helically symmetric reduction; the Riccati inequality dY/dt ≤ −νY + CεY² for MHD (R3) | G-7, N-19 | open (research) | Only the conditional comparison is compiled (`riccati_le_initial`, `riccati_exp_decay`); the inequality is a hypothesis |
| `Q-10` | **E5–E6**: existence/continuation for the radial transport model; a steady pressure-matched state (pressure equality, not a budget); the corrected relative-entropy identity with all terms | G-2, G-7, N-2, N-6 | open | Transport solutions are supplied in `solovev_one_plasma_*`; the relative-entropy identity is proved informally (N-2), not in Lean |
| `Q-11` | **E7–E8**: compatible numerics (constrained transport, admissible states) and integration on a shared candidate | G-7, G-8 | open | not started; E8 needs the earlier gates |
| `Q-12` | **Phase 16 remaining opaque leaves**: replace the remaining `decide +kernel` and opaque `kernel_fact` leaves within ≤ 6 GB and the olean budget | G-9 | active | §13 stage 9: 297 default / 2,114 overall lines with `decide +kernel`; 6,098 class-b `kernel_fact` leaves in the default build (0 of ≥ 0.1 s); `decide_cbv` in on-demand Mu3–Mu5 Adm; open: `NearAxisQAAveraged` parts, the fast side `famTB − famO`, `nodeFin`/`famL1` leaves, `KamTorusACheck`/`SurrogateCheck`/`FrameCheck` *17 November 2026: evolutionary-search route proposed (N-41).* |
| `Q-13` | Is the 0-D / 1-D burn obstruction at nominal confinement removable by profile peaking on stellarator geometry (ISS04 needs f_ren above measured values)? *Contract (C5):* this is the C5 obstruction for supplied anomalous scaling; with Q-22 the same question must be asked with C2-derived neoclassical losses added (poor omnigeneity can make burn inaccessible) | G-2 (C5), N-5 | open | Proved obstructions: `stellaris_measured_fren_no_access_steady`, `stellaris_measured_fren_no_access_loss`; the 1-D route on stellarator geometry is Q-15 *17 November 2026: evolutionary-search route proposed (N-41).* |
| `Q-14` | **Stepped pressure across the exact KAM torus** (Phase 14 route A): a finite-β equilibrium glued across the certified torus of the rational field. Under the contract this is the lead route to Q-20 (current-free finite β), provided the net toroidal part of the sheet currents is controlled | G-4, Q-20, N-12, N-13 | open (lead) | plan only (`after-kam.md` §3, `finite-beta-stellarator.md`) |
| `Q-15` | Transport barriers (T ≥ 10 keV in the core) on a **non-axisymmetric** validated geometry, with χ bounds from Â or neoclassical theory stated as supplied scalings; under the contract the geometry should satisfy C1 and the neoclassical χ comes from C2 (Q-22) | G-2, Q-22 | open | Barriers exist on the cylinder, helical and Solov'ev geometries only |
| `Q-16` | **A quasisymmetric solution** (*2 November 2026: **vacuum criterion met on a nested pair** of certified tori of the Dommaschk target, `DommaschkKamQ16.dommaschk_Q16_vacuum` (C1, |ι| ≥ 0.2386, strong-tier certified QA defect ≤ 0.009 |ι| on both); C2 open*), *re-aimed at C1 + C2 (contract, 30 October 2026)*: the target is a current-free field with ι ≥ ι_min > 0 (C1) that is omnigenous in the quasisymmetric form (C2). The decided vacuum criterion below already fits the contract (vacuum ⇒ I_tor = 0; ι ≥ ι_min; small ε_QS relative to ι). The finite-β criterion is now decided by the contract: **zero (bootstrap-level) net toroidal current**, ‖I_tor‖ ≤ I_max, replacing the alternative non-Killing bound on ξ. Decided criterion (user, 30 October 2026), vacuum version: an explicit or validated **vacuum** field with certified invariant tori on a nested region, rotational transform ι ≥ ι_min > 0 on them, and a certified quasisymmetry defect ε_QS small **relative to ι** (both numbers reported; in vacuum an axisymmetric field has ι = 0, so ι ≥ ι_min excludes trivially near-axisymmetric fields). The finite-β version needs a separate criterion (plasma current gives ι > 0 to near-tokamak fields): zero net toroidal current or a non-Killing bound on the generator ξ, to be decided | G-1, G-10, G-4, G-6 | open (research); the strong form (exact QS in a volume) is open mathematics | See N-27. Exact QS on a volume: neither existence nor non-existence is known (Constantin–Drivas–Ginsberg, arXiv:2009.08860; Burby–Kallinikos–MacKay, arXiv:1912.06468). Route (i), near-axis remainder, not recommended (the vacuum expansion is ill-posed without regularization, Ruth–Jorge–Bindel arXiv:2411.04352). Route (iii) negative: QS with a generator nonvanishing on the axis forces constant ‖B‖ on the axis, and both Landreman families have non-constant axis ‖B‖ for every ε ≠ 0 (compiled: `family1_not_weakQS`, `family2_not_weakQS`). Recommended: route (ii) as an explicit vacuum field (finite Dommaschk sum fitted to a QA target, exact by identity) + KAM-certified invariant tori + Boozer angles by one more cohomological equation + certified non-QS ℓ¹ part of ‖B‖. Criterion decided: vacuum version as stated (ratio form). The strengthened vacuum statement `dommaschk_Q16_embedded` keeps the same tori, sharp bounds and chart hypotheses. N-101 proves that the upper-height action at u=0.470 is below its target for every admitted birth angle. Physical C2 remains open. The QA2R pilot has a full 782-slab trace and a complete upper action comparison (N-110, N-101). N-115 locates the local mirror brackets at the next radial label. |
| `Q-17` | **A Lean statement of a Grad counterexample** (*re-labelled, contract 30 October 2026: mathematical infrastructure, not design progress*; non-symmetry is a consequence of C1, and both Landreman families carry net toroidal current, Q-18): for Landreman family 1 (and family 2), one theorem giving smooth fields on a toroidal domain with nested toroidal flux surfaces, non-constant pressure, force balance, and no continuous Euclidean symmetry (axial, helical or reflection); then the non-stellarator-symmetric τ-extension of Issan–Citrin–Landreman–Tracey (arXiv:2610.07304) | G-4, N-28 | family 1 verified (`family1_grad_counterexample`); family 2 and τ-extension open | `family1_grad_counterexample`: smooth B, J, p on 𝒰; ∇·B = 0 and force balance with the gradient of p = (2δ − 2ψ)/μ₀; ψ a first integral with compact nested sublevel sets, each level set ψ = c ∈ (0, δ] homeomorphic to Circle × Circle (`torusMap`); p non-constant; no rotation, translation or screw-motion symmetry (`killing_trivial_of_axis`); contrast `axisymmetric_limit_lie_zero` at ε = 0. Not covered: plane reflections; family 1 has ι ≡ 2 (closed field lines), so family 2 (sheared ι) is the stronger target |
| `Q-18` | **Net toroidal current of the Landreman families** (contract C1): compute I_tor(ψ) for families 1 and 2 and compare it with the field-producing current (B₀R₀·2π/μ₀) and with a bootstrap-level bound. If it is not small, the families are tokamak-like under C1 (ι comes from plasma current) | G-1, G-4, Q-16, Q-17 | answered for family 2: fails C1 (re-established 31 October with the intrinsic loop current) | `family2_loopCurrent_pos` (loop current > 0 around `loop2 λ k₀`, 0 < k₀ < 19/20) via `torCurrent_eq_lineIntegral` (Stokes, `SectionStokes.netToroidalCurrent_eq_lineIntegral_div`) and `family2_net_current_pos`; `family2_not_currentFreeTransform(_zero)` for any surface whose loop is `loop2 λ k₀`; λ-independent bound `family2_net_current_ge`. Family 1 open |
| `Q-19` | **Bounce-averaged drift / ε_eff for the rational stellarator vacuum field** (contract C2): on the certified surfaces of `RationalStellarator.field (1/4)`, compute (numerically first, as an untrusted oracle) the bounce-averaged radial drift of trapped particles and ε_eff, then decide whether a certified bound is reachable | G-10, G-1 | answered numerically (untrusted, 30 October): fails C2 | N-30: ι from 0.134 on the axis (1 − √3/2) to 0.169 at r = 0.40, matching the KAM torus (ι_A = 0.13743); best helicity QA (1, 0) with defect ≈ 26 % of the ‖B‖ variation (defect/ι ≈ 0.27, not shrinking toward the axis); ε_eff ≈ 0.2 r_eff (2.7 % at torus A, ≈ 10 % at r = 0.36), classical-stellarator level. Informal obstruction: for this planar-axis family the non-QA first-order ‖B‖ variation equals √(ι₀/N) (Garren–Boozer: a planar axis in vacuum admits no QS with ι ≠ 0), so adding harmonics cannot help. Lean target: `rotatingEllipse_firstOrder_QA_defect`. Consequence: the Dommaschk route (Q-16) needs a non-planar axis. The separate QA2R candidate has a positive trapped reference in N-117. Its numerical thermal fraction and radial drift are open under G-10. |
| `Q-20` | **A finite-β current-free equilibrium** (C1 + C4 at β > 0): stepped pressure across the certified torus of the rational field (Q-14), or a finite-β equilibrium near a Dommaschk QA vacuum field, with ‖I_tor‖ ≤ I_max proved | G-4, G-8 | open (research) | Q-14 is the lead (`after-kam.md` §3); stepped-pressure equilibria carry surface currents whose net toroidal part must be controlled **16 November 2026 (N-47):** an exact closed-form finite-β equilibrium with zero net toroidal current through every flux surface exists (Issan et al., arXiv:2611.07672, Family 1 with ρ_a = ρ₀; checked numerically, not in Lean), but it has ι = 0, so the open part of Q-20 is ι ≥ ι_min, not the current. The Q-31 obstruction on A excludes the N-44 strict sign route there. On a viable construction, the nonzero-step current and transform must both be estimated. N-69 proposes testing the first pressure variation for foliation and closed-field-line period obstructions. |
| `Q-21` | **Definitions and model contracts for C1 and C2** (kernel-level): net toroidal current through a cross-section of a toroidal domain; ι of a field on a family of invariant tori; bounce-averaged radial drift (ψ̇ averaged over a bounce; zero for all trapped orbits iff ∂J/∂α = 0 for the second adiabatic invariant J); omnigeneity; ε_eff (Nemov et al. 1999). Each with the **sanity triad**: (1) axisymmetric ⇒ omnigenous (bounce-averaged radial drift zero); (2) current-free axisymmetric ⇒ ι = 0, hence no confining rotational transform (no confinement); (3) a generic 3-D field (an explicit one) is not omnigenous | G-11, G-10, G-1 | C1 and C2 definitions in Lean (30 October); ε_eff open | `Theory/Contract/StellaratorContract`: `netToroidalCurrent`, `CurrentFree`, `IotaOnTorus`, `CurrentFreeTransform` (C1); tokamak exclusion `iota_eq_zero_of_purelyToroidal`, `not_currentFreeTransform_of_purelyToroidal`; vacuum ⇒ current-free (`netToroidalCurrent_eq_zero_of_vacuum`, `currentFreeTransform_of_vacuum`); `OmnigeneityContract` (C2, Boozer GC model) with `omnigenousOn_of_axisymmetric` and counterexample. `rationalStellarator_currentFreeTransform`: the rational field satisfies C1 on KAM torus A. Open: ε_eff; current-free axisymmetric with nested surfaces ⇒ purely toroidal (maximum principle); section independence of the current |
| `Q-22` | **Thermal-particle neoclassical transport bounds feeding G-2**: from a C2 bound (ε_eff or bounce-averaged drift), a stated neoclassical scaling (1/ν regime χ ∝ ε_eff^{3/2}, supplied as a model law) giving χ bounds for ions and electrons on stellarator geometry, used in the barrier theorems of Q-15 | G-2, G-10, Q-15 | open | none; the transport barriers exist on cylinder, helical and Solov'ev geometries with supplied χ |
| `Q-23` | **Quasisymmetry ⇒ omnigeneity (the C2 bridge)**: (a) exact: weak quasisymmetry (`WeakQS`) implies zero bounce-averaged radial drift of trapped particles (omnigeneity); (b) quantitative: a quasisymmetry defect ≤ δ gives a bounce-averaged radial drift ≤ C·δ with explicit C, hence a bound on ε_eff and on 1/ν neoclassical transport feeding C5 | G-10, G-2, Q-16 | exact and per-bounce quantitative versions verified in the Boozer GC model (30 October); ε_eff link open | `omnigenousOn_of_exactQS` (exact QS + twist ⇒ ψ returns after every bounce), `approxOmnigenousOn_of_defect_le` / `bounce_psi_drift_le` (‖ξB‖ ≤ δ, B ≥ B_min, twist ι_min ⇒ ‖Δψ‖ ≤ 2H/(‖q‖ B_min ι_min)·δ·τ per bounce; linear in δ, sharp on an explicit counterexample); `exactQA` omnigenous; `reactorQA` worst-case drift ≤ 4182 T m²/s (not a transport estimate). Model scope: Boozer GC equations, orbits and bounce existence supplied; Boozer ξB not yet linked to `WeakQS`. Open: ε_eff and 1/ν, a sharp oscillation bound, the quasi-isodynamic route (N-29). N-49 compares an approximate momentum on the physical phase space with the chart-based route. |
| `Q-24` | **Existence of strongly quasisymmetric, non-symmetric fields in a volume** (vacuum or MHS) | Q-16, G-10 | open mathematics (research, not on the critical path) | Unknown in the literature (Constantin–Drivas–Ginsberg arXiv:2009.08860; Burby–Kallinikos–MacKay arXiv:1912.06468; Garren–Boozer suggests non-existence away from the axis). If proved, the validated near-QS route of Q-16 becomes exact; the design path does not depend on it. Vacuum case made precise by the colleague's brief (N-32): for a fixed solid torus the vacuum field is unique, so the question is whether that field admits the linear system (FQS) with global conditions; its jet test is Q-25; its holomorphic (HYM/Bogomolny) lift is a re-encoding, and the twistor / elliptic-curve / higher-rank directions are speculative *17 November 2026: evolutionary-search route proposed (N-41).*. N-50 proposes linearizing the Euclidean realization conditions modulo reparametrization. |
| `Q-25` | **Fixed-field QS jet obstruction** (from the colleague's brief, N-32): (a) in Lean, for a vacuum field B, strong QS (ι_u β = dΨ, L_u α = 0, L_u ν = 0) ⇔ the linear system B·∇Ψ = 0, (B × ∇Q)·∇Ψ = −C B·∇Q (Q = ‖B‖², C constant, u = (∇Ψ × B + C B)/Q); the obstruction lemma: where X = B, Y = B × ∇Q, Z = [X, Y] are independent, dΨ = Cη, so dη ≠ 0 at one point excludes strong QS on every neighbourhood; (b) certified instance B = ∇(xyz) at (1, 2, 3) (dη_xy = 1739/21600); (c) certified non-QS points for `RationalStellarator.field` and the Dommaschk candidate (N-31), keeping their claims at the approximate tier; (d) research: a quantitative version giving certified lower bounds on the QS defect (two-sided Q-16 tiers). Optional: the global disk section p = Φ/P (B·∇p = Q/P > 0) and the return-map lemma | Q-16, Q-24, G-10 | **(a), (b) verified; (c) verified for the rational field (31 October)**; (c) for the Dommaschk target and (d) open | `Theory/Fields/QSLinearSystem`: `fieldDiv_fqsGen` (div of u = (∇Ψ × B + C B)/Q for vacuum B, actual fderiv), `FQSAt.strongQSAt` / `StrongQSAt.fqsAt` (equivalence), `JetHyp.jet_obstruction_curl` and `jet_obstruction_eta` (C ≠ 0 ⇒ dη(p) = 0), `strongQS_jet_obstruction` (vacuum corollary: dη(p) ≠ 0 ⇒ C = 0 and ∇Ψ ≡ 0 near p); `Design/QSJetExample`: B = ∇(xyz) is vacuum, dη_xy(1,2,3) = 1739/21600 (`curl_etaJac_two`), `strongQS_obstruction`, `not_strongQS_of_ne_zero` (local, not a solid-torus counterexample). Hypotheses: Ψ C² at p; rank 3 at p; Y, Z, h, k regularity supplied in the general corollary. Brief's numbers re-derived exactly in sympy (N-32); rank-deficient loci (symmetric fields) need separate analysis; local only, so no global non-existence |
| `Q-26` | **Burn dynamics and kinetic yield for C5** (N-38, from N-36): (a) stable operating band: `PowerBalance` with G ≥ 0 below and G ≤ 0 above a certified T* keeps T in the band (`stable_band_of_sign_change`), and instability for G′(T*) > 0; (b) finite-fuel obstruction: without fuelling no reaction rate bounded below for all time (`no_sustained_burn_without_fuelling`); (c) kinetic yield perturbation \|R(f) − R(F)\| ≤ K_max(‖f_D − F_D‖₁‖f_T‖₁ + ‖F_D‖₁‖f_T − F_T‖₁) (`reactionRate_sub_le`); (d) explicit alpha deposition fraction f_dep in G-2 claims (AK-1) | G-2, G-8 | open (a)–(c) lean-ready | none in Lean; proofs elementary (N-38); the compiled windows (N-5) are the f_dep = 1, fixed-density case *17 November 2026: evolutionary-search route proposed (N-41).* |
| `Q-27` | **Residual-based invariant neighbourhood** (N-39, from N-36 §10): (a) scalar lemma: Y′ ≤ −λY + LY² + ϵ(t), 0 ≤ ϵ(t) ≤ ϵ, Y(0) ≤ r*, −λr* + Lr*² + ϵ < 0 ⇒ Y ≤ r* (`le_inward_radius`), and ∃ r > 0 inward ⇔ λ² ≥ 4Lϵ (`exists_inward_radius_iff`); (b) time-dependent supersolution on a closed horizon (scalar part of gate E3); (c) norm-to-observable lemmas (weighted L²_v with ℓ > 9/2 controls moments ≤ 3; T Lipschitz in moments for n ≥ n_min) | G-7, G-2 | open ((a) lean-ready) | `riccati_le_initial` covers only a multiplicative ε and no additive residual; algebra re-derived exactly (N-36 checks 9–10) |
| `Q-28` | **Kinetic model contract and a turbulent flux bound** (N-40, from N-36): (a) lean-ready fixtures: Landau kernel U(z)z = 0 and PSD, pairwise conservation, energy-flux decomposition, non-constant Maxwellian not stationary, vacuum force balance ⇒ ∇p = 0, D–T reaction moments; (b) research: in local electrostatic gyrokinetics, |Q_s| ≤ C_Q W and Ẇ ≤ −λW + CW^{3/2} + ε with derived constants (brief Research target 1), or bounded turbulence with small mean flux; (c) research: a flux-divergence (operator-defect) bound so the barrier theorems can use a produced flux instead of a supplied D | G-2, G-11, G-3 | open ((a) lean-ready; (b), (c) research, after Q-20) | free-energy identity and fixtures re-derived exactly (N-36 checks 1–7); Â (N-20) remains a proxy |
| `Q-29` | **Corrected full-orbit flux for exact weak QS** (N-43, from N-42): (a) lean-ready: the tensorial homological solution `C = b(Ka)ᵀ + (Ka)bᵀ − ½S_⊥K`, `[C,K] = S`, and the exact identity `J' = ε²Σv_iv_jv_k∂_kD_ij` for `J = ψ − εu·v + ε²vᵀDv` along supplied orbits; (b) lean-ready: the certificate `\|Δψ\| ≤ 2A(V) + tR(V)`, the core confinement until `T_cert`, and the hot-core moment bounds; (c) research: combine with the gyro-Noether defect correction (explicit secular parallel term in `u·∇\|B\|`) | G-6, G-2, Q-23, Q-1, N-43 | open ((a), (b) lean-ready) | algebra checked in N-42 (symbolic and numeric); compiled analogue for Killing generators: `gyroNoether_hasDerivAt`, `gyroNoether_band`; barrier: no exact weak-QS equilibrium with a non-Killing generator (Q-16, Q-24). N-49 gives an alternative approach to part (c) via a phase-space generator. N-51 proves the common-volume periodic alternative on an annulus. |
| `Q-30` | **Signed free-boundary stability benchmark** (N-44, from N-42): (a) the cylinder window inequality chain with the Bessel ratio and Neumann-impedance lower bounds as hypotheses, giving `F_mn ≥ s²/8` and the period-uniform gap `(s²/80)(1 + \|m\| + κ)`; (b) research: transfer to a bent tube or torus with Hessian-change bounds uniform in the period | G-4, Q-3, Q-14, Q-20, N-44 | (a) verified with supplied multipliers; (b) open | `CylinderInterfaceGap.nonaxisymmetric_gap`, `axisymmetric_gap`, `fixed_flux_zero_mode`, `close_wall`. The period-uniform bound uses both low- and high-frequency estimates; the window needs a wall within about 5% of the minor radius at β ≈ 0.04 (unstable `m = 1` from `b/a = 1.1`); Mathlib has no modified Bessel functions |
| `Q-31` | **Toroidal interface sign test on the certified Dommaschk torus A** (N-44): does a `σ` exist with `a₀ + σb₀ < 0` on torus A (`a₀ = II(Y, g⁻¹ω)/\|ω\|²`, `b₀ = II(Y, g⁻¹Jω)`), giving a positive interface term for small stepped pressure? | G-4, Q-14, Q-20, N-33, N-44 | answered negatively on A | N-55, `DommaschkInterfaceArcBounds.exactTorusA_obstruction` and `DommaschkInterfaceArcWitness.exists_embedded_torus_obstruction`. At one point every positive metric pairing has positive mixed curvature. C has an external interval witness. Other stability criteria remain open. N-69 proposes a separate whole-interface energy test allowing a patch of adverse curvature. |
| `Q-32` | **Certified harmonic perturbations of the Dommaschk seed** (N-42 S-10): find members `B₀ + ∇Σa_jP_j` (symmetric harmonic polynomials) with better QS diagnostics and their own torus certificates, or quantify the KAM radius `ε_N` | Q-16, G-1, G-10, N-31, N-33, N-41 | open (research; workstation route) | KAM persistence (source Theorem 4, plausible) gives existence for an unquantified `ε_N` only; every member is C1 (vacuum); the certificate pipeline of N-33 is a-posteriori per field. Q-34 supplies a possible boundary deformation for comparison with coefficient variation. |
| `Q-33` | **A deformation complex for quasisymmetric equilibria** (N-46, speculative): is there a complex (dg Lie or L∞ algebra) attached to the weak-quasisymmetry and force-balance equations whose cohomology counts the free functions and the obstructions order by order, and explains why the near-axis expansion is solvable to second order and overdetermined from third order (Garren–Boozer)? | none (conceptual; would inform G-10) | open, exploratory, low priority | no formulation found in the literature search of 16 November 2026; the algebraic parts are compiled (`FormWeakQS`, `FormForceBalance`, `Kernel/Forms`) |
| `Q-34` | Does an embedded Dommaschk boundary satisfy Roussel’s admissibility, straight-field and mixed-curvature hypotheses, and admit a normal deformation with nonzero mean boundary return-map response? | Q-32, G-1, N-50 | open, research | Test the mixed second fundamental form on torus C or A. Tangential relabellings account for zero-mean variations. Q-36 now supplies the embedded boundary surfaces. The solid-torus domain, admissibility, straight-field and curvature hypotheses, and a physical normal variation with nonzero mean response still require evidence. |
| `Q-35` | When does a periodic flow over an annulus admit a radial label with zero averaged first-order drift and a quantitative second-order confinement bound? | G-6, Q-1, Q-29, N-49 | proved in periodic phase coordinates | N-51 proves the annular stream, corrected radial label, winding obstruction and confinement through inverse-square time in periodic phase coordinates (scoped audit `4b0bf64`). N-58 gives the finite-time radial barrier. On the QA2R pilot, N-99 and N-116 provide a closed height family of regular pilot wells with joint action and time bounds. N-104 and N-113 identify time as the action derivative in height and provide an inverse action coordinate. N-112, N-114 and N-117 give positive regular-birth mass. N-125 obtains an actual local radial band for both signs with existential time and fraction. N-118 supplies the fixed-height transverse action derivative. Constructing the physical bounce annulus, controlling phase coverage and radial variation, and bounding the reduction error and physical time remain open. N-123 supplies pointwise targets for positive radial variation on the pilot well. N-124 verifies both at the section-centre birth on the same embedded tori as all eight traces. N-126 also gives a finite two-label test using the height derivative alone. The paired profiles pass on all 325 rows externally. N-128 checks the first row pair in Lean on the actual lines through both original births. N-133 gives a physical interval below mirror strength at each of the four opposite-section births. N-132 verifies the full field and arclength hypotheses on the upper-mirror slab. N-136 joins the calibrated pilot and the second original birth, with both profile comparisons through ±5/16 radian. N-135 adds an explicit 1/270000 clearance on all 317 signed incoming tube pairs at u=0.478. N-137 checks the paired profiles at 22 difficult indices by sharing each spatial gradient over several signed rows. N-142 transfers the lower quadrature to nearby heights on the same trajectory. N-143 proves both profile inequalities through the outer 89 indices in each direction. N-144 gives a first-well action secant above 1/3 from a finite signed path comparison. N-140 verifies the signed physical action inputs near all four opposite-section births. N-145 localizes both near-upper first contacts to 1/512 radian of their upper-height locations. N-148 supplies a second physical lower-action route that can reuse each finer signed cell. N-147 converts two transverse branches into a four-dimensional tube around the compact physical central arc. N-146 discharges all 325 paired profile estimates on both signed clocks. N-150 applies one positive time and one five-dimensional neighborhood to a continuous arc, energy interval, height band and both velocity signs. N-149 grounds 224 matched physical step pairs, 6,240 action cells and two additional phase-zero clearance bounds. N-152 verifies all 48 original spatial growth bounds nearest the outer mirror and two local physical steps at row 317. N-154 uses a common regular vacuum enclosure to control the union of all admitted pilot arcs for one time. N-158 verifies 640 signed secondary clearance slabs at three radial labels for all admitted phase-zero birth angles. N-157 proves a genuinely nonconjugate pair of physical steps and screens all 2,007 new signed step indices. N-156 verifies an absolute lower bound on the action between the two actual first mirrors from each admitted second birth. N-161 grounds the full equal-height radial action secant greater than 1/3 throughout the shifted admissible height interval. N-159 gives a conditional exact height-measure lower bound for two sufficiently steep first mirrors. N-160 gives one positive local time for both regular arcs through all admitted launch phases from the same original tori. N-162 combines the absolute action enclosures with the same original birth trajectories used for the shifted-height comparison. N-163 checks independent forward and backward physical ODE steps at an asymmetric opposite-section row. Both archived heights have rigorously bracketed crossings conditional on the opposite-section paths reaching the specific signed cap tubes. The initial sign history, both-height caps, and lower-height first-root implications are checked for both outer phase-zero launches. N-155 certifies all earlier signed tubes up to the lower mirror brackets at the four opposite launches. The actual radial action secant exceeds 2/5 throughout the closed archive band, with an even sharper upper endpoint in N-162. N-164 proves the 51.639% uniform-height lower bound at the second original launch without checking pointwise field-strength slopes. N-166 verifies all twelve original signed residuals in a six-row group and both actual physical row-60 steps. N-167 attaches the target-or-grazing theorem to the proven endpoint wells at u=0.470 and 0.478; the interpolating capped family is still required. The fixed-line height probability is at least 51.6391% at u=0.478; the four opposite-section passage implications have bracket-width-specific probabilities. N-170 checks sixteen original opposite-section field defects and both physical steps of row 49; all 2,664 allowances pass exact group preflight. N-169 verifies strict upper-height signs on the four forward and four backward cap tubes. N-171 reduces the target-or-grazing application to original paths and field signs. N-174 observes the lower-height clearances at the extended physical checkpoint. N-173 begins the central physical residual check over the continuous interval. N-176 removes independent continuous-family and launch-position obligations from the four-section target test. N-175 proves a common 16-slab two-sided launch and the regular spatial box on every proposed tube. N-172 verifies the mirror orientation throughout the 112 signed collar tubes. N-177 verifies the faster exact fixed-point Horner route against identical original fields and slabs. N-178 gives a compact target-action set with every allowed phase in its projection. N-179 verifies an unconditional submirror interval through ±1/8 for every original launch in the rectangle. N-181 ties both transverse first mirrors and the three cap/section signs to the same tracked solution. N-180 gives the connected-level topology required for the sector application. N-182 verifies the orientation on the two physical radial faces used in the connected-level theorem. N-183 composes the complete observed signs with the jointly continuous sector test. N-184 proves a uniformly interior connected target set covering the small phase sector once the through-going lines are verified. N-187 verifies a smaller exact spatial certificate against the original signed row budgets. N-185 proves annular separation and the angular lift obstruction under global bracketing. N-186 supplies quantitative mirror persistence under variation in height at all original births, subject to physical tube membership. N-188 supports any continuous phase-dependent action prescription in the common interval. N-193 verifies opposite-section submirror strength throughout the four enlarged physical intervals. N-190 isolates an obstruction in the action even though the original births are submirror. N-189 validates the separate opposite-section backward frame against actual physical steps. N-192 identifies the physical time as the action derivative and gives joint continuity in phase, radius and height. N-191 proves positivity of the parallel speed over ±59/32 on true lines through the full small sector. N-196 checks physical launch strength directly on the entire broad radial interval in two sectors. N-194 obtains a quantitative physical clock on the nonturning angular core. N-199 reduces local exclusion of radial exits to an identified particle observable with initial mismatch plus drift at most 19/10000. N-197 moved spare spatial capacity to missing local ODE defects and began authenticating chain segments before the final cap. N-195 removes mirror bracket and slope computations from the direct opposite-section action-floor test. N-198 closes the all-phase launch-strength input on the true torus chart. Global first-well identification and action bracketing remain open. N-200 extends the true four-tile ODE to ±239/64 on all original radii. N-201 gives an explicit mass formula for Lipschitz actions and a compactness-based positive mass without a numerical derivative. N-202 supplies a positive outer action margin extending four millionths below the reference height. N-204 verifies both true initial ODE steps and 48 signed physical panels and supplies a resumable full-core verifier. N-205 closes the local four-tile QA2R target-action construction, including variable heights and actions. Global first-well bracketing and the physical drift estimate remain open. N-203 proves full-period accessible field-line segments and their Cartesian field equation with explicit strength and displacement bounds. N-206 controls observed radial first exit for variable heights given a pre-exit bound on action drift. N-210 records the updated C1–C5 assessment and its concrete drift target. N-207 reaches another pair of physical first mirrors, beyond the original 0.470–0.478 radius strip. N-212 permits continuous moving brackets when a fixed narrow strip misses the target. |
| `Q-36` | **Embeddedness of the certified tori (clause C1 with embeddedness).** Prove `Contract.EmbeddedCurrentFreeTransform` (C1 together with `EmbeddedSurfaces`: every surface an `EmbeddedTorus`, i.e. `C²`, injective modulo periods, immersed) for every C1 example: (a) the rational stellarator torus A (`rationalStellarator_currentFreeTransform`, `Sanity.ContractLoopCurrentFixture.rationalStellarator_fixture`); (b) Dommaschk torus C (`DommaschkKamC.dommaschk_C1_unconditional`); (c) Dommaschk torus A (`DommaschkKamA.dommaschkA_C1_unconditional`); (d) the nested pair (`DommaschkKamNested.dommaschk_nested_C1`) and the Q-16 theorems built on it (`DommaschkKamQ16`) | G-1, G-11; audit AF-1; N-48 | proved in Lean, 23 November 2026 | N-52 gives `FieldTorus.embeddedTorus_of_irrational` and `CurrentFreeTransform.embedded_of_irrational`. Applications are `rationalStellarator_embeddedCurrentFreeTransform`, `rationalStellarator_embedded_fixture`, `dommaschkC_embedded_C1`, `dommaschkA_embedded_C1`, `dommaschk_nested_embedded_C1`, `dommaschk_Q16_embedded` and `dommaschk_Q16_strong_embedded`. The original current and transform allowances, nesting, charts and defect bounds hold on the same witnesses. |

### RG.3 Note registry and dependency graph

Status values: exploratory / stated / proof-ready / lean-ready / verified / blocked / refuted /
superseded; mixed notes list the status of their parts. "Lean" names compiled evidence.

| Note | File and title | Addresses | Depends on | Difficulty | Status / Lean readiness | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| `N-1` | `notes/theory/toroidal-min-b-obstruction.md`: min-B / max-J restrictions | G-1 | §1.1 correction | moderate | core verified (`VacuumField.not_strict_local_max_normSq`, `exists_vacuum_strict_interior_min`, `Theory/Fields/CurvatureObstruction`); G conjectured; Hall–McNamara lead | finite-β curvature obstruction (T1 ○) |
| `N-2` | `notes/theory/relative-entropy-dissipation.md`: corrected identity | G-2, G-7, Q-10 | §1.5 | moderate | 1-D verified, including coercivity: identity (`relEnt_pointwise_identity`, `RelEntSetup.rate_eq`), dissipation bounds, zero Fisher information ⇒ T/T* constant (`RelEntSetup.ratio_eq_of_fisher_eq_zero`), H ≤ N M (b−a)²/(4k₀)·𝓕 with T = T* at an endpoint (`RelEntSetup.relEnt_le_mul_fisher`), exponential decay given dH/dt ≤ −𝓕 (`relEnt_exp_decay`); the boundary condition is necessary (`no_coercivity_without_boundary`) | differentiating H under the integral; radial axis term; 2-D/3-D |
| `N-3` | `notes/theory/flux-surface-holonomy.md`: periods, τ, Hodge bounds | G-7 (T10) | §1.2 | moderate | holonomy ↔ ι refuted; 2-form vanishing verified (`magneticTwoForm_flux_surface`); constant-metric τ/energy identity and Hodge period inequality verified (`periodBound_eq`, `energy_ge`, `energy_eq_iff`, `fieldLine_energy_ge`) | non-constant metric (isothermal coordinates, not in Mathlib) |
| `N-4` | `notes/theory/near-axis-quasisymmetry.md`: Garren–Boozer construction, Boozer GC model | G-1, G-6 | sources | hard | construction formal asymptotic; GC identity verified (`boozerGC_trapped_until`, `boozerGC_trapped`) | none pending; feeds N-8, N-17 |
| `N-5` | `notes/theory/stellarator-burn-parameters.md`: ISS04, reactor studies | G-2, Q-13 | Bosch–Hale, ISS04 (supplied) | routine | verified window and obstructions (`Design/BurnWindowStellarator`); parameters published | Q-15 Method note N-38 (burn dynamics, kinetic yield). |
| `N-6` | `notes/theory/transport-mhd-coupling.md`: one field for G-1 and G-2 | G-1, G-2, Q-10 | K2 kernel | moderate | verified in budget form (`solovev_one_plasma_actual`, `…_highQ_actual`, `…_ignited_actual`) on the Solov'ev field, **a tokamak model** (contract re-label, 30 October 2026: a model for G-2 and a technique test bed, not a candidate); solution existence and pressure equality open | Q-10; the transfer to a C1 geometry (Q-15, Q-22) Method note N-38. |
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
| `N-18` | `notes/pde-bounds-and-verification-roadmap.md`: Stages 1–7, Milestones A–G | G-1, G-2, G-7 | — | research | Milestone A verified (T1); B–D compiled under other names (`BartaCertificate.energy_pos`, `sbpGen_identity`, `mem_Icc_of_barriers`); E partial; F refuted; G abstract only (`radii_polynomial_fixedPoint`) | link stages to Q-7–Q-11 |
| `N-19` | `notes/bkm-regularity-and-perelman-burn-bounds.md`: corrected evolution specification (§11) | G-7, Q-7–Q-10 | §1.3, §11 | research | E1 verified (`quasisymmetry_not_pde_symmetry`, `lieBracket_gradient_of_contDiffAt`); conditional Riccati verified; rest stated | Q-7 (first theorem, §11.3) Method note N-39 (inward radii, norm-to-observable). |
| `N-20` | `notes/microturbulence-and-available-energy.md`: available energy, Â | G-2, Q-15 | sources | research | kernel lemmas verified (`Theory/Kinetic/AvailableEnergy`); opposite-sign claim refuted; Â bound stated | extract the Helander–Mackenbach Â formula (§1.5) Method note N-40 (kinetic contract, flux bound). |
| `N-21` | `notes/holomorphic-bundles-kym-wick-rotations.md`: exploratory geometry (T10) | G-7 | §1.2, §1.4 | research | exploratory; flux degree corrected to 0; refuted contract sketches fenced; direct KYM coupling and holomorphic QS generator closed by N-32 | verdict note before any Lean (T10 rule) |
| `N-22` | `notes/goals/` (overview, probabilistic, deterministic, milestones) | G-3 | §12 | research | stated (proposals); D/K cross-references unresolved | choose one N1 observable 4 Nov: acceptance criteria and rejection tests added in place (N-36). |
| `N-23` | `notes/design/vacuum-demonstrator.md`: tolerance-aware vacuum fixture | G-5, G-8 | — | routine | verified fixture (`Design/VacuumPair`, `Design/VacuumTolerance`) | none |
| `N-24` | `notes/formalization/00`–`09`: model contracts and topic specifications | all, G-11, Q-21 | — | — | active specifications (00 contracts is normative); C1/C2 definitions in Lean (`CurrentFreeTransform`, `OmnigeneityContract`, `OmnigenousOn`, `ApproxOmnigenousOn`, `bounceAvgDrift`); `EffectiveRippleBound` (ε_eff) and C5 not in Lean | Q-21: Lean definitions and the sanity triad |
| `N-25` | `notes/Stellerator.md`: original design basis | G-8 | — | — | historical (illustrative distances are not universal limits) | none |
| `N-26` | `notes/theory/orbit-existence.md`: existence of the orbits the confinement theorems quantify over | G-1, G-6, MA-M1, MA-M2 | N-8, N-14; `FieldLineExistence` | hard | Lorentz part verified (`lorentzOrbit_exists`, `reactor_alpha_born_confined`, `reactor_alpha_confined_nonvacuous_35MeV`); Boozer part: band of births to 0.05 s and, for the original class, the explicit horizon r₀/285000 s with r₀ = √(2ψ₀/B₀) (at most 1.49 μs, shrinking to 0 at the axis) (`alpha_band_orbit_exists_005`, `alpha_orbit_exists_explicit`); proved limits of the band method `Dpsi_gt_psiStart`, `band_empty_Tav` (AR-M5, AR-M6) | coordinates through the axis (user decision); uniqueness |
| `N-27` | `notes/theory/quasisymmetric-solution.md`: routes to a quasisymmetric solution (Q-16; re-aimed at C1 + C2 by the contract) | Q-16, G-1, G-10, G-4, G-6 | N-4, N-12; Landreman `field_axis` theorems; KAM pipeline | research | stated; route (iii) a proved barrier (`family1_not_weakQS`, `family2_not_weakQS`, with `WeakQS`/`qsDefect` in `Theory/Fields/WeakQuasisymmetry`) | first priority under the contract: Dommaschk QA fit (current-free by construction) with torus, ι and Boozer/ε_QS diagnostics; the same Boozer pipeline for Q-19 on the rational field |
| `N-28` | `notes/theory/grad-conjecture.md`: Grad's conjecture and the 2026 counterexamples (contract re-label: mathematical infrastructure, not design progress) | G-4, Q-14, Q-16, Q-17 | N-12, N-27; `LandremanEquilibrium.family1` | routine (synthesis) | stated | Q-17 for family 1; τ-extension; stepped pressure source [ELP] for Q-14 |
| `N-29` | `notes/theory/omnigeneity-bridge.md`: quasisymmetry ⇒ omnigeneity in the Boozer GC model | Q-23, G-10 | N-4, N-27; `helicalMomentum_conserved` | hard | exact and per-bounce bounds verified | ε_eff / 1/ν link; oscillation bound; link Boozer ξB to `WeakQS` |
| `N-30` | `notes/theory/rational-field-c2.md`: C2 diagnostics for the current-free rational field | Q-19, G-10, Q-16 | N-9, N-10, N-29 | moderate | numerics untrusted; obstruction verified at first order (`rotatingEllipse_firstOrder_QA_defect`: the non-QA part of the first-order ‖B‖ is the exact sup-distance √(Nι₀)/2 > 0 iff ι₀ ≠ 0; `rationalStellarator_firstOrder_not_QS` for the actual field, 4ε² < 1, ε ≠ 0) | reuse the Boozer and ε_eff code for the Dommaschk route (N-31); straight-field-line vs Boozer angles at O(r²) not formalized |
| `N-31` | `notes/theory/dommaschk-qa.md`: Dommaschk quasi-axisymmetric vacuum fit with a non-planar axis (workstation task `dommaschk-qa`) | Q-16, G-10, G-1 | N-27, N-29, N-30 | research | exact NFP-3 field verified in Lean (`DommaschkQA3.candidate_vacuum`, `candidate_currentFree`); numerics untrusted: smoke test defect/ι 0.014–0.029 (ι_min 0.15, r ≤ 0.045); medium workstation run (24 coefficients, ι_min 0.2, r ≤ 0.06) missed the moderate tier (best defect/ι 0.12, nested to r = 0.032, ε_eff 4.5 %) ; diagnostic run (ι_min 0.15, r ≤ 0.045): moderate tier on the nested region (defect/ι 0.021–0.038, ε_eff 0.6–1.0 %, |ι| ≈ 0.24), volume limited by the ι = 2/9 island chain (r_eff ≈ 0.019) ; second diagnostic (ι_min 0.2): same picture, best defect/ι 0.020–0.051 at |ι| ≈ 0.25, middle surface on the ι = 1/4 resonance ; **nmax 3 (42 coefficients): moderate tier**, defect/ι 0.009/0.015/0.023 at |ι| 0.246–0.235 (low shear, inside (2/9, 1/4)), ε_eff 0.08–0.13 %, κ 0.11–0.37, regular to r_eff ≈ 0.037 (untrusted) ; nmax 4 (62 coefficients): no improvement (best start fails the high-resolution check: 2/9 island, nested only to r = 0.015) ; windowed run at r ≤ 0.06: worse (defect/ι ≥ 0.08; the window cannot stop ι reaching 2/9 at r ≈ 0.048) ; high-ι windowed run failed (2/48 regular, |ι| below the window) ; **NFP 3, nmax 2 (24 coefficients): first `candidate_for_certification`**: defect/ι 0.007/0.013/0.020 at |ι| 0.29–0.27, ε_eff 0.13–0.47 %, κ ≤ 0.40, regular to r_eff ≈ 0.025 (N-31 §15) ; NFP 3 nmax 3: worse (crosses 1/3 and 3/10) ; **strong tier reached, purely rational** (certification target, N-31 §22: NFP 2, defect/ι ≤ 0.0035 at |ι| ≈ 0.235, ε_eff ≤ 0.018 %, nested to r_eff ≈ 0.052; untrusted) and a purely rational moderate-tier NFP-3 field (N-31 §21); **certification step 1 verified**: `DommaschkQA3.candidate_vacuum`, `field_vacuum` (all coefficients), `candidate_currentFree` (C1 current clause), `field_stellSym`, on the reusable `CylAlgebra.gradField_vacuum` | KAM tori and ι for the NFP-3 candidate (C1 transform clause), Boozer angles, certified QA defect; warm-start refinement on the workstation; certification path: exact field in Lean, KAM tori, Boozer angles, certified QA defect relative to ι, N-29 drift bound |
| `N-32` | `notes/theory/holomorphic-qs-brief.md`: assessment of the colleague's holomorphic strong-QS brief | Q-24, Q-25, Q-16; closes N-21 routes | N-21, N-27, N-30, N-31 | routine (assessment) | assessment complete; explicit numbers verified in sympy; KYM and holomorphic-generator routes of N-21 closed (brief Props 5.1–5.2, checked by hand); Boozer moment Ψ' = Mι − N links QA nondegeneracy to C1's ι ≠ 0 | Q-25 (a)–(b) in Lean, then (c) on the rational and Dommaschk fields Patched by N-37 (orientation of the lift). Alternative method N-50. |
| `N-33` | `notes/theory/dommaschk-kam-certificate.md`: design of the Lean KAM certificate for the Dommaschk target (step 2) | Q-16, G-1, C1 | N-31, `kam_flow_torus`, KronBall | hard | **carried out: C1 verified (`dommaschk_C1_unconditional`); build log N-35**. Original design: conditional go: KronBall residual chain (≈ 90 modules, 45–85 CPU-min, ≤ 5 GB per module), `FlowFieldG` generalisation, exact low small divisors; contract blocker resolved (AR-L4: `PoloidalAngle` about a moving reference curve); remaining: `FlowFieldG`, exact low small divisors, a high-resolution oracle (≈ 104 × 84 modes) | workstation runs at 80 × 64 / 96 × 80; then `FlowFieldG` |
| `N-34` | `notes/theory/dommaschk-qs-defect.md`: certified QA defect on the certified torus C, and the path to C2 | Q-16, Q-23, G-10 | N-29, N-30, N-31, N-33 | hard | design: GO for the per-torus defect (vacuum Boozer angles explicit on the torus; defect ∂_{φ_B}\|B\|; ~20 on-demand modules, 15–20 CPU-min, laptop); strong tier needs the Wirtinger bound (A2), otherwise ≈ 0.059; NO-GO for C2 claims on the actual field until a `BoozerModelOf` link exists | A1 `VacuumBoozerTorus`, then D3–D7 and A2. Alternative methods N-49 and N-50. |
| `N-35` | `notes/theory/kamflow-g-status.md`: status log of the Dommaschk certification chain | Q-16, G-1, G-10 | N-31, N-33, N-34 | — (log) | active log; current results C1 on nested tori and strong-tier certified QA defect (`dommaschk_Q16_vacuum`) | keep as the build record; claims live in N-33/N-34 and the plan |
| `N-36` | `notes/theory/kinetic-coil-brief.md`: assessment of the kinetic plasma and coils research brief (3 November 2026) | G-2, G-3, G-5, G-7, G-8, G-11; Q-26–Q-28 | N-2, N-5, N-6, N-16, N-19–N-22, N-32 | routine | assessment complete: 50 claims, 22 checked and correct, 0 incorrect; 12/12 exact checks (`scripts/kinetic_brief/check_brief.py`); audit items AK-1–AK-3 | the lean-ready items of Q-26, Q-27, Q-28 (a) |
| `N-37` | `notes/theory/holomorphic-lift-orientation-patch.md`: orientation of the ASD lift (patch to N-32) | Q-24, Q-25 (context) | patches N-32; N-36 | routine | verified by exact computation; no Lean effect; resolves AK-3 | none |
| `N-38` | `notes/theory/burn-dynamics-kinetic-yield.md`: burn dynamics, fuel depletion, kinetic yield, alpha deposition | G-2, Q-26 | method for N-5, N-6; N-36 | routine–moderate | stated; (a)–(c) lean-ready | `no_sustained_burn_without_fuelling`, `stable_band_of_sign_change` |
| `N-39` | `notes/theory/residual-invariant-neighbourhood.md`: additive-residual comparison, inward radii, norm-to-observable | G-7, Q-27 | method for N-19; N-36; `riccati_le_initial` | routine (a); research (producer) | stated; (a) lean-ready | `le_inward_radius`, `exists_inward_radius_iff` |
| `N-40` | `notes/theory/kinetic-contract-turbulent-flux.md`: kinetic model contract and free-energy route to a turbulent flux bound | Q-28, G-2, G-11 | method for N-20; N-2, N-36 | routine (a); research (b, c) | stated; (a) lean-ready | kinetic fixtures module (Q-28 a) |
| `N-41` | `notes/theory/evolutionary-search-suitability.md`: where evolutionary search (`plasmalean-evolve-optimize`) fits the goals | G-2, G-4, G-5, G-8, G-9, G-10; Q-3, Q-12, Q-13, Q-24, Q-25, Q-26 | task server and framework (`c74b6b0`); `family2_stable_of_cert`, `lowerBound_le`, `svFloorF`/`svCeilF`, `picone_certificate`, `compose_branch`; N-38 | routine (assessment); moderate–research (pilots) | stated (proposal) | pilot 1: Picone gauge for a Newcomb/Suydam form; then Q-3 representation search, Q-24/Q-25 (d) QS jets, Q-26 (a)/Q-13 burn window |
| `N-42` | `notes/theory/fusion-complex-geometry-assessment.md`: assessment of the complex vacuum fields and stability estimates research note (18 November 2026) | Q-16, Q-24, Q-3, Q-14, Q-20, Q-28; G-1, G-2, G-4, G-6, G-10; Q-29–Q-32 | N-1, N-12, N-17, N-29, N-31, N-32, N-33, N-37, N-40, N-41; `dommaschk_nested`, `AdmBoundsG`, `laplacian_normSqField`, `gyroNoether_hasDerivAt` | routine | assessment complete: 35 claims, 30 checked and correct, 0 incorrect, 5 unverified; scripts `scripts/fcg_source/`; analysis `notes/reasoning/2026-11-20-source-fusion-complex-geometry/`; audit item AF-1 | assess the earlier handoff `sources/complex_geometry_handoff.pdf`; lean-ready corollary: a vacuum field of constant \|B\| is constant (from `laplacian_normSqField`) |
| `N-43` | `notes/theory/weak-qs-corrected-flux.md`: corrected full-orbit flux for exact weak QS, absorbing-core certificate, hot-core moments | Q-29, G-6, G-2; Q-1, Q-23, Q-28 | method for N-29, N-17; N-42; `WeakQS`, `GyroNoether` | routine–moderate (Lean); research (application) | stated; proof checked; (a), (b) lean-ready | Q-29 (a): the homological solution and the exact identity. Alternative method N-49. |
| `N-44` | `notes/theory/cylinder-interface-stability.md`: fully signed free-boundary cylinder benchmark, toroidal interface criterion, transfer | Q-30, Q-31, G-4, Q-3, Q-14, Q-20 | method for N-12; N-42, N-13, N-33 | routine (Q-30 a); moderate (Q-31); research (Q-30 b) | cylinder window and period-uniform gap verified with explicit multipliers | Q-30 (b). N-55 rules out the strict Q-31 construction on A. |
| `N-45` | `notes/theory/differential-form-kernel.md`: differential-form language for the vacuum and force-balance kernel laws, with equivalences to the vector language | G-11 | `Kernel/Vacuum`, `Kernel/Equilibrium`; Mathlib `extDeriv` | routine–moderate | verified (`vacuumForm_flux_iff`, `vacuumField_fluxSymm_iff`, `formForceBalance_iff`, `forceBalance_iff`, `extDeriv_flat`, `extDeriv_flux`; `Sanity/Forms`; theory bridges `formFirstIntegralOn_flux_iff`, `formSymmetricFlux_iff`, `formWeakQS_flux_iff`, `formBeltramiOn_flat_iff`, `isContactAt_of_beltrami`) | audited 16 November 2026 (AD-*; `Sanity/AuditForms`); open: AD-L4, AD-L5 |
| `N-46` | `notes/theory/sullivan-infinity-structures.md`: assessment of Sullivan's L∞ (combinatorial) and eigenspace fluid models for MHD and stellarators | G-9, G-11, Q-33 | `sources/SullivanFluids.pdf`; N-45; `Theory/Stability/Elsasser` | moderate | stated; Part 2 checked in Lean (`EulerianODE.energy_conserved`, `EulerianODE.helicity_conserved`, `rigidBody_eulerian`); no design consequence | none required; revisit if an implementation of the L∞ hierarchy is published |
| `N-47` | `notes/theory/issan-arbitrary-field-periods.md`: assessment of the closed-form equilibria with any number of field periods (Issan et al., arXiv:2611.07672) | G-4, Q-17, Q-18, Q-20 | `sources/Non-AxisymmetricMHD.pdf`; N-28, N-27 | moderate | stated; 12 of 20 claims checked numerically (`scripts/issan_equilibria/`), none incorrect; nothing in Lean | optional Lean unit: Family 1 (ρ_a = ρ₀, N = 3) with zero loop current (Q-20) |
| `N-48` | `notes/theory/form-kernel-tauceti-complex-geometry.md`: the form kernel after TauCeti v4.36.0: topology and periods, contact geometry, the anti-self-dual lift, charged-particle Noether and Hamiltonian theory; fit of the complex-geometry notes | G-11; supports Q-29, Q-24, Q-16 | method for N-45; N-42, N-43, N-44; TauCeti v4.36.0 | routine–moderate | verified, audited 23 November 2026 (AV-*): twenty theory modules under `Theory/Fields/Form*` and `Theory/Kinetic/{Noether*, Magnetic*, CrossedFieldOrbit}` with sanity modules; see the note's "Current state" | open audit items AV-M4 (local versions); line bundle and Chern class of the lift (blocked on TauCeti); remaining N-48 internals after the scoped audit at `4b0bf64`. The geometric embedding theorem applies to the actual candidate surfaces through N-52. Alternative method N-49. |
| `N-49` | `notes/theory/trapped-particle-momentum.md`: approximate momentum, periods and finite-time loss | Q-1, Q-23, Q-29, G-6, G-10, G-3 | method for N-34, N-43, N-48 | research | conditional estimates on paper, field application open | regular trapped band, bounce mean and exit margin. N-51 constructs the radial coordinate from averaged flux. |
| `N-50` | `notes/theory/harmonic-field-shape-variation.md`: harmonic-field shape variation and Euclidean realization | Q-34, Q-32, Q-24, G-1, G-10 | method for N-32 and N-34, uses N-33 | research | sourced boundary theorem, seed hypotheses open | curvature test and physical normal variation |
| `N-51` | `notes/theory/annulus-averaged-flux.md`: radial stream, flux obstruction and second-order confinement | Q-35, Q-1, Q-29, G-6 | method for N-49 | moderate | Lean verified in the default library | construct a regular physical bounce band and bound its constants Also: a sanity module with an instance of the main theorem, docstrings for the fields of `VolumeChart`, and an audit. |
| `N-52` | `notes/theory/irrational-return-embedding.md`: irrational return and winding | Q-36, G-1, G-11 | method for N-48 | moderate | Lean verified on all Q-36 witnesses, 23 November 2026 | `FieldTorus.section_return_chord` and `FieldTorus.embeddedTorus_of_irrational`. The rational and Dommaschk applications preserve their C1 bounds. |
| `N-53` | `notes/theory/hamiltonian-bounce-band-test.md`: Hamiltonian bounce-band test | Q-1, Q-35, Q-22, G-10 | method for N-49, N-51 | research | Littlejohn band predicate and complementary-mass bound verified; candidate identification pending | measure level geometry and birth coverage |
| `N-54` | `notes/theory/dommaschk-mirror-screen.md`: two mirror-height screens on the Dommaschk field | G-6, G-10, Q-1, Q-35 | N-33, N-49, N-51, N-53 | research | winding-graph and simple-root criteria verified; deeper well supported by sampled diagnostics | N-56 covers the launch and an initial segment; certify the mirror crossings and action inequalities |
| `N-55` | `notes/theory/dommaschk-interface-obstruction.md`: positive principal direction on a certified toroidal interface | Q-31, Q-14, Q-20, G-4 | method for N-44; N-33, N-52 | verified A; external C | source sign test fails on A | evaluate an alternative interface or total-energy argument |
| `N-56` | `notes/theory/dommaschk-launch-collar.md`: flux and multidimensional field-line enclosure | G-6, G-10, Q-1, Q-35 | method for N-54; N-33, N-52, N-53 | moderate locally; research for the full bounce | reusable step and flux theorems in Lean; candidate bounds externally checked | N-57 reaches the mirrors locally; expand coverage of the strip |
| `N-57` | `notes/theory/dommaschk-regular-mirror-cell.md`: regular local mirrors and action inversion | G-6, G-10, Q-1, Q-35 | method for N-54 and N-56 | research for wider phase coverage | centred trajectory, arclength and regularized action theorems verified; local mirrors and j bounds checked externally | first variations beyond the tested common section and radial action bounds; certificate status patched by N-61 |
| `N-58` | `notes/theory/action-faces-and-winding.md`: action bounds on two radial faces | Q-1, Q-35, G-6, G-10 | method for N-51, N-53, N-54 | moderate | finite-time face barrier and oriented winding graph criteria proved | verify the two opposite face extrema on the phase circle and bound physical action drift |
| `N-59` | `notes/theory/dommaschk-phase-faces.md` — Action bounds on six Dommaschk phase sectors | Q-35, G-6, G-10 | N-52, N-54, N-56–N-58 | moderate for local sectors | two face bounds verified externally on six phase sectors, geometric and action-envelope theorems compiled | extend angular coverage; N-60 establishes local radial crossings at both symmetry sections; certificate status patched by N-61 |
| `N-60` | `notes/theory/dommaschk-local-action-graphs.md` — two fixed-action graph arcs on each of two phase sectors | Q-1, Q-35, G-6, G-10 | N-52, N-54, N-56–N-59 | research for winding | local graph and action estimates compiled, candidate arcs externally checked on the same full sectors | certify overlapping phase-dependent radial brackets and identity through a period; certificate status patched by N-61 |
| `N-61` | `notes/theory/dommaschk-mirror-certificate-replay.md` — Lean replay of mirror certificates | G-6, G-10, Q-1, Q-35 | patches N-57, N-59, N-60 | long trajectory remains open | physical Q-16 launch collar, 28 directed action packets and 32 radial half-traces | certify the actual moving-frame trajectory and its radial variation through the mirror caps |
| `N-62` | `notes/theory/dommaschk-long-trace-witness.md` — exact long-trace witness and finite-slab gluing | G-6, G-10, Q-1, Q-35 | N-57, N-59–N-61 | per-slab identification in progress | one two-sided 391-slab endpoint replayed externally, ODE gluing and observable identities compiled | check full physical defects and variational bounds inside Lean |
| `N-63` | `notes/theory/dommaschk-eight-long-traces.md` — long traces at all eight local-action endpoints | G-6, G-10, Q-1, Q-35 | N-60–N-62 | physical enclosures open | eight two-sided traces and 6,256 exact slab replays | prove the moving-tube bounds on the actual QA2R field |
| `N-64` | `notes/theory/dommaschk-physical-frame-trace.md` — physical entries and frame certificates | G-6, G-10, Q-1, Q-35 | N-60–N-63 | one-sided field derivative on moving tubes | physical entries at all eight radii, all 6,256 scalar steps, all harmonics, and the first forward physical reference defect compiled | prove the physical Jacobian estimate and compose the first step, then extend along both directions |
| `N-65` | `notes/theory/dommaschk-first-physical-step.md` — first physical moving-frame step | G-6, G-10, Q-1, Q-35 | N-61–N-64 | physical propagation on subsequent slabs | first forward slab from Q-16 births proved, three central defects compiled, all 6,256 central budgets screened exactly | compose adjacent physical steps, then reach the mirror and certify the radial variations |
| `N-66` | `notes/theory/dommaschk-full-frame-budgets.md` — full-trace Jacobian budgets and physical chain criterion | G-6, G-10, Q-1, Q-35 | N-60–N-65 | proof generation on long chains | all 6,256 Jacobian budgets pass exact screening, sufficient physical ball bounds and entry-to-chain theorem compiled | discharge adjacent physical bounds in Lean and reach the first mirrors |
| `N-67` | `notes/theory/dommaschk-two-physical-slabs.md` — physical trajectory across two adjacent frames | G-6, G-10, Q-1, Q-35 | N-61–N-66 | extending the physical estimates through whole mirror passages | one physical Q-16 solution reaches 1/32 radian at u=0.470 with uniform Euclidean error at most 1.232 × 10⁻⁶ | discharge and assemble the later moving-frame rows, including the first mirror |
| `N-68` | `notes/theory/dommaschk-quarter-radian-trace.md` — physical forward prefix and two-sided passage | G-6, G-10, Q-1, Q-35 | N-61–N-67 | consecutive candidate-specific enclosures | 16 physical forward slabs through 1/4 radian, signed two-sided first passage and field reflection checked | extend the connected trajectory to the first mirror and verify radial variation |
| `N-69` | `notes/theory/stellarator-conditions-and-geometric-questions.md` — C1–C5 and three geometric research questions | G-8, Q-20, Q-31, Q-35 | N-33, N-34, N-44, N-51, N-55, N-58, N-60, N-68 | global dynamics and finite-pressure geometry | assessment of compiled results and open problems | test well continuation and first-order pressure solvability |
| `N-70` | `notes/theory/dommaschk-signed-four-slab-trace.md` — three-eighths-radian trace and four-slab signed passage | G-6, G-10, Q-1, Q-35 | N-64–N-68 | extend estimates to both mirrors | 42 forward slabs and a four-slab signed field line verified at radius 0.470 | extend the physical traces and control radial action variation |
| `N-71` | `notes/theory/dommaschk-one-radian-and-signed-trace.md` — one radian forward and signed field-line trace | G-6, G-10, Q-1, Q-35 | N-61–N-68, N-70 | physical bounds on the remaining tubes | 64 slabs forward, 64 slabs each way from a shared birth, and both 391-row defect checks complete | extend the joined physical paths through the first mirrors |
| `N-72` | `notes/theory/bounce-action-sublevel-arclength.md` — bounce action from sublevel arclength | G-10, Q-35 | N-69, mirror action and Mathlib layer cake | estimating physical sublevel lengths across labels | exact representation, sharp comparison, equality and derivative bound in default Lean | bound sublevel profiles on a returning family of wells |
| `N-73` | `notes/theory/finite-sublevel-action-comparison.md` — finite sublevel action estimates | G-10, Q-35 | N-61, N-72 | verifying physical arclength at thresholds across labels | finite enclosure, mesh-corrected difference and counterexample compiled, exact eight-endpoint feasibility | produce direct length bounds on the physical wells |
| `N-74` | `notes/theory/dommaschk-projected-physical-trace.md` — physical field line through three projected Jacobians | G-6, G-10, Q-1, Q-35 | N-66, N-70, N-71 | derivative bounds over remaining tubes | 72 physical forward slabs through 9/8 radian at radius 0.470 checked | close the remaining rows up to the lower mirror |
| `N-75` | `notes/theory/dommaschk-signed-projected-trace.md` — a signed solution through reflected rectangular bounds | G-6, G-10, Q-1, Q-35 | N-71, N-74 | common signed trial projections and rates | single trajectory on [−9/8,9/8] from the same birth, 72 slabs each way | extend both directions to the mirror brackets |
| `N-76` | `notes/theory/dommaschk-signed-trace-spatial-split.md` — three signed radians and a split Jacobian | G-6, G-10, Q-1, Q-35 | N-66, N-74, N-75 | two half-boxes cover the full trial | [−3/2,3/2] joined; local row 226 proved in both directions | connect the rest of the path to the mirror |
| `N-77` | `notes/theory/dommaschk-mirror-level-contact.md` — local physical mirror heights | G-6, G-10, Q-1, Q-35 | N-60, N-66, N-70, N-75, N-76 | field polynomial signs and continuity on each enclosed path | four local ODE hits, plus a generic earliest-contact lemma | attach the birth passage and verify earlier strict signs and transversality |
| `N-78` | `notes/theory/dommaschk-adaptive-action-grids.md` — exact adaptive grid certificates | G-6, G-10, Q-1, Q-35 | N-60, N-61, N-72, N-73 | physical node arclength inequalities | strict target arithmetic on all 2,655 speed intervals in eight tables | derive the node bounds from the field-line data |
| `N-79` | `notes/theory/dommaschk-signed-submirror-trace.md` — strict field-strength bound along the birth trajectory | G-6, G-10, Q-1, Q-35 | N-66, N-75, N-76, N-77 | both signed paths and chronological field-strength certificates | signed path to ±2 radians; no level hit through ±3/2 radians; earliest-contact implications at both brackets | extend the strict prefix and path to the mirror |
| `N-80` | `notes/theory/physical-sublevel-arclength-from-time-panels.md` — derive closed-threshold lengths from time cells | G-6, G-10, Q-1, Q-35 | N-60, N-61, N-72, N-73, N-78 | measured well and directed time-panel packet covers | positive-threshold transfer, zero case and two concrete full-packet threshold sums | bind every adaptive node and prove physical coverage |
| `N-81` | `notes/theory/dommaschk-transverse-physical-mirror-brackets.md` — oriented physical mirror contacts | G-6, G-10, Q-1, Q-35 | N-66, N-76, N-77, N-79 | field derivatives on actual spatial tubes and endpoint signs | unique transverse local contacts in both brackets and directions; earlier heights excluded through ±2 radians | connect the full launch passage and sign prefix |
| `N-82` | `notes/theory/dommaschk-complete-sublevel-archive.md` — all eight directed action grids from the original archive | G-6, G-10, Q-1, Q-35 | N-60, N-61, N-73, N-78, N-80 | physical speed and arclength-density bounds on each original time panel | all 2,655 nodal hypotheses and eight strict targets from those covers | prove the original covers on the true field lines |
| `N-83` | `notes/theory/dommaschk-eight-reference-defects.md` — first-slab reference defects at all eight launches | G-10, Q-16, Q-35 | N-60, N-64, N-66, N-68 | exact central polynomials, moving frames and harmonic models | sixteen directed defect bounds and a rational Hessian-transfer comparison | assemble each launch’s own physical tube |
| `N-84` | `notes/theory/dommaschk-complete-pre-mirror-signs.md` — strict signs before both mirrors | G-10, Q-16, Q-35 | N-66, N-77, N-79, N-81 | each directed outgoing tube | both complete ordered strict bounds and same-path transverse first-contact implication | close physical propagation to the two brackets |
| `N-85` | `notes/theory/mirror-profile-stability.md` — profile stability | G-6, G-10, Q-1, Q-35 | N-72 | a finite common arclength measure and field perturbation estimate | sharp action and root-motion bounds; linear estimates from branch slopes | quantify physical label and arclength changes |
| `N-86` | `notes/theory/dommaschk-first-physical-action-cells.md` — three physical action cells | G-10, Q-16, Q-35 | N-60, N-66, N-77, N-81, N-82, N-84 | signed birth or admissible local backward entry | both original column inequalities with geometric arclength | cover contiguous slabs on one birth trajectory |
| `N-87` | `notes/theory/mirror-action-collar.md` — mirror-height collar | G-6, G-10, Q-1, Q-35 | N-72, N-85 | common measured well and regular near-height bands | linear action estimate even with a critical well bottom | verify a collar and density transfer across physical labels |
| `N-88` | `notes/theory/mirror-action-changing-arclength.md` — varying arclength | G-6, G-10, Q-1, Q-35 | N-72, N-85, N-87 | common parameter and integrable nonnegative densities | sharp additive L¹ error and derivative correction | bound physical density variation across labels |
| `N-89` | `notes/theory/dommaschk-five-radian-birth-trace.md` — five-radian birth trace | G-10, Q-16, Q-35 | N-66, N-69, N-76, N-79, N-81, N-84 | physical steps and field signs for 160 signed slabs each way | the same Q-16-launched field line lies below both heights throughout [−5/2,5/2] | extend through the two mirror brackets |
| `N-90` | `notes/theory/dommaschk-two-physical-action-blocks.md` — complete original launch-adjacent action blocks | G-10, Q-16, Q-35 | N-60, N-79, N-82, N-86 | physical birth path and compensated polynomial bounds | the original Covers theorem on 96 consecutive physical panels | extend to further blocks using shared exact bounds |
| `N-91` | `notes/theory/dommaschk-eight-signed-launches.md` — signed birth paths at all eight launches | G-10, Q-16, Q-35 | N-64, N-66, N-83, N-89 | signed spatial rectangles and physical entry from common tori | one true trajectory through both original first rows for each admissible birth | extend to the mirror brackets and the original action panels |
| `N-92` | `notes/theory/dommaschk-signed-action-integral.md` — partial action on one six-radian physical field line | G-10, Q-16, Q-35 | N-84, N-86, N-89, N-90 | complete signed trajectory and physical 96-cell cover | both mirror-height bounds on [−3,3] and a physical integral below 0.005587 on [−1/64,1/64] | extend propagation and quadrature to the well |
| `N-93` | `notes/theory/cylindrical-action-sensitivity.md` — cylindrical tangent and action sensitivity | G-6, G-10, Q-1, Q-35 | N-85, N-87, N-88 | full same-angle tangent discrepancy and fixed-density profile error | sharp geometric error bound on actual curve-weighted action | enclose the spatial velocity and strength change across labels |
| `N-94` | `notes/theory/dommaschk-native-action-panels.md` — original action bounds on both physical tubes of row 16 | G-10, Q-16, Q-35 | N-60, N-66, N-79, N-82, N-86, N-90 | seven harmonic channels, five physical interval models, original directed digits | 96 physical panel inequalities and exact rounded-root checks on blocks 308 and 341 | repeat and assemble on a common birth trajectory |
| `N-95` | `notes/theory/dommaschk-first-mirrors-from-birth.md` — First mirror contacts from a physical birth | G-10, Q-16, Q-35 | N-69, N-77, N-81, N-84, N-92 | both complete signed physical chains and earlier strict signs | One signed pilot path reaches the first contacts at both heights in both directions. | connect the wells to arclength and action |
| `N-96` | `notes/theory/dommaschk-first-well-action-floor.md` — Physical action between the first upper mirrors | G-10, Q-16, Q-35 | N-60, N-86, N-93, N-95 | a regular cylindrical region and physical first mirrors | The dimensionless one-way physical action exceeds 553/2000 at the upper height. | bound variation in whole-well action across births |
| `N-97` | `notes/theory/regular-mirror-births-and-components.md` — Connected wells and actual regular mirror births | G-6, G-10, Q-1, Q-16, Q-35 | N-60, N-91, N-95, N-96 | positive oriented velocity and equality with the original birth | Open and closed accessible components and the arclength contract at the original interpolated birth. | extend over a height band and a birth set of positive measure |
| `N-98` | `notes/theory/finite-transverse-mirror-bounce-time.md` — Finite one-way time between the first physical mirrors | G-10, Q-16, Q-35 | N-60, N-95, N-97 | inverse speed diverges at each mirror | The true arclength-weighted flight time is finite and positive at both pilot heights. | enclose flight time quantitatively on a height and birth range |
| `N-99` | `notes/theory/dommaschk-mirror-height-band.md` — First mirror wells throughout a physical height band | G-6, G-10, Q-1, Q-16, Q-35 | N-95, N-97, N-98 | signed physical slope on nine adjacent closed slabs, including their seams | The two outward first mirrors vary Lipschitz-continuously, action increases strictly with height, and every well has a finite positive flight time. | extend the birth labels and enclose flight time numerically |
| `N-100` | `notes/theory/open-mirror-wells-and-birth-area.md` — Persistence of mirror wells and the area of certified births | G-6, G-10, Q-1, Q-16, Q-35 | N-95, N-97, N-99 | joint continuity of strength and time derivative on a finite bracket | Open regular-well test, positive mass criterion for a physical chart, and a certified pilot rectangle in angle-height coordinates. | realize a chart varying radius and velocities under a physical birth law |
| `N-101` | `notes/theory/dommaschk-native-first-well-action-enclosure.md` — Physical action enclosure between the first upper mirrors | G-10, Q-16, Q-35 | N-60, N-94, N-95, N-96 | Original signed arclength and speed enclosure across 31,200 panels on one physical trajectory | At u=0.470 the actual upper-height well action exceeds 553/2000 and is at most 1146552112157123/844424930131968, strictly below target. | prove the other seven physical endpoint comparisons |
| `N-102` | `notes/theory/continuing-endpoint-field-lines.md` — Continuing signed field lines at other QA2R birth labels | G-10, Q-16, Q-35 | N-60, N-91 | actual first returns to the section, signed residuals and whole-tube spatial derivative estimates | Two signed rows each way at u=0.478 near zero and u=0.456 near π/2, with a common-torus comparison to the pilot in each case. | extend both trajectories to their own first mirrors |
| `N-103` | `notes/theory/quantitative-first-mirror-flight-times.md` — Numerical one-way flight bounds | G-6, G-10, Q-1, Q-16, Q-35 | N-95, N-97, N-98, N-99 | inverse-speed control through the physical turning points | T > 237/40 on the full height band, T < 34000 on its upper half, and a general length–action–time inequality | sharpen the bounds and control the lower half of the band |
| `N-104` | `notes/theory/mirror-action-flight-identity.md` — Action derivative and one-way flight time | G-10, Q-16, Q-35 | N-96, N-98, N-99 | clipping at moving endpoints and integrability near regular mirrors | Integrated identity on compact windows, with a pointwise derivative at each physical pilot height and a flat critical counterexample. | control variation with spatial launch labels |
| `N-105` | `notes/theory/shared-harmonic-endpoint-jacobians.md` — One field evaluation for four signed branches | G-10, Q-16, Q-35 | N-60, N-91, N-94, N-102 | harmonic identities for the field and six spatial derivatives, a shared rectangle and separate frame budgets | Three signed slabs each way at q0r523, q0r531 and q1r456. Four at q0r478. | continue the paths and verify separate matrices for nonconjugate frames |
| `N-106` | `notes/theory/toroidal-field-and-flight-bounds.md` — Toroidal field and sharper mirror flight times | G-10, Q-16, Q-35 | N-96, N-98, N-99, N-103 | exact harmonic coefficients on the continuous cylindrical envelope | Bφ > 7/8 everywhere in the pilot region; T > 14 across the band and T < 592 on the upper half. | quantify the central speed margin for the lowest energies |
| `N-107` | `notes/theory/independent-signed-endpoint-frames.md` — Separate signed matrices for unequal endpoint frames | G-10, Q-16, Q-35 | N-91, N-102, N-105 | independent forward and reflected-backward inequalities on the same physical field rectangle | A true local backward step at q1r456 row 129 and a three-slab birth application. All 6,256 individual Jacobian inequalities pass in the exact external screen. | construct the preceding physical chain and check the remaining signed steps |
| `N-108` | `notes/theory/full-band-first-mirror-flight-times.md` — One-way time throughout the closed pilot height band | G-6, G-10, Q-1, Q-16, Q-35 | N-84, N-98, N-99, N-103, N-106 | 316 signed central slabs each way and the two transverse outer collars on the same field line | 14 < T < 4450 at every height, with T below the central integral plus 40. | integrate the individual central clearances for a sharper uniform time bound |
| `N-109` | `notes/theory/rowwise-first-mirror-flight-budget.md` — Rowwise first-mirror flight budget | G-6, G-10, Q-1, Q-16, Q-35 | N-84, N-99, N-106, N-108 | 316 individual reciprocal-speed ceilings on each signed physical trajectory and an integrable collar at each end | 14 < T < 264 on the entire closed height band at every admitted angle. | quantify action increments and extend the result across launch positions |
| `N-110` | `notes/theory/full-signed-pilot-birth.md` — Full signed trace through the pilot birth | G-10, Q-16, Q-35 | N-84, N-92, N-95, N-97 | 391 physical rows each way, common approach, original contact certificates | The physical trajectory through the original birth stays within 3.327 × 10⁻⁶ of its indexed references throughout ±391/64 radians. Four first contacts on the same path. | repeat the long-field passage at a second launch |
| `N-111` | `notes/theory/reflected-secondary-defect-budget.md` — Reusing the physical central defect on the second radial label | G-10, Q-16, Q-35 | N-91, N-102, N-105, N-107 | exact reference and frame reflection, sharp forward enclosures, independent backward budget | A compiled six-slab trajectory each way at u=0.478. All 391 proposed reflected budgets pass the exact feasibility test. | finish the physical chain to the second launch’s mirror brackets |
| `N-112` | `notes/theory/local-flow-persistence-of-physical-births.md` — Openness from a single local field-line bracket | G-6, G-10, Q-1, Q-16, Q-19, Q-35 | N-97, N-100 | C¹ velocity and strength, positive alignment on an open physical tube, one transverse bracket | Open neighborhood in Cartesian position and height and positive regular-birth mass for every measure charging open sets. | exhibit a concrete physical bracket and quantify neighborhood size for a thermal distribution |
| `N-113` | `notes/theory/first-well-action-height-inverse.md` — Recovering height from the first-well action | G-10, Q-16, Q-35 | N-99, N-104, N-109 | derivative of action and two-sided flight-time bounds on the same field line | The complete action image is a closed interval and every positive action increment satisfies ΔJ/264 < Δh < ΔJ/14. | compare actions across different physical launch labels |
| `N-114` | `notes/theory/cartesian-open-regular-pilot-births.md` — Positive four-dimensional regular-birth volume in QA2R | G-6, G-10, Q-16, Q-19, Q-35 | N-95, N-97, N-99, N-100, N-112 | Cartesian field-line ODE, positive aligned chart and one transverse bracket on each actual pilot path | Every admitted angle and height gives a true interior point. Regular births have positive Cartesian position-height volume. | lift the volume statement to physical birth variables and quantify a fraction |
| `N-115` | `notes/theory/secondary-qa2r-mirror-brackets.md` — Signed physical mirror bracket tubes at the second radial label | G-10, Q-16, Q-35 | N-60, N-81, N-91, N-102 | physical field enclosures, two signed clocks and spatial-gradient enclosures | Both directions bracket the lower level at 317–318 and upper level at 325–327 in units of 1/64. Squared field strength increases outward at rate >1/400 on the bracket rows. | exclude previous contacts and join to the 328-slab birth trajectory |
| `N-116` | `notes/theory/action-floor-for-first-mirror-flight-time.md` — Joint action and flight-time bounds for the complete first well | G-6, G-10, Q-16, Q-35 | N-99, N-101, N-103, N-106, N-108, N-109 | complete signed field line, first upper well action cap, restricted 316-row speed budget | 54.98668 < T < 264 throughout the closed band, with T > 57.80606 at the upper endpoint. The action cap holds on the same well throughout. | compare action and flight estimates at the second radial label |
| `N-117` | `notes/theory/qa2r-trapped-birth-coordinates.md` — Open subsets in the contracted guiding-centre birth variables | G-6, G-10, Q-1, Q-16, Q-19 | N-99, N-100, N-112, N-114 | strict pilot birth, continuous Hamiltonian/pitch/height maps, interior reference cuts | The five-dimensional trapped reference contains an open set for each strict sign of parallel velocity and has positive mass under every measure charging open sets. | supply numerical mass coverage and a radial survival theorem |
| `N-118` | `notes/theory/first-variation-across-mirror-field-lines.md` — First variation across field-line labels | G-6, G-10, Q-1, Q-16, Q-19, Q-35 | N-85, N-93, N-104 | derivative and uniform secant control of the field profiles on a common window, two transverse first mirrors | Signed transverse action derivative and bound by A J + B T for the arclength and field sensitivities. | certify label derivatives on QA2R and attach the bounce-drift law |
| `N-119` | `notes/theory/native-harmonic-central-defects.md` — Physical central defects in a common harmonic representation | G-10, Q-16, Q-35 | N-94, N-102, N-105, N-111 | exact physical field models, the original reference and each stored signed allowance | A mixed-method physical birth chain and audited central defects at rows 4 and 317. The row-4 signed check is about 2.5 times faster. | continue the secondary trace with authenticated reusable leaves |
| `N-120` | `notes/theory/eight-signed-traces-on-common-tori.md` — Eight physical traces on one nested pair | G-10, Q-16, Q-35 | N-91, N-102, N-105, N-107, N-110, N-111 | a common torus entry and separate signed tube chains at each label | One theorem covers 974 signed slabs with both terminal enclosures at every label. | extend the shorter sectors to their own first mirrors |
| `N-121` | `notes/theory/secondary-qa2r-submirror-exclusion.md` — Incoming mirror exclusion at the second radial label | G-10, Q-16, Q-35 | N-105, N-111, N-115, N-119 | reflected physical outputs, exact coefficient shifts and grouped field signs | All 317 rows per direction are below the lower mirror height. The actual signed birth satisfies the exclusion through ±1 radian. | extend the physical path through the bracket and attach first contacts |
| `N-122` | `notes/theory/vacuum-local-littlejohn-births.md` — Local guiding-centre orbits of signed pilot populations | G-10, Q-16, Q-35 | N-99, N-114, N-117 | nonzero smooth vacuum field, pilot reference and compatible birth cuts | Exact Littlejohn denominator identity and open positive-mass sets of births admitting true local orbits for both velocity signs. | quantify a common time, excursion and birth-law fraction on specified physical scales |
| `N-123` | `notes/theory/pilot-radial-action-slope-criterion.md` — Signed physical radial action variation test | G-10, Q-16, Q-35 | N-56, N-101, N-116, N-118 | certified action and time bounds at common mirrors, and signed sensitivities of field and arclength | Lean implication gives ∂ᵤJ > 1/3 from ∂ᵤf ≤ −1/144 and ∂ᵤw ≥ −w/32. The two-label numerical screen satisfies both targets. | certify the radial tangent and both inputs on continuous physical trajectories |
| `N-124` | `notes/theory/pilot-radial-birth-variation.md` — Physical radial tangent at birth | G-10, Q-16, Q-35 | N-120, N-123, Q-16 launch inclusion | certified torus Fourier errors and pilot spatial jets | Both embedded tori and all eight signed traces share the exact initial radial tangent at u=0.470, φ=0. The strength derivative is ≤ −1/144 and density derivative is positive there. | propagate the radial tangent through the whole well |
| `N-125` | `notes/theory/common-local-littlejohn-time.md` — Common local time for both velocity signs | G-10, Q-16, Q-35 | N-99, N-114, N-117, N-122 | augmented vacuum flow, two lifted pilot births and compatible support cuts | For each displacement cap there are open signed populations, a common positive time and a positive covered fraction of every compatible measurable finite reference with an open-positive law and compact nonempty axis. | bound the time and fraction at specified physical scales |
| `N-126` | `notes/theory/finite-radial-action-comparison.md` — Finite comparison by shifting the pilot height | G-10, Q-16, Q-35 | N-99, N-101, N-104, N-113, N-116, N-120, N-121 | same-path derivative in height and flight floor, plus comparable profiles on two first wells | Actual pilot has action-width > 0.0284. Two finite comparisons would give an action increment > 1/375 at radial spacing 1/125. All 325 paired rows pass the centered external arithmetic. | replay the pairwise estimates and attach the second mirror-to-mirror path |
| `N-127` | `notes/theory/secondary-first-mirror-height-band.md` — Second-label branch across all heights | G-10, Q-16, Q-35 | N-99, N-115, N-121 | full incoming exclusion, ten closed-cell slopes per sign and exterior cap | For any joined path through the bracket the first roots cover the entire height band, move strictly between 7/64 and 10/64 radian, and have inverse derivative in (0,800h) in the interior. | attach the physical chain continuing past 327/64 |
| `N-128` | `notes/theory/paired-physical-launch-profiles.md` — True paired observables at launch | G-10, Q-16, Q-35 | N-91, N-94, N-99, N-126 | original position and field records and the common geometric section | On the same embedded invariant tori, the two true birth lines meet the field-drop and density-ratio tests throughout [−1/64,1/64] for every admitted launch angle. | propagate the comparisons out to the raised pilot first mirrors |
| `N-129` | `notes/theory/centered-strength-separation.md` — Physical field separation on a difficult paired row | G-10, Q-16, Q-35 | N-120, N-126, N-128 | original signed outputs at common time and field derivatives covering the full spatial error boxes | A centered mean-value proof gives a squared-strength drop of at least 17/144000 on both directions of row 324. All 325 rows pass the exact external screen. | reuse the centered producer on the remaining paired tubes |
| `N-130` | `notes/theory/common-torus-pilot-action.md` — Joint action calibration on the eight-sector geometry | G-10, Q-16, Q-35 | N-101, N-110, N-116, N-120, N-124, N-126 | all 326 original signed pilot rows, quadrature and first-well bounds, and the common embedded pair | A single family spanning 1,046 signed slabs contains the complete calibrated 391-row pilot at each admitted angle. | apply the finite comparison on a joined secondary well of these same surfaces |
| `N-131` | `notes/theory/outer-phase-zero-submirror-births.md` — Three signed submirror segments on common embedded surfaces | G-10, Q-16, Q-35 | N-91, N-121, N-130 | compatible physical entries and the original signed paths | The true 0.478, 0.523 and 0.531 lines stay below both heights for 64, 32 and 5 rows each way on one nested pair. | verify the complete incoming tubes and continuation to each first mirror |
| `N-132` | `notes/theory/paired-physical-arclength.md` — Paired physical arclength and strength | G-10, Q-16, Q-35 | N-94, N-126, N-128, N-129 | physical angular denominators and two signed field models at a common angle | Both signs of row 324 meet the full comparison; the least favorable arclength row 296 passes as well. | certify and assemble the remaining ordered pairs on the two actual paths |
| `N-133` | `notes/theory/opposite-section-submirror-births.md` — Four submirror births at the opposite section | G-10, Q-16, Q-35 | N-91, N-105, N-120, N-121, N-130 | independently enclosed signed coordinates in one common harmonic model and the original physical paths | All four opposite-section births lie below the lower height for 16, 5, 5 and 5 signed rows each way on the calibrated tori. | extend the paths to their own first mirrors |
| `N-134` | `notes/theory/secondary-native-lower-action-cells.md` — Lower action at the second phase-zero radius | G-10, Q-16, Q-35 | N-60, N-94, N-101, N-115, N-121, N-127 | signed field and arclength models, downward quadrature and actual first-well coverage | The central 322 pairs already exceed the upper-height action target. Four physical row pairs pass, two on the same signed birth line. | check the full central cover and attach the actual upper mirrors |
| `N-135` | `notes/theory/quantified-grouped-mirror-clearance.md` — Quantified field clearance below the lower mirror height | G-10, Q-16, Q-35 | N-121, N-131 | tight positive radial scaling and the original signed tube bounds | All 634 incoming 0.478 tubes clear the lower height by more than 1/270000. One pair of embedded tori carries quantified physical intervals at three radii. | connect the continuous physical birth path to the end of every quantified incoming prefix |
| `N-136` | `notes/theory/compared-signed-trace-prefixes.md` — Comparing two calibrated physical paths at a common angle | G-10, Q-16, Q-35 | N-110, N-126, N-128, N-129, N-130, N-132 | consecutive signed pairs and the two actual trajectories on the calibrated surfaces | Twenty rows each way give both profile comparisons on ±5/16 radian. Comparison on all 325 suffices for the finite action increment once the second first well is joined. | extend the ordered physical comparisons to the pilot upper mirrors |
| `N-137` | `notes/theory/grouped-paired-physical-profiles.md` — Grouped field and arclength comparison | G-10, Q-16, Q-35 | N-126, N-129, N-132, N-135, N-136 | common time with separate spatial remainders and certified physical gradients | Both signs of rows 236–251 and 319–324 clear the field drop and arclength tests. | finish all 13 grouped comparisons through the tenth outer bracket |
| `N-138` | `notes/theory/secondary-action-cover-from-birth.md` — Contiguous lower action on the second birth line | G-10, Q-16, Q-35 | N-115, N-121, N-127, N-134 | chronological signed physical cells, one increasing-angle trajectory, and first-well identification | A 1,536-panel Cartesian action floor is grounded at u=0.478. The upper-height first-well target follows from the 322-row cover and a signed path through 328 rows. | continue the two proof campaigns and apply the checked first-well theorem |
| `N-139` | `notes/theory/eight-action-resolutions.md` — Eight coarse exact action comparisons and four minimal lower windows | G-10, Q-16, Q-35 | N-60, N-82, N-94, N-101, N-134, N-138 | proper angular section, physical interval weights and original directed arithmetic | The eight kernel-checked packets need 67,928 physical panel enclosures in place of 250,848. Four exact lower-window cutoffs are minimal among symmetric original windows. | attach the coarser physical panels and signed first wells |
| `N-140` | `notes/theory/opposite-section-coarse-action-cells.md` — Physical coarse action panels at the opposite QA2R section | G-10, Q-16, Q-35 | N-60, N-83, N-94, N-120, N-134, N-138, N-139 | independently rounded field enclosures for both clocks at each radius | One pair of nested embedded surfaces supports the four opposite-section signed births, with 96 true enclosures covering all 384 chronological cells adjacent to the section. | continue the physical action covers and signed trajectories toward the mirror brackets |
| `N-141` | `notes/theory/submirror-prefix-projection.md` — Preserve signed paths when projecting observed prefixes | G-10, Q-16, Q-35 | N-119, N-121, N-131, N-135 | matched ordered prefix on both physical clock directions | All 160 signed pairs on the actual second birth path have field strength strictly below the lower height minus 1/270000. | apply the same complete sign archive at subsequent path checkpoints |
| `N-142` | `notes/theory/secondary-action-height-window.md` — A positive height interval for the second launch’s lower action | G-10, Q-16, Q-35 | N-127, N-134, N-138 | original physical core and genuine first mirrors for the full-well bound | The 322-pair lower packet retains a strict margin at every height within 267/2²⁷ below the upper endpoint. A 3,072-panel Cartesian integral bound is grounded over that interval. | attach the complete chronological cover and the signed mirror passage |
| `N-143` | `notes/theory/ordered-paired-profile-suffix.md` — The ordered paired comparison on the outer 89 signed slabs | G-10, Q-16, Q-35 | N-126, N-129, N-132, N-136, N-137 | synchronized signed physical tubes and thirteen shared gradient enclosures | All 89 outer indices on both clocks now have a joint field and arclength comparison on the two original physical tubes, including their common boundaries. | join the first 236 paired comparisons on the two through-birth trajectories |
| `N-144` | `notes/theory/paired-first-well-actions.md` — A finite radial secant between the first wells on two field lines | G-10, Q-16, Q-35 | N-126, N-127, N-130, N-136, N-138, N-143 | one calibrated torus family, the 325 paired bounds and the 328-slab outer trajectory | Both actual trajectories obey the physical comparisons throughout ±1 radian. A full paired cover and outer mirror passage imply a first-well action secant greater than 1/3. | assemble the complete signed family and paired cover and apply the first-well theorem |
| `N-145` | `notes/theory/secondary-near-upper-first-wells.md` — First-mirror locations and a strict action floor near the upper height | G-10, Q-16, Q-35 | N-127, N-135, N-138, N-141, N-142 | complete incoming field margins and the original signed physical passage | The true 192-pair second trajectory has Cartesian action greater than 8/25 over ±3 radians. Reaching the first mirrors raises the proved floor to 43/100 over a positive height interval. | apply the first-well bound when the 328-pair path reaches the high caps |
| `N-146` | `notes/theory/full-paired-physical-profiles.md` — Full signed field-profile comparison at the two radial launches | G-10, Q-16, Q-35 | N-126, N-132, N-136, N-137, N-143 | matched signed angles and checked physical enclosures on both sets of original tubes | All 325 slab pairs on each clock carry the physical field and arclength inequalities at the two radii. The conclusion holds pointwise on any two trajectories enclosed in the original tubes. | apply the complete comparison to the signed through-mirror trajectory at the second birth |
| `N-147` | `notes/theory/compact-regular-birth-arcs.md` — An open Cartesian tube of regular births about a complete central field-line arc | G-10, Q-16, Q-35 | N-117, N-122, N-125, N-127, N-130, N-138 | transverse outward branches, a larger signed physical domain and regular Cartesian field geometry | A single positive position-height radius works along the pilot’s whole central arc through ±316/64 and throughout the closed height band. The second radius has the same proved implication on ±317/64 once its path reaches the exterior caps. | ground the second central arc on the signed through-mirror family |
| `N-148` | `notes/theory/second-phase-zero-coarse-action.md` — Sixteen-panel physical action bounds at the second phase-zero launch | G-10, Q-16, Q-35 | N-120, N-134, N-138, N-139, N-140 | the signed physical birth, matching lower quadrature packet and its checked phase-zero reflection | Sixteen genuine physical enclosures cover both launch clocks by reflection. A proved transfer reuses finer lower cells, and the coarser full-core target needs 325 pairs. | join direct and transferred physical blocks through both upper-height first mirrors |
| `N-149` | `notes/theory/compared-physical-birth-arcs.md` — A 3.5-radian field comparison on two physical birth trajectories | G-10, Q-16, Q-35 | N-130, N-131, N-135, N-138, N-145, N-146, N-148 | actual signed ODE enclosures, matched physical tubes and a common embedded torus pair | The two physical birth lines satisfy both profile inequalities throughout ±3.5 radians. One embedded family contains 1,482 signed steps. A 65-pair signed action integral has a physical lower bound from 6,240 cells. | reach both first mirrors at the second birth and apply the finite secant theorem |
| `N-150` | `notes/theory/compact-littlejohn-arc.md` — A shared guiding-centre time for a compact family of trapped births | G-10, Q-16, Q-35 | N-117, N-122, N-125, N-147 | a compact family in a regular vacuum field and interior support, height and energy cuts | One positive time and one open neighborhood work for every position on a physical pilot arc, every certified height, both velocity signs and every energy in a compatible positive closed interval. | bound this time at a physical operating point or extend uniformity to all launch phases |
| `N-151` | `notes/theory/lower-mirror-branches-at-two-more-radii.md` — First lower-height mirror brackets at two further phase-zero radii | G-10, Q-16, Q-35 | N-115, N-126, N-131 | complete prehistory, signed caps, two bracket slopes and through-going ODE trajectories | At u=0.523 and 0.531, the signed lower first mirrors are simple in brackets (322,324)/64 and (323,325)/64, conditional on their physical trajectories reaching the bracket. Both-height caps passed. | verify all intervening slopes and attach each original signed trajectory |
| `N-152` | `notes/theory/grouped-moving-frame-jacobians.md` — A shared spatial Jacobian on consecutive physical trial tubes | G-10, Q-16, Q-35 | N-102, N-105, N-111, N-119, N-137 | physical polynomial identities, affine model inclusions and the original signed frame data | Four shared field enclosures prove the original moving-frame growth bounds on both clocks for all 48 rows 280–327 at u=0.478. An identical-row replay reduced amortized compilation time from 184.743 to 29.259 seconds. | extend the signed continuation through the first mirrors using the shared spatial bounds and the independent central defects |
| `N-153` | `notes/theory/opposite-section-physical-mirror-caps.md` — Signed physical mirror brackets at the opposite section | G-10, Q-16, Q-35 | N-107, N-115, N-133 | signed physical Taylor models of the strength gap at original cap nodes | At the four opposite-section launches, 32 physical cap signs imply 16 crossings for any continuous signed strength paths meeting their corresponding tubes. | attach the through-going trajectories, exclude earlier contacts, and quantify regular mirror heights |
| `N-154` | `notes/theory/common-time-across-pilot-launches.md` — A common guiding-centre time across all pilot launch phases and central arcs | G-10, Q-16, Q-35 | N-106, N-147, N-150 | a compact regular vacuum enclosure and physical pilot arcs throughout the admitted launch window | One positive orbit-control time works across the entire original launch-angle interval and every central pilot arc, both velocity signs, every height and every energy in a compatible positive closed interval. | quantify a useful time and transport allowance or apply the same argument to verified exterior births |
| `N-155` | `notes/theory/four-opposite-incoming-field-profiles.md` — Field strength before the first mirror brackets at all four opposite-section launches | G-10, Q-16, Q-35 | N-133, N-138, N-153 | exact signed tube memberships, harmonic field enclosures and a calibrated birth family | All 2,586 incoming signed physical tubes lie strictly below the lower height at the four π/2 launches. On one embedded pair the signs attach to actual prefixes of 48, 16, 8 and 5 slabs each way. | attach the completed trajectories through the four mirror brackets |
| `N-156` | `notes/theory/second-first-well-polynomial-floors.md` — Polynomial lower bounds for the second QA2R first-well action | G-10, Q-16, Q-35 | N-129, N-134, N-137, N-138, N-148 | two signed physical field models, a native central cover and first-mirror timing | The actual upper-height action at the second radial birth is at least 1.3618404, above the archived absolute target by more than 0.0019182. | combine the outer floor with the inner ceiling on one calibrated pair of trajectories |
| `N-157` | `notes/theory/signed-moving-frames-beyond-mirror-caps.md` — Independent signed moving frames on a shared group of physical slabs | G-10, Q-16, Q-35 | N-102, N-105, N-107, N-119, N-152 | separate signed clocks, original signed frame allowances and independent residual proofs | A single physical field enclosure now handles genuinely different original forward and backward moving frames at the opposite section. Both original ODE steps pass at row 129. The six further routes screen in 171 groups over 2,007 indices. | replay all six signed continuations beyond their exterior caps and apply the mirror theorems |
| `N-158` | `notes/theory/common-original-birth-margins.md` — Field-strength margins on four physical births of one phase-zero torus family | G-10, Q-16, Q-35 | N-135, N-141, N-147, N-149 | one embedded family, original birth uniqueness, and the three signed field margins | Three true trajectories through their original interpolated births simultaneously carry strict height clearance through ±4, ±3/4 and ±1/4 radians at u=0.478, 0.523 and 0.531. The same embedded pair carries the calibrated pilot. | ground these paths through their respective first mirrors |
| `N-159` | `notes/theory/first-mirrors-regular-values.md` — First mirror heights from topology and the area formula | G-10, Q-16, Q-35 | Trajectory slab first contact, Mathlib one-dimensional area formula | two capped scalar profiles and differentiability for the measure bounds | First contacts increase strictly and are left-continuous. Almost all heights have two transverse contacts. The height measure with either slope at most m is at most m times the sum of the two bracket widths. | derive these hypotheses on signed physical QA2R passages |
| `N-160` | `notes/theory/joint-regular-launch-arcs.md` — One guiding-centre time for two radii and all launch phases | G-10, Q-16, Q-35 | N-127, N-147, N-150, N-154 | compact regular birth families and the two actual through-going mirror passages | A single positive local time covers the central arcs at u=0.470 and 0.478, every admitted launch phase, both velocity signs, the full height band and the chosen positive closed energy interval. | obtain numerical time or measure bounds for a specified population |
| `N-161` | `notes/theory/two-physical-first-well-actions.md` — Action variation between two physical QA2R first wells | G-10, Q-16, Q-35 | N-126, N-127, N-144, N-146, N-149, N-158 | 325 paired profiles and the physical second line through both first mirrors | On the actual inner and outer field lines the equal-height action gap exceeds 1/375 and the radial secant exceeds 1/3 wherever the shifted height also fits the archive band. | bound the upper-endpoint secant using absolute action bounds on the same two paths |
| `N-162` | `notes/theory/upper-height-radial-action-secant.md` — Equal-height radial action secant at the upper mirror height | G-10, Q-16, Q-35 | N-144, N-156, N-161 | use both absolute bounds on the very same chosen trajectories | At the upper endpoint the same two physical lines bracket the target. Their action difference exceeds 1/250 and the radial secant is at least 0.50624. | extend a common secant bound to the remaining upper part of the height band |
| `N-163` | `notes/theory/independent-harmonic-central-defects.md` — Independent harmonic ODE residuals at the opposite section | G-10, Q-16, Q-35 | N-102, N-107, N-119, N-157 | original signed central curves, frames and residual allowances | Both physical ODE defects at opposite-section slab 129 are 3.10 times faster to verify with seven harmonics. All 2,664 signed proposals pass exact external screening. | certify the other six trajectories through their respective mirror caps |
| `N-164` | `notes/theory/physical-first-mirror-values.md` — First-mirror height measure on physical QA2R field lines | G-10, Q-16, Q-35 | N-106, N-127, N-153, N-155, N-159 | original signed passages, checked cap and incoming signs, positive toroidal field on the physical tube | On each actual u=0.478 path both first-contact slopes exceed 1/1250 on at least 51.639% of the archived height band. Four π/2 applications now require just the signed path through their caps. | extend the four opposite-section trajectories to their exterior caps |
| `N-165` | `notes/theory/closed-height-band-action-secant.md` — An equal-height action gap throughout the closed mirror-height band | G-10, Q-16, Q-35 | N-116, N-144, N-146, N-147, N-156, N-161, N-162 | paired field and arclength comparisons, a pilot action upper bound and the signed physical arclength floor | Across the entire closed height band, the same physical outer first well contains the inner well, its Cartesian action exceeds the inner action by more than 2/625, and the radial secant exceeds 2/5. | establish continuous first-well action across the intervening radial interval |
| `N-166` | `notes/theory/grouped-physical-central-defects.md` — Grouped physical central defects for the phase-zero continuations | G-10, Q-16, Q-35 | N-105, N-111, N-119, N-152, N-157 | shared harmonic time models, individual signed frames and original defect budgets | A degree-twelve common field model verifies twelve signed original residuals in 199.813 seconds against 465.098 seconds on the same rows. All 675 paired row budgets pass exact external preflight. | continue the original physical trajectories across larger radius and test independent shifted-section groups |
| `N-167` | `notes/theory/prescribed-first-well-action-or-grazing.md` — A prescribed first-well action or a grazing first mirror | G-10, Q-16, Q-35 | N-69, N-144, N-159, N-162 | jointly continuous field and arclength density and common strict exterior caps | In a connected family with strict caps and opposite endpoint action signs, the target action occurs or a first mirror is a local maximum of its field. The two physical QA2R endpoint inputs are discharged. | certify a continuous through-going physical family and exclude grazing between the two original radial labels |
| `N-168` | `notes/theory/height-sampling-first-mirrors.md` — Sampling heights with two steep first mirrors | G-10, Q-16, Q-35 | N-159, N-164 | Borel measurability of the two-slope event and the physical bracket-width budget | The two-slope event on the actual second original line has at least 51.6391% probability under uniform height. A density envelope on the failed set controls the result under a change of law. | identify a physical sampling law, or extend the four opposite-section trajectories to apply their sharper probability bounds |
| `N-169` | `notes/theory/upper-radial-ribbon-entry-and-caps.md` — Four physical entry balls and a common high cap for the upper radial bracket | G-10, Q-16, Q-35 | N-60, N-65, N-120, N-156, N-162, N-167 | Sharp Q-16 launch bounds and signed endpoint proposals. | All radii in [0.470, 0.478] have physical entries on the same two tori. The original field is strictly above the upper height on all eight end-cap tubes. | Prove the original ODE stays inside the signed tubes and exclude grazing on every possible contact slab. |
| `N-170` | `notes/theory/grouped-opposite-section-ode-defects.md` — Grouped independent ODE residuals on both clocks at the opposite section | G-10, Q-16, Q-35 | N-107, N-119, N-152, N-157, N-163, N-166 | separate signed harmonics, deviations, frame and quotient data on each original clock | A grouped harmonic proof checks sixteen independent signed residuals on the same eight original rows 3.17 times faster than separate runs. Both physical steps on row 49 pass. | carry grouped original ODE proofs through the four opposite-section mirror caps |
| `N-171` | `notes/theory/radial-field-line-continuation.md` — Continuous field-line families across the upper action bracket | G-10, Q-16, Q-35 | N-162, N-167, N-169 | Independent original endpoint action bounds and common torus entries. | Continuous dependence and endpoint identification follow from the physical ODE. Through-going paths with strict cap signs imply a prescribed action or a grazing first mirror. | Continue the four physical tubes and prove simple first contacts on their full radial interval. |
| `N-172` | `notes/theory/radial-ribbon-mirror-orientation.md` — Outward orientation of both mirror collars across the radial bracket | G-10, Q-16, Q-35 | N-130, N-151, N-167, N-169 | Original QA2R physical numerator, signed radial packets and harmonic enclosure bounds. | All 112 signed tubes in [317/64,331/64] have outward squared-strength derivative above 1/16384. All four initial eight-row prefixes lie below the upper height. | Join the full lower-field histories and all four physical through-cap paths to obtain simple mirrors. |
| `N-173` | `notes/theory/radial-ribbon-central-defects.md` — Central ODE defects for the continuous radial birth interval | G-10, Q-16, Q-35 | N-119, N-166, N-169 | Signed radial packets and the harmonically grouped physical field calculation. | Lean checks the first eight rows in both directions on all four widened birth intervals. Exact replay covers all 2,656 central budgets for the longer proof. | Complete all 168 groups of signed central defects and compose with the verified spatial and scalar bounds. |
| `N-174` | `notes/theory/eight-launch-signed-checkpoint.md` — Eight original launches on a common pair of tori through 1,998 signed slabs | G-10, Q-16, Q-35 | N-155, N-158, N-161, N-170 | Eight original signed paths and the calibrated pilot and paired observables. | The 1,998-slab snapshot extends original-birth margins to ±2 and ±1/2 radians at 0.523 and 0.531. Opposite-section paths have 48, 32, 16 and 24 verified slabs each way. | Extend all six unfinished secondary paths through their own mirror brackets. |
| `N-175` | `notes/theory/radial-ribbon-through-chains.md` — Two-sided physical field lines from four radial birth intervals | G-10, Q-16, Q-35 | N-65, N-119, N-169, N-171, N-173 | Original signed packets, central residuals, logarithmic norms and scalar step certificates. | For every point of four section balls, a single original field line follows 16 slabs each way. All 2,656 proposed tubes lie inside the regular spatial domain. | Complete all eight 332-slab chains and attach the high caps and mirror slopes. |
| `N-176` | `notes/theory/four-section-prescribed-action-criterion.md` — Four section checks suffice for an original birth at the prescribed action | G-10, Q-16, Q-35 | N-162, N-167, N-169, N-171 | Signed ODE uniqueness and the actual two endpoint action certificates. | For every original phase near zero, four universal section-ball checks suffice to give a strictly interior torus-interpolated birth at the exact action, with two transverse first mirrors. | Discharge all four signed section obligations using the physical central and spatial row proofs. |
| `N-177` | `notes/theory/integer-horner-taylor-defects.md` — Integer Horner certificates for rounded Taylor models | G-10, Q-16, Q-35 | N-94, N-166, N-170, N-173 | Common fixed-point scale and exact integer bounds on polynomial convolution and rounding. | Identical physical models and original signed budgets verify 1.51× faster for a complete central group and 1.89× faster for a shared nine-field spatial jet. | Use the verified integer path for remaining physical field and gradient groups and preserve prior authenticated work. |
| `N-178` | `notes/theory/compact-sector-first-well-actions.md` — A compact target-action set over launch phase and radius | G-10, Q-16, Q-35 | N-167, N-169, N-171, N-176 | Embedded torus birth data, the physical endpoint comparison and the signed section criterion. | Continuous moving-clock ODEs and transverse first wells imply a compact exact-action set over the full phase–radius rectangle. It has an interior radial representative at every phase. | Discharge the long signed section conditions and investigate connected continuation of the action level. |
| `N-179` | `notes/theory/accessible-radial-birth-window.md` — The original radial births share an accessible interval around phase zero | G-10, Q-16, Q-35 | N-169, N-171, N-172, N-175, N-176 | Common torus entries, four signed sixteen-row paths, and first eight signed row exclusions. | Every original birth in the full small phase–radius rectangle is on a regular signed physical line with field below the upper mirror height throughout [−1/8,1/8]. First wells around zero also contain the birth phase. | Extend original-field propagation to the mirrors at 331/64 and use the same accessible component for the action test. |
| `N-180` | `notes/theory/connected-rectangle-action-level.md` — A connected action level across a radial launch bracket | G-10, Q-16, Q-35 | N-178 (application context) | Brouwer fixed point on compact convex sets and compact Hausdorff component separation. | Browder continuation gives a compact connected subset of a continuous target level projecting onto the entire phase interval under opposite radial-face signs. | Apply the rectangle result to the original physical endpoint faces and jointly continuous action. |
| `N-181` | `notes/theory/radial-ribbon-through-cap-signs.md` — First-mirror signs on the four complete radial tube sequences | G-10, Q-16, Q-35 | N-167, N-169, N-171, N-172, N-176 | Canonical four-tile signed packets, compensated slope bounds and exact upper-height exclusion. | The four complete radial packets imply both first-contact transversality and all three field signs. Lean checks all 2,536 incoming tubes, 112 signed collar tubes and eight caps. | Supply the original joined physical solutions through all 332 signed rows each way. |
| `N-182` | `notes/theory/radial-sector-face-actions.md` — Strict endpoint actions on both radial faces of the phase sector | G-10, Q-16, Q-35 | N-162, N-169, N-171 | Actual endpoint wells and arclength actions, verified original positions and uniqueness on the overlap. | For every phase near zero the endpoint inequalities hold on any regular long family through the original two births. The same embedded tori supply the intermediate entries and sector criterion. | Apply the compact connected rectangle crossing to the original two face signs. |
| `N-183` | `notes/theory/radial-sector-through-trajectory-criterion.md` — The signed trajectories are the remaining input to physical radial action attainment | G-10, Q-16, Q-35 | N-175, N-176, N-178, N-181 | Candidate-specific field and derivative histories and original two-endpoint sector attachment. | With all four 332-slab signed field-line solves, the original radial sector has a compact physical target-action set meeting every phase. All signs, comparison and continuity inputs are discharged. | Complete and authenticate the full 332-row through theorem to discharge the trajectory hypothesis. |
| `N-184` | `notes/theory/connected-original-birth-action-level.md` — A connected set of original births at the prescribed first-well action | G-10, Q-16, Q-35 | N-178, N-179, N-180, N-182, N-183 | Actual two-face action signs, full signed observations, accessible original births and continuous sector action. | The through-trajectory hypothesis implies one compact connected set of true birth-centered target wells covering the full phase sector, with common positive radial clearance from both faces. | Close the four long signed trajectories and quantify continuation toward the full phase circle. |
| `N-185` | `notes/theory/connected-periodic-action-separator.md` — A connected periodic action level separating the two boundary circles | G-10, Q-16, Q-35 | N-180 | Continuity and strict oriented action bounds on both faces over the entire phase circle. | A continuous full-period action with strict opposite face signs has a compact connected exact level separating the boundary circles. Its inclusion in the annulus is essential. | Determine domains of valid periodic first-well coordinates and test the global face hypotheses. |
| `N-186` | `notes/theory/radial-ribbon-mirror-height-band.md` — Transverse first mirrors and physical flight times over a height band | G-10, Q-16, Q-35 | N-169, N-172, N-175, N-179, N-181 | Enclosed signed paths over all 332 slabs on all four section balls. | The four through-going physical trajectories give two transverse first mirrors and 14 < T < 10000 for normalized one-way Cartesian flight time on the full closed height interval of width 1/18750. | Combine the height and action intervals and discharge the long trajectories. |
| `N-187` | `notes/theory/radial-ribbon-matrix-certificates.md` — Integer frame arithmetic and smaller time covers for the radial family | G-10, Q-16, Q-35 | N-169, N-173, N-175, N-177 | Original dyadic moving frames, genuine field Jacobians, and exact bounds for each signed radius. | On eight original signed slab pairs, exact integer frame checks and fewer time panels reduce spatial proof time from 44.678 to 24.592 seconds. All sixteen original physical ODE steps recheck. | Complete the remaining physical trajectories with the faster authenticated matrix certificates. |
| `N-188` | `notes/theory/radial-sector-prescribed-action-band.md` — A common interval of prescribed actions across the original launch sector | G-10, Q-16, Q-35 | N-162, N-178, N-179, N-180, N-182, N-183, N-184 | Physical endpoint actions and a continuous, enclosed through-going family on the four radial tiles. | The verified endpoint actions strictly bracket an interval of width 1/250. Each continuous phase-dependent target in that interval has a connected exact level once the four trajectories reach their caps. | Compose the completed physical trajectories and extend the certified prescription range to varying heights. |
| `N-189` | `notes/theory/fused-signed-endpoint-matrices.md` — Faster signed endpoint matrix certificates on the six original launches | G-10, Q-16, Q-35 | N-174, N-177, N-187 | Original physical endpoint packets, separate signed clock frames and authentic kernel receipts. | Fused field and signed matrix certificates reduce measured kernel time by a factor of 2.795 on twelve opposite-section rows. Each of the six endpoint labels passed separate forward and backward physical IVPs before switching. | Continue the six original trajectories to their first mirrors and measure whole-campaign throughput. |
| `N-190` | `notes/theory/opposite-section-excludes-pilot-action-strip.md` — The original radial action strip misses the target on the opposite section | G-10, Q-16, Q-35 | N-56, N-59, N-60, N-185 | Original enclosed signed first-well actions on seven opposite-section cells for the physical use of the Lean implication. | Seven directed-arithmetic radial cells put the whole narrow strip above the target at a quarter-turn. Lean checks their coverage and arithmetic margins. Replaying the seven physical action floors inside Lean remains open. | Prove the original physical action floors in Lean and test the wider full-period face bounds. |
| `N-191` | `notes/theory/radial-passing-speed-core.md` — A uniform parallel-speed floor along the original radial family | G-10, Q-16, Q-35 | N-169, N-172, N-175, N-179, N-186 | 128 joined signed rows and a tightened squared-field bound through 118 rows in each direction. | For every original birth in the launch rectangle a true physical ODE holds through ±127/64. On ±59/32 the field is below 132/125 and the normalized parallel speed exceeds 1/12 at every archived height. | Extend the positive-speed core and the four through-going physical solutions toward the first mirrors. |
| `N-192` | `notes/theory/height-action-rectangle.md` — A rectangle of prescribed heights and actions on the radial birth sector | G-10, Q-16, Q-35 | N-178, N-180, N-184, N-186, N-188 | The 332-row signed physical path family on the four original seed balls. | At once for all continuous height and action prescriptions in the closed rectangle, the joined long trajectories give connected sets of true birth-centered first wells. Their mirror endpoints and Cartesian actions vary jointly continuously. | Discharge the four signed trajectories and transfer the first-well estimates to wider sectors. |
| `N-193` | `notes/theory/eight-launch-signed-continuation.md` — Eight original launches through 2,590 signed physical slabs | G-10, Q-16, Q-35 | N-151, N-162, N-174 | Independent original signed ODE chains and archived field and arclength bounds. | The six secondary physical paths now extend 224, 96, 96, 64, 48 and 48 slabs each way at the two sections. Together with the two completed mirror launches, 2,590 signed slabs share the same original tori. | Continue the six unfinished endpoint paths to their actual mirror brackets. |
| `N-194` | `notes/theory/original-radial-passing-time.md` — A physical travel clock on the nonturning segment of each original birth | G-10, Q-16, Q-35 | N-191 | True signed initial field lines and quantitative bounds on parallel speed and Cartesian arclength density. | Throughout the archived height band, the true normalized parallel travel time from each original birth has a unique angular position for every signed time of absolute value at most 966655/1048576. | Extend the clock toward the mirrors and tackle cross-field guiding-centre action drift. |
| `N-195` | `notes/theory/opposite-inner-action-subwell.md` — A positive action core at the opposite-section inner birth | G-10, Q-16, Q-35 | N-139, N-190 | Signed physical observable covers through 320 rows per clock on the new original launch and an enclosed birth well for its full physical action. | For the genuine singleton launch at a quarter-turn, 320 row pairs already give an exact action floor above target. Lean checks all 15,360 quadrature panel inequalities and the reduction to actual tube covers and an enclosed birth well. | Complete the remaining physical observable covers and signed ODE bindings on the singleton launch. |
| `N-196` | `notes/theory/wide-original-birth-strength.md` — The original QA2R births lie below both mirror heights on two wide sectors | G-10, Q-16, Q-35 | N-56, N-61, N-79, N-190 | Original common-torus launch coordinates, sector polynomial field enclosures and geometric angle bounds. | Every original birth on the same two nested embedded tori at labels 0.44–0.54 has field strength below both heights for phases within 1/32 of zero or π/2. The combined phase width is 1/8 radian. | Develop original-birth enclosures beyond these two sectors and test the wider radial action faces. |
| `N-197` | `notes/theory/balanced-ribbon-defect-campaign.md` — Balancing the central and spatial proofs of the long radial trajectories | G-10, Q-16, Q-35 | N-173, N-175, N-177, N-187, N-189 | Authenticated central and spatial row receipts, process-exclusive scheduler locks and reserved workstation resources. | With the same observed 7.97 CPU cores, coordinated scheduling advanced 224 genuine physical row pairs in eight minutes versus 88 before. Immutable eight-row chain segments can be joined as soon as their physical inputs pass. | Finish the four physical trajectories and join their signed chains through both caps. |
| `N-198` | `notes/theory/periodic-original-birth-strength.md` — Submirror strength at every original birth over the full QA2R field period | G-10, Q-16, Q-35 | N-56, N-79, N-190, N-196 | Uniform original KAM torus enclosures, the finite Fourier launch profiles and periodic compensated field certificates. | Every real launch phase and every radius label 0.44–0.54 on one original pair of nested embedded tori have physical field strength strictly below the lower mirror height. Thirteen exact angular field groups cover one complete period. | Prove an explicit signed ODE collar at every phase and establish the action bounds on the broad radial faces. |
| `N-199` | `notes/theory/physical-face-action-exit.md` — A measured action-drift budget for a first radial exit | G-10, Q-16, Q-35 | N-58, N-162, N-171, N-182, N-188 | Completed physical endpoint traces and first-well actions. The orbit application requires its own drift bound and phase/face identification. | The true first-well actions on the two completed physical faces give an exit budget 19/10000. A path whose initial mismatch plus action drift fits the budget and whose potential exit observes the physical face value stays strictly inside. | Verify a corrected action and its residual on an actual guiding-centre band. |
| `N-200` | `notes/theory/radial-passing-240.md` — The full radial birth family through 240 slabs in both directions | G-10, Q-16, Q-35 | N-175, N-191, N-194, N-197 | The 240-row physical join and exact incoming field estimates through row 237. | All four original radial tiles have 240 physical slabs each way. Their ordinary ODE holds through ±239/64, and the parallel-speed floor and quantitative travel clock extend to ±237/64. | Complete the four signed paths through both outer caps. |
| `N-201` | `notes/theory/uniform-radial-action-windows.md` — Uniform radial measure for approximate first-well action | G-10, Q-16, Q-35 | N-180, N-186, N-188, N-192 | A continuous observable on a compact parameter space times a nondegenerate radial interval, and an attained target in each fiber. | For a continuous action on compact parameter fibers, every positive tolerance admits a common interval length around attained values. Lean applies this to true first-well actions on the small QA2R sector conditional on the long trajectories. | Discharge the long physical trajectories and quantify the candidate radial continuity modulus for a numerical sampling fraction. |
| `N-202` | `notes/theory/outer-physical-face-flight.md` — Flight time and action response on the completed outer radial face | G-10, Q-16, Q-35 | N-122, N-162, N-188, N-199 | Both independent signed ODEs and regular first mirrors on the completed outer face. | On each original outer-face birth, dJ/dh equals the actual one-way flight time throughout the archived band. In its top 10⁻⁵ this time is below 452, giving a quantitative lower action bound at varying heights. | Transfer the two physical face inequalities to a wider window of admissible first-exit heights. |
| `N-203` | `notes/theory/periodic-original-fieldline-collar.md` — A signed nonturning field-line collar for every original QA2R birth | G-10, Q-16, Q-35 | N-56, N-196, N-198 | Signed rectangular physical ODE existence on a periodic cover of the entire original launch chart. | All phases and all original labels 0.44–0.54 have a true signed magnetic field-line segment through ±1/256 radian, with strength below hL−1/1000 and poloidal coordinate excursions at most 1/1536. | Enclose physical action on the wide radial faces and determine where their original first-well branches continue. |
| `N-204` | `notes/theory/opposite-inner-physical-trace.md` — An original opposite-section action trajectory and a resumable physical campaign | G-10, Q-16, Q-35 | N-189, N-190, N-195, N-197 | Original opposite-sector birth seed, separate clock matrices and central defects, physical action enclosures. | All 320 original signed row pairs and their 15,360 action panels are joined on the same physical trajectory. On every qualifying first-well observation at the upper height J exceeds the target by more than 0.0003. | Campaign complete on 26 November. The full-period and thermal claims remain open. |
| `N-205` | `notes/theory/completed-original-radial-sector.md` — Connected first-well action levels on one actual QA2R radial sector | G-10, Q-16, Q-35 | N-169, N-175, N-181, N-183, N-184, N-186, N-188, N-192, N-197, N-201 | All four original 332-row signed ODE paths, signed physical observations, endpoint action enclosures and the topological crossing theorem; all discharged. | All 2,656 signed physical ODE steps are joined. Compact connected sets of true birth-centered wells realize the prescribed heights and actions over the entire small sector, with uniformly positive radial sampling mass at any positive tolerance. | Extend from the local sector to further measured phases and obtain a guiding-centre action-drift bound and a numerical population estimate. |
| `N-206` | `notes/theory/varying-height-first-exit.md` — A radial first-exit bound with varying mirror height | G-10, Q-16, Q-35 | N-199, N-202, original whole-height pilot action cap | Physical observations at a possible first exit in the certified phase and height rectangle, with a bound on pre-exit action drift. | The actual inner and outer first-well actions exclude radial first exit under the closed drift budget 249/250000 throughout the top two millionths of the height band. | Derive the pre-exit drift bound for an actual guiding-centre model and extend the two-face inequalities in phase. |
| `N-207` | `notes/theory/original-endpoint-first-mirror-continuations.md` — First mirror branches from the original phase-zero birth at 0.523 | G-10, Q-16, Q-22, Q-35 | N-120, N-131, N-189, checked endpoint caps and outward slopes | The same signed physical trajectory must support both mirror histories and the original section entry. | An approach from each original birth reaches a common section where both first-mirror time functions are proved on one field line over the full archived height interval. The signed path spans 337/64 radians each way. | Finish the u=0.531 and quarter-turn trajectories, then quantify the actions of their wells. |
| `N-210` | `notes/theory/stellarator-conditions-after-sector-closure.md` — Stellarator conditions after the first-well sector proof | G-8, G-10, Q-20, Q-31, Q-35 | N-69, N-198, N-199, N-201, N-202, N-203, N-205, N-206 | C1, physical first-well and first-exit statements on a common candidate. | The two-torus C1 and vacuum-equilibrium results are established. The local C2 action construction now closes; quantitative guiding-centre drift and thermal population coverage remain open. | Test phase coverage and prove a physical action-drift bound before selecting thermal targets. |
| `N-212` | `notes/theory/phase-dependent-radial-faces.md` — Action levels between phase-dependent radial faces | G-10, Q-35 | N-185, N-190, first-exit lemma | A continuous action on the moving strip with strict opposite signs on its boundary graphs. | Strict brackets on continuous moving faces give a compact connected, angularly essential exact-action set meeting every passage. There is a corresponding first-exit theorem for time-dependent faces. | Construct phase-dependent physical face brackets at the outstanding QA2R phases. |
| `N-213` | `notes/theory/band-form-fixed-inputs.md` — The band form of C2 with fixed inputs | G-10, G-8, Q-35; AW-H3, AW-M3, AW-M4 | N-53 | The compiled `GuidingCentreBand` and its loss bound. | `BandSpec`, `BandSpec.Admissible`, `MeetsBand`, `BandContract` (default build); regressions reject point-mass birth laws and the non-Maxwell fixture. No positive instance; C2 remains open. | Prove `MeetsBand` for an admissible specification: a horizon bound independent of the excursion cap. |
| `N-214` | `notes/theory/label-drift-and-sector-scales.md` — Label drift of guiding centres and the scales of the QA2R first-well sector | G-10, G-8, Q-35, Q-1 | N-53, N-122, N-205, N-206, N-210, N-213 | The Littlejohn model, the vacuum identity `B*_∥ = ‖B‖`, the first-exit theorem with its `Observes` and `drift` hypotheses. | `LabelDrift.label_hasDerivAt`, `rate_vacuum`, `abs_rate_vacuum_le`, `label_displacement_le` (default build). Untrusted screen: banana excursion ≈ 25 ε and precession ≈ 55 ε per half bounce against a strip of 8.4·10⁻⁵ and a phase window of 9.2·10⁻⁹; thermal particles leave the certified sector in about 5·10⁻¹⁰ s. The local sector cannot carry a thermal band. | Certified label gradients on the signed traces; wider radial windows; full-period wells with moving faces (N-212); an averaged drift estimate with a corrector. |
| `N-215` | `notes/theory/lipschitz-labels-and-backward-bounds.md` — Lipschitz labels: guiding-centre drift without flow derivatives | G-10, Q-35 | N-214, N-66 | The Littlejohn model; the sign of the logarithmic-norm bound in `FieldBounds`. | `LipschitzLabel.displacement_le`, `LabelDrift.velocity_vacuum`, `norm_drift_le`, `lipschitz_displacement_le` (default build). Correction to N-214: the slab certificates bound growth away from the section only, so label Lipschitz constants are not available. Untrusted constants: K ≈ 1.86, direct bound ≈ 93 ε per half bounce. | A lower logarithmic-norm bound per slab, a two-sided Grönwall step, and traces on a grid of section points; best done with the enlarged campaign of N-214. |
| `N-216` | `notes/theory/wide-tube-label-campaign.md` — Wide-tube label campaign for QA2R: screen and design | G-10, G-8, Q-35 | N-213, N-214, N-215 | The Lipschitz-label drift theorem; the moving-frame slab format; campaign receipts. | Stage 1 done (untrusted screen): a thin-tube grid would cost 10⁵–10⁶ CPU-hours; tubes of frame radius 10⁻³ keep \|μ\| ≤ 0.034 and a label constant below 2, so one coarse trace per direction can carry a thermal-electron bounce. No certificate yet. | Stage 2: flow label on a tube from two-sided bounds (Lean theory). Stage 3: slab certificate with a lower bound, pilot of 8 slabs per direction first. |

Main dependency edges: N-9 → N-10 → N-14 → N-15 → (Q-4, Q-5); N-10 → N-13 → (N-16 → Q-2, Q-14);
N-4 → (N-8, N-7 → N-17 → Q-1); N-12 → (Q-3, Q-14, Q-16) → G-4; N-4 → Q-16 → G-6; N-2, N-6 → Q-10 → G-2, G-7;
N-19 → Q-7 → Q-8 → Q-11 → G-8.
Contract edges (30 October 2026): Q-21 → (Q-19, Q-16, Q-18) → G-10, G-1; N-9 → N-10 → Q-19 → G-10;
Q-14 → Q-20 → G-4; G-10 → Q-22 → Q-15 → G-2; (G-1, G-4, G-10) → G-8.
Kinetic/coil brief edges (4 November 2026): N-36 → (N-37 ⊸ N-32; N-38 ⊸ N-5, N-6 → Q-26 → G-2; N-39 ⊸ N-19 → Q-27 → G-7; N-40 ⊸ N-20 → Q-28 → G-2, G-11) (⊸ = patch or method for).

### RG.4 Strict audit status

The canonical first command is `start` (skill `plasmalean-audit-domain`). Previous code is in scope.

| Audit | Value |
| --- | --- |
| Audited commit | **`6ceca0e` (complete refresh audit, 23 November 2026, of all changes since `921a8c3`; record [`notes/audit/2026-11-23-refresh-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-23-refresh-audit.md); findings AV-*)**; before that `921a8c3` (refresh audit, 31 October 2026, of all changes since `cda8bd0`; record [`notes/audit/2026-10-31-refresh-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-31-refresh-audit.md)); before that `cda8bd0` (first strict audit, 30 October 2026) |
| Latest refresh audit | **`0bec221` (refresh audit, 25 November 2026, of all changes since `6ceca0e`; record [`notes/audit/2026-11-25-refresh-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-25-refresh-audit.md); findings AW-*)**: no critical finding; 3 high (AW-H1 headline C2 declarations generated outside the repository, resolved; AW-H2 not reproducible from the repository, resolved; AW-H3 the band form of C2 admits instances without confinement content), 14 medium and 16 low. Commands: default build current (11,949 jobs), the 180 on-demand modules built, `check_axioms.lean` passed for 55,063 declarations, task server tested |
| Subsequent scoped review | At `4b0bf64`, all eight N-51 modules, N-52 and its candidate uses, and the later N-48 public interfaces and selected proofs were reviewed. The review corrects the coil-source restriction and records coverage and clock caveats. [Audit record](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-23-annulus-embedding-audit.md) |
| Mirror-action scoped review | The N-60 review covers the N-58–N-60 confinement and graph statements, the two signed field-line traces, both height and radius conventions, the 16-tile composition and its scope. The new code shares the kernel and toolchain of §RG.4. Standard-axiom audits passed for 53,665 default and 60,332 on-demand declarations. [Assumptions and scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-local-action-graphs.md) |
| Scope | full startup audit: all six kernel modules; repository scans; headline-claims trace; note-to-code links; certificate soundness |
| Kernel coverage | every kernel declaration reviewed (52: 28 definitions, 11 laws with 48 fields, 3 predicates, 10 theorems), record [`notes/audit/2026-10-30-kernel-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-kernel-audit.md) |
| Commands run | `lake build --no-build PlasmaLean` (current), `lake env lean scripts/check_axioms.lean` (122 entry points, standard axioms only), single-module builds of the new sanity modules, then `lake build PlasmaLean` (zero warnings) |
| Open findings | kernel: 1 medium (F-1), 9 low; repository: 0 critical, 1 high (H-1), 5 medium; forms audit: AD-L4, AD-L5 (low); audit of 23 November: AV-M7, AV-M8 (medium) and the items listed below; see below and [`notes/audit/2026-10-30-repository-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-repository-audit.md) |
| Missing sanity checks | added: 58 kernel theorems in `PlasmaLean/Sanity/Audit{Equilibrium, ThermalSlab, Vacuum, Transport, Fusion}.lean` and 54 model theorems (plus 7 definitions) in `PlasmaLean/Sanity/AuditModel{GuidingCentre, Stability, Transport}.lean` (triad, risk-specific and regression checks), all in the default build; model record [`notes/audit/2026-10-30-model-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-model-audit.md) |

**Refresh audit (25 November 2026).** Audited commit `0bec221`; scope: all 531 Lean files changed
since `6ceca0e`, the generated-module pipeline of `scripts/dommaschk_kam/`, and 180 changed
documents. Six independent read-only sub-audits; record
[`notes/audit/2026-11-25-refresh-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-25-refresh-audit.md).
- **No false or vacuous exported theorem in the repository; no certificate checker that accepts
  false data.**
- **AW-H1 (high, resolved 25 November):** the headline QA2R C2 results (N-205, N-203, N-207, the
  full signed trace and flight-time bounds) were stated by script-generated Lean modules compiled
  into caches outside the repository. The 184 cited generated modules and their import closure
  (43,435 modules) are now the on-demand library `QA2RGenerated` (`generated/qa2r/`, stored as
  archives); a cold `lake build` passed and `scripts/check_axioms_qa2r.lean` found standard axioms
  only. After the opposite-inner closeout of 26 November the library has 186 cited roots and
  55,818 modules, replayed at `8ae555c` (clean tree): standard axioms only in 6,440,911
  declarations, 87,629 receipt theorems present.
- **AW-H2 (high, resolved 25 November):** `python3 scripts/qa2r/replay.py` replays these results
  from the repository (hashes, build, axiom audit) without `/tmp` inputs. Regenerating the sources
  from the numerical inputs is not covered; the generators stay untrusted.
- **AW-H3 (high, open):** `GuidingCentreBand` admits a point-mass population and an existential
  horizon (`quadratic_guidingCentreBand`, `DommaschkCommonLittlejohnTime.BandAt`); band-form
  instances of this kind do not count as C2 progress. Strengthening the clause is a contract
  decision.
- Medium findings AW-M1–AW-M14 (AW-M1, AW-M9, AW-M13 corrected in documents); low AW-L1–AW-L15
  (AW-L1 fixed). AV-M7 is sharpened by AW-H3; AV-M8, AV-M9, AV-M11, AV-L3, AV-L6 remain open.

**Complete refresh audit (23 November 2026).** Audited commit `6ceca0e`; scope: all 304 Lean
files changed since `921a8c3` and the note-to-code links of N-41–N-48, the README and the
Rosetta-stone page. Six independent read-only sub-audits; record
[`notes/audit/2026-11-23-refresh-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-23-refresh-audit.md).
- **No critical finding; no false or vacuous exported theorem.** 1 high, 12 medium, about 40
  low. Commands after the fixes: all 1,729 modules build (13,003 jobs, no warning);
  `check_axioms` passed for 52,147 declarations; `check_axioms_heavy` for 59,106.
- **AV-H1 (high, documentation, resolved):** the magnetic symplectic form was mislabelled: in the
  convention used it is `Ω − q π^*ω_B` on kinetic phase space. The proved identities were
  correct. Sign pinned by `magneticForm_lorentzForceField`; rejected fixture
  `uniform_plus_sign_fails`.
- **AV-M1, AV-M2 (resolved):** the clause-C1 corollaries are Stokes on the planar cross-section;
  "automatic for vacuum fields" was an overstatement; general form
  `CurrentFreeTransform.imax_zero_of_convex`.
- **AV-M3 (resolved):** gauge invariance now stated with hypotheses
  (`noetherMomentum_gauge_invariant`).
- **AV-M7 (open): clause C2 for a field has only a vacuous instance** (the toroidal field with
  `ι = 0`, which fails C1). No field is shown to satisfy C1 and C2 together.
- **AV-M8 (open): `BoozerChart` does not pin the poloidal angle**; the `ι` of C2 is defined modulo
  integers (`BoozerModelOf.relabel`, `toroidal_boozerModelOf_iota_one`) and is not tied to the `ι`
  of C1.
- **AV-M9 (documented; one part open):** C1 is satisfied by a single torus; `ι` is unique for a
  fixed parametrisation only under a differentiability hypothesis (`iotaOnTorus_iota_unique`).
- **AV-M4 (partly resolved):** the kinetic theorems need a global vector potential; uniqueness of
  orbits now holds for `C¹` fields without potentials (`lorentzOrbit_unique_of_contDiff`).
- **AV-M10 (resolved):** `dommaschk_Q16_chart` exposes the regularity behind the defect bounds.
- Open after this audit: AV-M7, AV-M8, parts of AV-M4, AV-M9, AV-M11; AV-L3, AV-L6; AF-1; AD-L4,
  AD-L5. The later Q-36 proofs resolved AF-1 for the certified examples.

**Partial audit of the differential-form modules (16 November 2026).** Audited commit `1e5d4f3`,
scope `Kernel/Forms`, `Sanity/Forms`, `Theory/Fields/FormBridges` only; record
[`notes/audit/2026-11-16-forms-audit.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-16-forms-audit.md).
The rest of the work since `921a8c3` had no refresh audit until 23 November 2026 (above).
- No exported theorem was false; conventions (orientation, signs, `extDeriv` normalization) are
  consistent.
- **AD-H1 (high, documentation, resolved):** the `FormBridges` module doc claimed symmetric-flux
  fixtures that did not exist.
- **AD-M1 (resolved, definitions changed):** `IsBeltramiOn` and `FormBeltramiOn` had no
  regularity clause, so a kinked field was Beltrami with λ = 0 at the kink. Both now require
  differentiability. The predicate is the curl equation only (∇ · B = 0 is not part of it).
- **AD-M2–M7 (resolved):** circular sanity checks; missing totalization regression for
  `VacuumForm`; `FormSymmetricFlux` vacuous with free γ; incomplete triads; contact coverage;
  missing `form_current_tangency`. Regressions are in `Sanity/AuditForms.lean` (29 theorems).
- **AD-L1–L3 (resolved), AD-L4–L5 (low, open):** a global instance in the kernel file,
  misplaced dot-notation names, doc nits; tautological sanity theorems kept; no Beltrami fixture
  with non-constant λ.

**Refresh-audit findings (31 October 2026).** The kernel is sound (only F-1 changed). No new
forbidden tactics, `check_axioms.lean` passes, every new module is covered.
- **AR-H1 (high, resolved 31 October):** the C1 current clause was vacuous with degenerate
  sections. It is restated as the poloidal-loop circulation, with a Stokes theorem for regular
  sections. Regressions are in `Sanity/AuditRefreshContract.lean`.
- **AR-M1 (resolved):** C1 uses ι_min ≤ |ι|. Still open: the negative-ι version of the C2 twist
  lemma (`twistOn_qa_of_iota_ge`).
- **AR-M2–M8 (prose fixed 31 October):**
  - `OmnigenousOn` is stronger than leading-order omnigeneity.
  - No trapped bounce is constructed for `exactQA`/`reactorQA`.
  - The QA-obstruction prose overclaimed.
  - The "1.5 μs" horizon is r₀/285000 s.
  - "Proved obstructions" are limits of the band method.
  - The hypotheses of not-weakly-QS are now stated.
  - Grad family 1 has ι ≡ 2 and follows the formulation of Cardona et al.
- **AR-L1–L9 (low):** stale "not in Lean" text, fixed. The `_root_` `VacuumField` lemmas stay in
  `CylAlgebra` (decision: no kernel change for theorems). Also open: a Dommaschk non-triviality
  fixture, parametrisation independence of ι, the C1/C2 common witness, and docstring nits,
  batched for the next Lean pass.

**Items from the kinetic/coil brief (N-36, 4 November 2026; low).**
- **AK-1 (low, open):** `Kernel/Fusion` `DTPlasma.alphaPower` counts the full 3.5 MeV birth energy as prompt local heating (deposition fraction 1). The docstring lists slowing-down delay as neglected, but G-2 claims do not name f_dep = 1 as an assumption. Fix: state it in their scope, or carry an explicit f_dep (Q-26 d).
- **AK-2 (low, open):** the fixed-density burn models (0-D windows, `solovev_one_plasma_*`) implicitly assume refuelling and ash removal (the docstring lists fuel burn-up and ash dilution as neglected). G-2's "or forever" needs a fuelling model; without one, sustained burn is impossible (Q-26 b).
- **AK-3 (low, resolved by N-37):** N-32 called β + dt ∧ α anti-self-dual without an orientation; it is self-dual for dt ∧ vol₃. Prose only, no Lean effect.

**Item from the complex-geometry note (N-42, 20 November 2026; low).**
- **AF-1 (low, resolved for the certified tori, 23 November 2026).** The original finding identified the gap between parametrised invariance, ray ordering and embeddedness. The strengthened clause `EmbeddedCurrentFreeTransform` now holds for each rational stellarator and Dommaschk example named in Q-36. The generic `FieldTorus` records parametrised invariance, and `NestedTori` records winding and ray order. Claims using these predicates alone still require a separate embedding argument. The double cover and the winding-one section with a stationary tangent at zero transform are regression examples.

**Strict-audit findings (30 October 2026).**

- **H-1 (high, resolved by the model audit):** the model definitions behind the headline claims (`LittlejohnOrbit`, `LorentzOrbit`, `BoozerGCOrbit(On)`/`BoozerField`, `mercierIndex`/`MercierStable`, ballooning `P`/`Q`/`LineData.Stable`, `coefF`/`coefG`/`ModeStable`, `NewcombReduction`, `BoschHaleFine`, `ConfinementLaw`/`SteadyScaling`, `FluxGeometry.Laws`, `IsSolovevGeometry`/`IsHelicalGeometry`, `IsFieldLine`) were re-derived against their sources (Littlejohn, Boozer, Landreman–Jorge, the ballooning equation, Newcomb/Freidberg, Bosch–Hale, IPB98) and match. Findings:
  - **MA-M1 (medium, partially resolved, 30 October; wording corrected by audit AR-M5/M6, 31 October):** orbits exist on the full horizon for a band of births further out (`alpha_band_orbit_exists_short`: 2.75 ≤ ψ₀ ≤ 5.5 for 8e-4 s; `alpha_band_orbit_exists_005`, `alpha_band_nonvacuous_005`: 4 ≤ ψ₀ ≤ 4.3 for 0.05 s), and for the original class 0 < ψ₀ ≤ psiStart on the explicit horizon r₀/285000 s (r₀ = √(2ψ₀/B₀); 1.49 μs at ψ₀ = psiStart, shrinking to 0 at the axis) (`alpha_orbit_exists_explicit`). Proved limits of the band method: no band reaches ψ₀ ≤ psiStart (`Dpsi_gt_psiStart`) and none survives for T ≥ 0.06 s (`band_empty_Tav`); the full 0.19 s horizon for the original class needs coordinates through the magnetic axis (a change of the model statement, user decision). Earlier: local existence proved (`boozerGCOrbitOn_exists_local`; `alpha_trapped_reactorQA_averaged_nonvacuous` gives a constructed orbit satisfying the hypotheses on some 0 < T ≤ 0.19 s, N-26). Existence on the full horizon needs an off-axis bound and cannot hold for the whole class born at ψ₀ ≤ psiStart. Original finding: `BoozerGCOrbitOn` requires the orbit to stay off the magnetic axis (ψ > 0), so the near-QA results (`alpha_trapped_reactorQA_averaged*`, `alpha_trapped_reactorQA`, `reference_kick_osc`, `exactQA_kick_osc`) exclude axis-crossing orbits, and no such orbit is shown to exist for `reactorQA`. Scope now stated on the slides.
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
1b. **Fixed-field QS jet obstruction** (Q-25 (a)–(b), N-32): lean-ready and cheap; then certified non-QS points for the rational and Dommaschk fields, so that the Q-16 claims stay honestly at the approximate tier.
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


**Research choices after the vacuum Q-16 milestone (23 November 2026).** For trapped particles,
compare the N-49 approximate momentum with direct radial drift on a regular band. Use the
Dommaschk field as the certified benchmark and a published quasi-isodynamic example as a comparator.
Screen a boundary deformation (N-50, Q-34) and use the N-55 obstruction to test alternative interfaces. Seek numerical or analytic evidence for a margin, or an obstruction to the proposed
construction, before building a field-specific proof chain. The fixed-domain exact-QS
linearization in N-50 is an exploratory direction.

**Status of the order of 30 October, and the order of 23 November 2026 (user-approved,
23 November 2026; it replaces the order of 30 October for work selection).** Items 0–4 of the approved order are done or answered: Q-23 in the Boozer model,
Q-16 in vacuum on two tori, Q-25 (a)–(c) for the rational field, Q-19 (the rational field fails
C2, untrusted), Q-18 (family 2 fails C1), Q-21 except ε_eff. Item 5 (Q-20/Q-14, Q-22, Q-3 on a
current-free equilibrium) has not started in Lean. Measured against the goal G-8 (one candidate
with C1–C5), the critical path is now:

1. **Validity of the candidate results.** Q-36 is complete for the rational stellarator and
   Dommaschk examples, including the Q-16 witnesses. The review at `4b0bf64` covers N-51, N-52 and selected fourth- and fifth-round N-48 proofs.
   Remaining audit work concerns the N-48 implementation details outside its stated coverage. Q-34 can use the embedded boundary surfaces; Q-31 is answered on A.
2. **C2 on the actual field.** Identify one regular physical bounce family and match its reduced field, invariant area and time to N-51. If the flux form is globally exact, its signed period is a consistency check. Search for two regular winding levels, measure their physical radial excursion and separation from a separatrix, and compare the N-49 momentum gap and direct drift estimate on the same births. Predeclare species, coverage, tolerance and horizon. Bound physical ε and any reduction error before certifying the band. N-56 encloses the initial ±1/8 radian on the whole strip. Rectangular propagation widens well before the sampled mirrors. N-57 reaches them using a centred trajectory on a local cell. Pulling each birth to a common section increased the certified phase width by 524,288 at the same radius. Use N-58 to test the largest height on the inner radial face and the smallest on the outer, uniformly over launch phase. N-60 obtains both local curves from endpoint signs and transverse variation on two sectors. Continue them with overlapping radius brackets adapted to each phase, prove equality on overlaps, and close the period seam. For a physical orbit, bound the discrepancy between its action and the action used in the face calculation. C5 also needs a loss bound on the complement (N-53). **Decided (user,
   23 November 2026): both forms of C2 are allowed.** A candidate may satisfy C2 in the
   Boozer-chart form (`OmnigeneityContract`) or in the band form: for stated species, energy
   and pitch ranges and a stated birth band of phase space, orbits stay within a stated radial
   range through a stated time (the N-51 form). A band-form claim must state its band, species,
   time and model, and is weaker than omnigeneity; the Lean predicate is `GuidingCentreBand` in the static Littlejohn model (G-11).
3. **Finite β (Q-20), in parallel with the bounce screen.** N-55 excludes the strict Q-31 pressure-step criterion on torus A. An external enclosure gives the same obstruction on C. Screen a different interface or bound the full quadratic energy, allowing a mixed-sign curvature term. Defer sheet-current and transform estimates for a pressure step until the proposed construction can pass its own sign test. The cylinder benchmark Q-30(a) supplies a period-uniform mode gap under explicit multiplier bounds. Its curved-domain analogue Q-30(b) remains open.
4. **Lean-ready items already in the registry:** Q-29 (a)–(b), Q-27 (a), Q-26, Q-28 (a). They are
   cheap and feed 2 and C5.
5. **Lower:** improving the seed (Q-32, Q-34/N-50) while the candidate's own C2 numbers are
   good; the fixed-domain rigidity test (Q-24); further general theory for N-48 (bundles,
   cohomology classes) and for N-51 without a physical band. For full-orbit versions, `lorentzOrbit_existsUnique_of_confined` already gives global existence from compact a priori position bounds. `exists_forward_of_apriori` suffices for a finite horizon under its compactness hypotheses. A general maximal-orbit escape lemma is a separate open result.

### RG.6 Definition of done and evidence gates

(Adopted from the LeanTheory template, 3 November 2026; §8 below remains the per-cycle checklist.)

- **A research note** is done when its claims and evidence are classified, its dependencies and
  barriers are current, its outputs are recorded, and the next readiness-changing action is
  explicit. Implemented notes keep their content; changes go into method or patch notes (skill
  `plasmalean-modify-notes`).
- **A verified result** is done when:
  - its declarations compile with docstrings and sanity theorems, with zero warnings;
  - the axiom audit passes (`scripts/check_axioms.lean`, or `check_axioms_heavy.lean` for on-demand
    modules);
  - semantic audit findings are resolved;
  - its entry points are registered;
  - its note gives an honest scope statement.

  Kernel laws have the sanity triad plus risk-specific checks.
- **A goal** is done when all required contract clauses hold for one compatible witness and model,
  and every claimed dependency is backed by the recorded level of evidence. A formal theorem alone
  does not validate the physical model.
- **Evidence gates.** The contract clauses that must hold for the same witness are C1–C5 (part "The
  stellarator contract"); the roadmap gates are P0–P9 (`notes/formalization/08-roadmap.md`), and
  the design verification levels L0–L5 are in the skill `plasmalean-design-stellarator`. The
  assumption ledger is §1 (corrections) and the kernel docstrings (§2.1); guidance on stating goals
  is `notes/goals/method.md`.
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

- **Done (default build):** `Theory/Fields/WeakQuasisymmetry.lean`: `WeakQS` (Constantin–Drivas–Ginsberg Definition 1, pointwise: ξ ≠ 0, div ξ = 0, B × ξ = −∇ψ, ξ·∇‖B‖ = 0), the defect `qsDefect` (sup of ‖ξ·∇‖B‖‖; zero iff ξ·∇‖B‖ vanishes on the region, `qsDefect_eq_zero_iff`; exact weak QS iff zero defect for a generator, `weakQS_iff_defect_zero`), exact axisymmetry as a special case (`qsError_rotGen_eq_zero_of_axisymmetric`), sanity triad (`weakQS_uniform`, `weakQS_screw`, `not_weakQS_mirror`), and the axis lemma (`WeakQS.normB_const_of_gradient_eq_zero`: ‖B‖ constant on a field line where ∇ψ = 0). `Design/LandremanNotQS.lean`: `family1_not_weakQS`, `family2_not_weakQS` (and `_flux` variants): for ε ≠ 0 neither family is weakly quasisymmetric on a region containing the whole axis with ∇ψ = 0 there. Not excluded: generators vanishing on the axis.

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

### Colleague's holomorphic strong-QS brief assessed, 30 October 2026

- Source: `gpt/stellarator_holomorphic_research_brief.pdf` (14 pp.). Assessment in
  `notes/theory/holomorphic-qs-brief.md` (N-32).
- Verdict: the holomorphic (HYM / abelian Bogomolny) lift re-encodes the unique vacuum field of a
  fixed solid torus and constructs nothing new. Its proved content is two ansatz obstructions
  (flat rank-one KYM forces constant B; a holomorphic horizontal QS generator is Killing), which
  close two N-21 routes. The fixed-domain framing is compatible with the design search, since a
  vacuum field is determined by its outer surface.
- Adopted: the linear first-order system for the QS moment and its pointwise jet obstruction, as
  new question Q-25 (Lean equivalence and obstruction lemma; certified instance; certified
  non-QS points for the rational and Dommaschk fields; quantitative lower bounds as research).
  The vacuum Boozer identity Ψ' = Mι − N (QA moment regular iff ι ≠ 0) supports the Q-16 ratio
  criterion. The global disk section is an optional item.
- Checked: the brief's explicit numbers for B = ∇(xyz) at (1, 2, 3), reproduced exactly in sympy
  (det 564480, η = (−2201/720, 869/180, 463/240), dη_xy = 1739/21600), and the div-u identity.
  No Lean change.

### Dommaschk QA fit: medium workstation run reviewed, 30 October 2026

- Run `workstation/dommaschk-qa-20261030T112135Z`: nmax 2 (24 coefficients), 16 starts, ι_min 0.2,
  surfaces r = 0.02, 0.04, 0.06; 4.2 min wall on 16 jobs, 0.8 GB peak. Untrusted numerics; results
  merged under `scripts/dommaschk_qa/results/20261030T112135Z/`.
- Outcome: no tier. Best start defect/|ι| 0.12–0.13 with |ι| ≈ 0.24, nested only to r = 0.032,
  ε_eff 4.5 % at r = 0.02; low-defect starts lost the outer surface. Worse than the smoke test
  (defect/ι 0.014–0.029 at ι ≈ 0.17, surfaces ≤ 0.045). N-31 §7.
- Next: two diagnostic medium runs at the smoke surfaces (ι_min 0.15 and 0.2) to separate the
  effect of ι_min from the surface radii; the larger run (ι_min 0.3, wider surfaces) waits for a
  medium run reaching the moderate tier.
- On-demand olean archive (`ondemand.tar.gz`, built at 6377afa): the source checks passed, but lake
  rejects every module downstream of `PlasmaLean.Certificates.EvalCert` (45 default-build, 57
  on-demand-only modules), because their traces hash the native `PlasmaLeanMeta` library
  (`precompileModules`; `.so` on Linux, `.dylib` here). Modules outside that cone were accepted.
  The overwritten default-build modules are rebuilt here from source. The archive route does not carry the
  Mu/Ew on-demand families across platforms as it stands.

### Dommaschk QA fit: first diagnostic run reviewed, 30 October 2026

- Run `workstation/dommaschk-qa-20261030T115455Z`: nmax 2, 16 starts, ι_min 0.15, surfaces
  r = 0.015, 0.03, 0.045; 5.1 min wall on 16 jobs. 15 of 16 starts regular. Best start: |ι| ≈ 0.24,
  defect/ι 0.021 and 0.038 and ε_eff 0.56 % and 0.96 % on the two nested surfaces (moderate tier
  there), κ 0.34–0.59. Nesting stops at the ι = 2/9 island chain (r_eff ≈ 0.019), so the summary
  tier is "not small". The surface radii, not ι_min, caused the medium run's failure. N-31 §8.

### Dommaschk QA fit: second diagnostic run reviewed, 30 October 2026

- Run `workstation/dommaschk-qa-20261030T120025Z`: nmax 2, 16 starts, ι_min 0.2, surfaces
  r = 0.015, 0.03, 0.045; 2.7 min wall. 13 of 16 starts regular. Best start: |ι| 0.258–0.238,
  defect/ι 0.020 (inner) to 0.051 (outer), ε_eff 0.66 %; the middle surface sits on the ι = 1/4
  island chain, with regular tori on both sides out to r = 0.048. ι_min 0.2 is not the obstacle;
  low-order resonances and the loss of field lines near r ≈ 0.05 set the volume. N-31 §9.
- Next: larger bases (nmax 3 and 4, 48 starts) at the same surfaces on the workstation; then a
  resonance-avoiding ι window in the objective (code change).

### Dommaschk QA fit: nmax 3 run reaches the moderate tier, 30 October 2026

- Run `workstation/dommaschk-qa-20261030T120952Z`: 42 coefficients, 48 starts on 24 jobs,
  ι_min 0.2, surfaces r = 0.015, 0.03, 0.045; 11.4 min wall. Best start (rounded rational
  coefficients, high-resolution diagnostics): |ι| 0.246, 0.241, 0.235; defect/ι 0.009, 0.015,
  0.023 (**moderate tier**, the inner surface at the strong level); ε_eff 0.08 % and 0.13 %; κ 0.11–0.37;
  low shear keeps ι inside (2/9, 1/4); regular out to r_eff ≈ 0.037, strictly nested to
  r_eff ≈ 0.027; non-planar axis (z_max 0.051). Untrusted numerics. N-31 §10.
- Also new on `main`: an optional `--iota-window lo,hi` objective term in `optimize.py` (off by
  default, residuals unchanged when off), passed through `DQA_EXTRA`.

### On-demand oleans installed via `oleans.py retrace`, 30 October 2026

- The workstation archive (MuQuarter and EwFamily, built at 6377afa) is installed: the default
  build was rebuilt here (192 modules, bounded, 0 failures, all targets up to date), and 57
  on-demand modules downstream of `PlasmaLean.Certificates.EvalCert` were retraced (new
  `oleans.py retrace`, on-demand modules only, outputs byte-identical to the archive). Lake
  accepts `RationalStellaratorGCMuQuarter` and `RationalStellaratorGCEwFamily`. The 12 entry points of
  Mu2–Mu5, MuQuarter and EwFamily (`scripts/check_axioms_heavy.lean` minus MuWide/CoilKamCert, which
  were not in the archive) load with `propext`, `Classical.choice`, `Quot.sound` only. Workstation
  trust as for the on-demand policy; not re-checked by the laptop kernel.

### Dommaschk QA fit: nmax 4 run reviewed, 30 October 2026

- Run `workstation/dommaschk-qa-20261030T122122Z`: 62 coefficients, 48 starts, 24 jobs; 40.6 min wall,
  1.5 GB peak. The best start at optimiser resolution (worst defect/ι 0.041) fails the
  high-resolution diagnostics (middle surface in the 2/9 island chain, outer surface lost, nested
  only to r = 0.015). The larger basis overfits the coarse objective; the nmax 3 candidate (N-31
  §10) stays the best. N-31 §11.

### Dommaschk QA fit: windowed run at larger radii reviewed, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T034330Z`: nmax 3, 48 starts, `--iota-window 0.226,0.248`,
  surfaces r = 0.02, 0.04, 0.06; 19.5 min wall. Every regular start has defect/ι ≥ 0.08; ι reaches
  2/9 at r ≈ 0.048 despite the window; strictly nested only to r_eff ≈ 0.021. The steep
  volume/QA trade-off at NFP 2 and 42 coefficients leaves the N-31 §10 candidate the best. N-31 §12.

### Dommaschk QA fit: high-ι windowed run reviewed, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T040304Z`: nmax 3, ι_min 0.38, window 0.405–0.44;
  12.6 min wall. Only 2 of 48 starts were regular; the selected one has |ι| 0.36–0.39 (below the
  window), defect/ι 0.11, ε_eff ≈ 10 %. At NFP 2 the N-31 §10 candidate remains the best. Next on
  the workstation: exploratory NFP 3 runs (a laptop smoke test gave |ι| ≈ 0.33 with defect/ι
  0.04–0.05 after 4 evaluations). N-31 §13.

### Dommaschk QA fit: warm-start option, 31 October 2026

- `optimize.py --init FILE` (candidate.json matched by basis name, or start_NNN.json): restart from
  an earlier field with field-scaled perturbations, straight into stage B; default behaviour
  bit-identical. Laptop check (2 starts, untrusted): a perturbed restart of the N-31 §10 candidate
  gives a moderate-tier field with |ι| ≈ 0.32, defect/ι 0.013–0.021, ε_eff 0.3–1.0 %, but a
  smaller region (r_eff ≈ 0.016). Workstation refinement commands are queued after the NFP 3 runs.
  N-31 §14.

### Dommaschk QA fit: three field periods give the first certification candidate, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T044845Z`: NFP 3, nmax 2 (24 coefficients), 48 starts,
  ι_min 0.25; 9.6 min wall; 43 of 48 starts regular. Best start (rounded rationals, high
  resolution): |ι| 0.294, 0.283, 0.268; defect/ι 0.007, 0.013, 0.020 (moderate tier); ε_eff 0.13 %,
  0.25 %, 0.47 %; κ 0.14–0.40; regular to r_eff ≈ 0.025 (first island at ι ≈ 3/14); all Q-16 checks
  pass and `candidate_for_certification` is true. It becomes the lead candidate for the
  certification path (N-31 §15). Untrusted numerics.

### Dommaschk QA fit: NFP 3, nmax 3 run reviewed, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T045824Z`: 42 coefficients, 48 starts; 21.4 min wall. The
  selected start crosses the 1/3 and 3/10 resonances at high resolution (defect/ι 0.054, nested
  only to r = 0.018). As with NFP 2, the larger basis does not improve on the smaller one; the
  NFP 3, nmax 2 candidate (N-31 §15) remains the lead. N-31 §16.

### Dommaschk QA fit: certification step 1, exact NFP-3 field in Lean, 31 October 2026

- New default-build modules `Theory/Fields/CylAlgebra` (reusable exact algebra of
  `x^a y^b z^j r₂^s (log r₂)^q` functions: formal derivatives proved to be Fréchet derivatives,
  smoothness, a sound normal form, `gradField_vacuum`, `VacuumField` closure under sums and scalar
  multiples), `Design/DommaschkQA3Data` (generated by `scripts/dommaschk_qa/emit_lean.py` from the
  N-31 §15 candidate; 24 `kernel_fact` harmonicity checks, 34 s, 3.0 GB) and `Design/DommaschkQA3`:
  `basis_harmonic`, `field_vacuum` (every coefficient vector), `candidate_vacuum`,
  `candidate_netToroidalCurrent_eq_zero`, `candidate_currentFree` (C1 current clause),
  `field_stellSym`; non-vacuity sanity `nf_lap_x2_ne`. Standard axioms only; `lake build PlasmaLean`
  clean. Open: 2π/3 rotation symmetry, KAM tori and ι (C1 transform clause), Boozer angles and the
  certified QA defect. N-31 §17.

### Dommaschk QA fit: first poller batch, NFP-3 warm start reviewed, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T075059Z` (poller batch `2026-10-31-warmstart`): 48 warm
  starts around the N-31 §15 candidate; 46 regular; six with worst defect/ι 0.013–0.019 at optimiser
  resolution. The selected one fails at high resolution (inner surface on ι = 3/8). `optimize.py` now
  re-ranks the top starts at diagnostic resolution and keeps all coefficients in `starts.json`
  (`--init starts.json:K`). N-31 §18.

### Dommaschk QA fit: NFP-2 warm start reaches the strong level on most surfaces, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T075915Z`: 48 warm starts around the N-31 §10 candidate
  (σ 0.002); best five worst defect/ι 0.0025–0.0042 at optimiser resolution. Selected start at high
  resolution: inner surface on ι = 1/4 (island); outer surfaces defect/ι 0.0012 and 0.0026, ε_eff
  0.002 % and 0.03 %, regular to r_eff ≈ 0.042. The poller's batch `2026-10-31-warmstart` finished
  (exit 0, 23 min); the re-rank batch `2026-10-31-rerank` is queued. N-31 §19.

### Q-25 (a)–(b) verified: QS linear system and jet obstruction, 31 October 2026

- `Theory/Fields/QSLinearSystem` (default build): pointwise algebra of u = (∇Ψ × B + C B)/Q
  (`cross_fqsVec`, `inner_fqsVec`, `eq_fqsVec_of_cross_of_inner`); divergence formula with actual
  Fréchet derivatives for vacuum B (`fieldDiv_fqsGen`, `fieldDiv_fqsGen_eq_zero_iff`); equivalence
  strong QS ⇔ (FQS) (`StrongQSAt.fqsAt`, `FQSAt.strongQSAt`); jet obstruction for general X, Y, Z
  (`JetHyp.jet_obstruction_curl`, `jet_obstruction_eta`: C ≠ 0 ⇒ dη(p) = 0) and the vacuum corollary
  `strongQS_jet_obstruction`. `Design/QSJetExample`: B = ∇(xyz) (`field_vacuum`, `field_eq_gradient`),
  exact jet data at (1, 2, 3) (`jet_values`, `jetSolution`), dη_xy = 1739/21600 (`curl_etaJac_two`),
  `strongQS_obstruction` / `not_strongQS_of_ne_zero`: no strong QS with C ≠ 0 on any neighbourhood
  of (1, 2, 3). Standard axioms; 0.76 GB. Local example only. Next: (c) certified non-QS points for
  the rational and Dommaschk fields; (d) a quantitative version.

### Audit fix AR-H1/AR-M1: intrinsic C1 current clause, 31 October 2026

- `Theory/Contract/StellaratorContract`: `lineIntegral`, `poloidalLoop`, `poloidalCirculation`,
  `loopCurrent`; `SurfaceData` reduced to (R, z, ι, φ₀); `CurrentFreeTransform` bounds
  |μ₀⁻¹∮B·dl| around each torus's own poloidal loop (μ₀ > 0, C¹ loop, B continuous on it) and asks
  ι_min ≤ |ι|. `currentFreeTransform_of_potential` (toroidal part plus single-valued potential) replaces
  `currentFreeTransform_of_vacuum`; the tokamak exclusion is restated. New `Theory/Contract/SectionStokes`:
  `netToroidalCurrent_eq_lineIntegral_div` (Stokes for C² seam-matched sections with a degenerate inner
  edge, via Mathlib's divergence theorem on rectangles). Family 2 fails C1 again
  (`family2_not_currentFreeTransform`, `family2_loopCurrent_pos`). Witnesses:
  `rationalStellarator_currentFreeTransform` (now needs μ₀ > 0), `DommaschkQA3.candidate_currentFreeTransform`.
  Regressions `Sanity/AuditRefreshContract` (pinch facts for the section notion, `rotY` circulation
  2πa², `rotY_not_currentFreeTransform`). `lake build PlasmaLean` clean; axiom audit passed (48,589
  declarations).

### Dommaschk QA fit: strong tier reached, 31 October 2026

- The tightened re-rank (Birkhoff ≤ 1e-5, Boozer modes up to 8), applied on the laptop to the committed
  starts of `workstation/dommaschk-qa-20261031T083850Z`, selects start 11: NFP 2, 42 coefficients,
  |ι| 0.240–0.233 inside (2/9, 1/4), defect/ι 0.0013 / 0.0021 / 0.0043 (**strong tier**), ε_eff
  0.002–0.019 %, κ ≤ 0.08, strictly nested to r_eff ≈ 0.032; all Q-16 checks pass,
  `candidate_for_certification` true (untrusted numerics; results
  `scripts/dommaschk_qa/results/20261031-laptop-rerank-083850Z/`).
- Purely rational NFP 3 field (`--exclude-log`, run `20261031T084057Z`): moderate tier (defect/ι ≤ 0.019
  at |ι| ≈ 0.33), regular to r_eff ≈ 0.047. N-31 §21.

### Dommaschk QA fit: certification target chosen, 31 October 2026

- Run `workstation/dommaschk-qa-20261031T085357Z` (NFP 2, `--exclude-log`, purely rational): start 30, defect/ι
  0.0012 / 0.0016 / 0.0035 at |ι| 0.239–0.231 (**strong tier**), ε_eff ≤ 0.018 %, strictly nested to
  r_eff ≈ 0.052, monotone ι in (2/9, 1/4); `candidate_for_certification` true (untrusted). Chosen as the
  certification target (N-31 §22): purely rational, so the polynomial KAM pipeline applies.

### Certification step 1 for the target: exact NFP-2 rational field in Lean, 31 October 2026

- `Design/DommaschkQA2RData` (+ `DommaschkQA2RDataCheck0`–`2`, generated, sliced harmonicity checks,
  peaks ≤ 3.1 GB) and `Design/DommaschkQA2R`: `field_vacuum` (all coefficients), `candidate_vacuum`,
  `candidate_loopCurrent_eq_zero`, `candidate_currentFreeTransform` (C1 reduces to certified tori),
  `field_stellSym`, `candidate_log_free`. `Theory/Fields/CylAlgebra`: `sliceCheck`,
  `eval_eq_zero_of_sliceCheck`, `gradField_vacuum_of_eval`, `gradField_vacuum_of_sliceCheck`.
  `lake build PlasmaLean` clean; axiom audit passed (48,770 declarations). N-31 §23.

### Refined certification target, 31 October 2026

- Poller batch `2026-10-31-refine-target` (exit 0, 29 min): run `20261031T092522Z` start 46 is strong
  tier on surfaces out to r = 0.06 (defect/ι ≤ 0.0047, ε_eff ≤ 0.036 %), strictly nested to
  r_eff ≈ 0.053, purely rational; it replaces the §22 field as the certification target, and
  `DommaschkQA2RData`/`DommaschkQA2R` were regenerated from it (same theorems, standard axioms). Run
  `20261031T094002Z`: strong tier, smaller region. N-31 §24.

### Certification step 2, numerics: KAM flow-torus oracle for the target, 31 October 2026

- `scripts/dommaschk_kam/` and the task `dommaschk-kam`, ported from `scripts/kam_oracle/` (exact
  polynomial flow form with D = s⁴B^φ). Laptop, torus A (ι = −(19+√5)/89): residual 9.5 × 10⁻²⁰ at
  64 × 52 modes, 40 digits; ELP-S twist T/|ω| = +0.147, one sign (low shear is not a barrier); FHL
  tolerance about 10⁹–10¹¹ expected at 80 × 64. Main barrier: certificate size (degree-17 residual,
  about 6 × 10⁶ coefficients), so a ball-arithmetic certificate with tails, not exact Kronecker.
  Workstation main run queued (batch `2026-10-31-kam-A-C`). N-31 §25. Untrusted numerics.

### Certification step 2: Lean certificate design (N-33), 31 October 2026

- `notes/theory/dommaschk-kam-certificate.md` (N-33): conditional go. The exact torus for the
  rational field comes from `FlowField.KamH.kam_flow_torus` (`Design/KamFlowIteration`); the
  guiding-centre torus (KronBall residual chain plus low-resolution admissibility chain) is the
  template. Needed: a `FlowFieldG` generalisation (moving frame centre, density exponent 7, centre
  R₀ ≈ 0.91), an exact-low-small-divisor estimate (κ ≈ 80× smaller), about 104 × 84 modes at 128
  bits (e₀ ≲ 2 × 10⁻²³), a KronBall chain of 35–40 product nodes; estimated 45–85 CPU-min, ≤ 5 GB per
  module, about 90 modules (first build on the workstation). Prototype
  `Design/DommaschkKamProto` (on demand): one product image of 41 Mbit at 104 × 88 costs 8.8 s and
  3.7 GB; the kernel refuses `Nat.pow` above 2²⁵ bits (emitters use shifts). Estimator
  `scripts/dommaschk_kam/kam_constants.py` reproduces the certified rational-torus constant
  (10748.5 against ≤ 10800).
- **Blocker found (contract):** `PoloidalAngle` uses one fixed reference point (R₀, z₀) for all
  cross-sections; the target's axis wanders more than its nested minor radius, so no surface of this
  field can satisfy `IotaOnTorus`, and `candidate_currentFreeTransform`'s torus hypothesis cannot be
  met as defined. Audit item AR-L4 is raised to a blocker; fix in progress: a continuous
  2π-periodic reference curve (R₀(φ), z₀(φ)) (the constant curve recovers the old definition).

### Audit fix AR-L4: poloidal angle about a moving reference curve, 31 October 2026

- `Theory/Contract/StellaratorContract`: `PoloidalAngle R z R₀ z₀ Θ` with a continuous 2π-periodic
  reference curve `R₀ z₀ : ℝ → ℝ`; `IotaOnTorus` quantifies over such curves; `poloidalAngle_const_iff`,
  `PoloidalAngle.ofConst`, `exists_R_gt`/`exists_R_lt`; the tokamak exclusion
  `iota_eq_zero_of_purelyToroidal` re-proved. Fixtures: `Sanity.AuditRefresh.wander_poloidalAngle`,
  `wander_not_poloidalAngle_const`, `RationalStellaratorContract.twistTorus_not_iotaOnTorus`. Unblocks C1
  for fields with a wandering non-planar axis (N-33 O3). `lake build PlasmaLean` clean; axiom audit
  passed (48,803 declarations).

### Certification step 2: exact low small divisors, 31 October 2026

- `Theory/KAM/CohomologicalLow` (`DiophantineSplit`, `cohSol_estimate_split`, `Bd.coh_split`, reduces to
  `cohSol_estimate_one`) and `Design/DommaschkKamDio` (`dkOmegaA_split` with d = 0.1193 for k = 1,
  γ₂ = 0.3645 for |k| ≥ 2; the oracle's 0.3646 is refuted by `dkOmegaA_not_split_high`). Rüssmann factor
  3.05× better; N-33 plan items 2 and 4 done. Default build; axiom audit passed (48,865
  declarations). Next: the `KamFlow*G` generalisation (N-33 item 3).

### Certification step 2: generalised KAM interface, milestone 1, 31 October 2026

- `Design/KamFlowFieldG` and `Design/KamFlowFrameG` (default build): `FlowFieldG` with a general centre
  R₀, density exponent p, flux-primitive exponents, and a moving frame centre given by trigonometric
  data (N-33 obstacles O1, O2); every frame identity of `KamFlowFrame` in this generality
  (`frame_decomp_R/Z`, `torsion_coord`, `S_coord`, `eta2_flux`, `newton_error_R/Z`, …). Reduction to the
  rational field: `FlowField.toG`, `toG_frameHyp_iff`, `toG_invariant_iff`, `field14G_invariant_iff`;
  rejected fixture `toroidalShift_Pof_ne` (a moving centre changes the torsion). Remaining:
  `KamFlowStepG` (constants with p, `DiophantineSplit`) and `KamFlowIterationG`
  (`notes/theory/kamflow-g-status.md`). Axiom audit passed.

### Certification step 2: generalised KAM Newton step, milestone 2, 31 October 2026

- `Design/KamFlowStepG` (default build): `SCG` (bounds for the moving centre, ‖R‖, exponent p, split
  Diophantine data), `FlowFieldG.StepH` with `DiophantineSplit` and `Bd.coh_split`, and
  `FlowFieldG.StepH.kam_step` (one Newton step: ‖ΔK‖ ≤ cK e/δ², ‖𝓛ΔK‖ ≤ cL e/δ², new error ≤ κ e²/δ⁴).
  Reduction: `SC.toSCG` makes every constant equal for the rational field; `FlowField.StepH.toG`,
  `field14_stepH_toG` (needs e·δ₀ ≤ 1, true for torus A). Remaining: `KamFlowIterationG` (milestone 3).
  Axiom audit passed (49,485 declarations).

### Certification step 2: generalised KAM iteration, milestone 3 (interface complete), 31 October 2026

- `Design/KamFlowIterationG`: `AdmBoundsG`, `GlobalHG` (split Diophantine, no `hδ2`), `KamHG`, and
  `FlowFieldG.KamHG.kam_flow_torus` (exact real analytic invariant torus, same shape as the original).
  Adapters `FlowField.GlobalH.toG`, `KamH.toG`, `toG_iterK`. `Design/KamTorusAExactG`: the certified
  rational torus A re-derived through the generalised theorem (`torusA_exactG`, `torusA_exact_viaG`, the
  statement of `torusA_exact`, same iterates). The generalised KAM interface (N-33 item 3) is complete;
  the Dommaschk instantiation (items 5–10: field, constants, admissibility chain, residual chain,
  contract) is next, and needs the high-resolution oracle runs. Axiom audit passed (49,638
  declarations).

### Certification step 2: Dommaschk flow-field instance (N-33 item 5), 31 October 2026

- The target needs a dφ-component in the KAM flux primitive (⟨B_z⟩ = c₀ ≠ 0; proved:
  `DommaschkKam.no_flowFieldG`); `FlowFieldG` extended by `Pcp` (rational field: 0; all G modules
  unchanged otherwise). `DommaschkKam.dkFieldC` / `dkField : FlowFieldG` (R₀ = 29/32, p = 7) with
  kernel-checked identities (`divFree`, `flux_a`, `flux_b'`, `flux_c'`, `torsion_poly`) and the
  identification with `DommaschkQA2R.field candidate` (`Dp_ident`, `nRp_ident`, `nZp_ident`,
  `flow_ident`). Modules ≤ 3.0 GB. Axiom audit passed (49,997 declarations). Items 6–10 need the
  high-resolution oracle (workstation).

### Q-25 (c): certified jet obstruction for the rational stellarator field, 31 October 2026

- `Design/RationalStellaratorJetObstruction`: for the actual `RationalStellarator.field (1/4)` at
  p₀ = (1, 0, 1/4) (a quarter unit above the axis), dη(p₀) has y-component ≈ 38.69 (exact rational,
  `kernel_fact`), so `strongQS_obstruction`: any strong QS on a neighbourhood of p₀ has C = 0 and ∇Ψ ≡ 0
  nearby; `not_strongQS_of_ne_zero`. Jets of B to third order via polynomials in (x, y, z, 1/r₂) with a
  formal derivative proved correct off the axis. Local statement, complementing the first-order
  obstruction `RationalStellaratorQAObstruction`. 4.3 GB, 18 s. Axiom audit passed (50,162 declarations).

### Certification step 2: KAM oracle at 80 × 64 (workstation), 1 November 2026

- Run `workstation/dommaschk-kam-20261031T163518Z`: torus A flow error 1.6 × 10⁻²³, torus C 1.5 × 10⁻²⁴ (FHL tolerance
  with exact low divisors 1.7 × 10¹¹ and 9.0 × 10¹¹); twist +0.147 / +0.151. Torus C meets the N-33
  requirement (e₀ ≲ 2 × 10⁻²³) by about 13× at 80 × 64 and becomes the preferred certification torus;
  a 96 × 80 run of C is queued for margin. N-31 §26. Untrusted numerics.

### Certification step 2: torus C at 96 × 80 (workstation), 1 November 2026

- Run `workstation/dommaschk-kam-20261031T184225Z`: flow error 1.6 × 10⁻³⁰ (FHL tolerance 1.9 × 10¹⁷ with exact low
  divisors), margin ≈ 10⁷ over the N-33 requirement; torus C is the certification torus. Numerics
  for step 2 are sufficient; the remaining work is the Lean certificate chain (N-33 items 6–10).
  N-31 §27. Untrusted numerics.

### Certification step 2: items 6–7 (centre, torus data, small divisors, constants), 1 November 2026

- `Design/DommaschkKamCData` (96 × 80 torus C, generated, 6 s / 1.4 GB), `DommaschkKamCTorus` (quarter-turn
  rotation `rotψ` between the oracle and strip-algebra angles; `u₀C`, `z₀C`, `dkFieldTC` with a 3-harmonic
  centre, W₀ one-signed), `DommaschkKamDioC` (`dkOmegaC_split`, d = 0.1208, γ₂ = 0.2671). Constants
  estimate: κ ≈ 4.0 × 10¹², required e₀ ≈ 1.3 × 10⁻²³; the 96 × 80 torus has ‖E‖_{0.045} = 5.9 × 10⁻²⁹
  (margin 2.3 × 10⁵); **80 × 64 is insufficient** (correction to N-31 §26–27, which compared the sup
  error). Next: item 8 (low-resolution admissibility chain, near-sharp inverses). Axiom audit passed
  (50,270 declarations).

### Certification step 2: item 8, admissibility chain for torus C, 1 November 2026

- On-demand top module `Design/DommaschkKamCAdm` (`lake build PlasmaLean.Design.DommaschkKamCAdm`, ≈ 26
  CPU-min on the laptop, peak 5.1 GB): `DommaschkKamC.dk_adm` gives all of `dkFieldTC.AdmBoundsG` (frame
  units and inverses of D, R, W₀, torus and field bounds, torsion, twist) for every analytic torus
  μ-close (μ ≤ 10⁻¹²) to the data torus, on every strip 0 < ρ ≤ 0.045; `dk_hadm` is the `hadm` field of
  `KamHG`. KronBall chain on the 24 × 28 surrogate with near-sharp approximate inverses (qD, qW, qR);
  certified bounds within 0.02 % of sharp except the twist (14.16 vs 14.26). With them κ ≈ 4.08 × 10¹²,
  required e₀ ≈ 1.31 × 10⁻²³, margin ≈ 2.2 × 10⁵ for the 96 × 80 torus. 27 modules (generated by
  `scripts/dommaschk_kam/emit_adm.py` with the ball engine `adm_ball.py`). Axioms standard (scratch
  check). Remaining: item 9 (`cDK : SCG`, C₂, closed numeric facts) and the high-resolution residual
  chain (initial error e₀), then item 10 (contract link).

### Certification step 2: item 9, constants and the conditional exact torus, 1 November 2026

- `Design/DommaschkKamCJet` (default build; second-order majorant jets with a kernel-checked rational
  mirror) and on-demand `Design/DommaschkKamCConsts` (`lake build PlasmaLean.Design.DommaschkKamCConsts`):
  `cDK : SCG` (`cDK_ok`), certified κ ≤ 4.0798 × 10¹², C₂ = 4.0797 × 10¹², `dk_globalHG`, all closed `KamHG`
  fields, `dk_kamHG` and **`dk_exact_of_res`**: given the two initial residual bounds
  ‖resR‖, ‖resZ‖ ≤ e0qDK (= 10⁻²⁴; admissible up to 1.15 × 10⁻²³) at ρ = 0.045, there is an exact real
  analytic invariant torus of `dkFieldTC` within μ = 10⁻¹² of torus C. Remaining: the residual chain
  (in progress) and item 10 (contract link). Axioms standard.

### Certification step 2: item 10, contract link (C1 conditional on the residual bounds), 1 November 2026

- On-demand `Design/DommaschkKamCRadial` and `Design/DommaschkKamCContract`
  (`lake build PlasmaLean.Design.DommaschkKamCContract`): **`dommaschk_C1`**: given the initial residual
  bounds `e0R`, `e0Z` (‖resR‖, ‖resZ‖ ≤ 10⁻²⁴ at ρ = 0.045), for every μ₀ > 0 there is a family S with
  `CurrentFreeTransform μ₀ (DommaschkQA2R.field candidate) S 0 (6/25)`: contract clause C1 with zero net
  toroidal current and |ι| ≥ 0.24 for the exact Dommaschk field. Also `dommaschk_iotaOnTorus`,
  `dommaschk_C1_of_exact`. Construction: the exact flow-form torus mapped to cylindrical (R, z) with
  ψ = 2φ − π/2; `FieldTorus` from the invariance equations and `Dp/nRp/nZp_ident` (B_φ ≠ 0 from the
  admissibility frame); poloidal angle about the θ-average of the exact torus (a continuous periodic
  reference curve), radial positivity certified by one Kronecker digit sum (`radial_ge_of_close`).
  Rejected fixture `not_C1_iotaMin` (ι_min = 1/4 fails). Only the residual chain remains.

### Certification step 2 complete: C1 for the exact Dommaschk field, 1 November 2026

- Residual chain (N-33 item 7): on-demand `Design/DommaschkKamCRes` (29 modules, generated by
  `scripts/dommaschk_kam/emit_res.py`; hand-written `DommaschkKamCResKron` with salted packed rows and
  divide-and-conquer Kronecker images; ≈ 12 min on the laptop, peak 5.4 GB): `dk_e0R`, `dk_e0Z`
  certify the initial invariance error ≤ 1.23 × 10⁻²⁷ at ρ = 9/200 for the 96 × 80 torus C.
  Workstation task `dommaschk-res` exists but is not needed.
- Final assembly: on-demand `Design/DommaschkKamCFinal`
  (`lake build PlasmaLean.Design.DommaschkKamCFinal`): **`dommaschk_C1_unconditional`**: for every
  μ₀ > 0, `∃ S, CurrentFreeTransform μ₀ (DommaschkQA2R.field candidate) S 0 (6/25)`, and
  `dommaschk_iotaOnTorus_unconditional` (certified invariant torus with ι_C = −(85+√5)/361). Standard
  axioms. **Contract clause C1 is proved for the exact strong-tier quasi-axisymmetric Dommaschk vacuum
  field.** Not certified: confinement inside the torus, nested families, the QS defect, C2.

### N-34: design of the certified QA defect, and an audit item on C2, 1 November 2026

- `notes/theory/dommaschk-qs-defect.md` (N-34): on an invariant vacuum torus the Boozer angles are
  explicit (φ_B = Φ∘K, θ_B = θ + ι(φ_B − φ)); the QA defect is ∂_{φ_B}|B|, which is exactly the
  bridge's `symmetryDefect` on one surface and bounds the oracle's Boozer spectral defect
  (defect·B00 ≤ (√2/N)‖g‖_{L²(J)}). Untrusted: on torus C defect/|ι| = 0.0019 (spectral), sup of the
  defect 0.0090. Correction: the N-31 κ figures are about 2× optimistic (mode truncation). Plan:
  A1 `Theory/Fields/VacuumBoozerTorus`, A2 `BoozerWirtinger` (needed for the strong tier), D3–D7 the
  ball chain and identification (on demand, laptop). Prototype `Design/DommaschkQSProto` (on demand).
- **Audit item AC-1 (medium; high as soon as C2 is claimed for an actual field):**
  `OmnigeneityContract F c κ` is not tied to the physical field (a trivial Boozer model satisfies it
  for any candidate). Proposed fix: `∃ F, BoozerModelOf B Ω F ∧ OmnigeneityContract F …` with a proved
  chart. No C2 claim for the Dommaschk field is made until then.

### N-34 D3: polynomial form of the QA defect for the Dommaschk field, 1 November 2026

- `Design/DommaschkKamCQSData` (generated by `scripts/dommaschk_kam/emit_qs.py`) and
  `Design/DommaschkKamCQSPoly` (default build): torusQADefect = ∂_{φ_B}|B| = N_g/(2Q√Q R⁹) with
  Q = n_R² + R²D² + n_z² (= R¹⁶|B|²) and N_g = N₀ + ι(N₁u_θ + N₂z_θ) evaluated as a program of products
  (`QSLeaves`; expanded N₁ would have 45k terms). Kernel-checked φ-derivative and R-form data; field
  identities `normSq_flow`, `boozerJ_flow`, `boozerA_flow`, `qsDefectSq_eq`, `qsDefect_eq_real`;
  rejected fixture `qsDefectSq_needs_invariance`. Validated on torus C (256² grid): agrees with the
  estimator to its finite-difference error (5.7e-9); sup of the defect 0.009002. Axiom audit passed
  (50,460 declarations).

### N-34 A1: vacuum Boozer angles on an invariant torus, 1 November 2026

- `Theory/Fields/VacuumBoozerTorus` (default build): `torusQADefect` (= ∂_{φ_B}|B| on a torus),
  `boozerJac_eq_normSq_div` (J = ‖B‖²/B^φ on a `FieldTorus`), vacuum angle facts (straight field lines in
  (θ_B, φ_B)), the Boozer direction `boozerPhiVec_eq_field`, the QA characterisation in both directions
  (`torusQADefect_eq_zero_of_qa`, `exists_qa_of_torusQADefect_eq_zero` without the implicit function
  theorem), `boozerAngles_bijective` (J > 0 and a bounded potential), links `qsError_eq_torusQADefect`,
  `WeakQSDefect.torusQADefectLe` (the torus defect is the trace of the δ₂ component of `WeakQSDefect`) and
  `symmetryDefect_eq_torusQADefect_vacuum` (the bridge's hypothesis on one surface). Sanity: the circular
  torus of ∇φ (defect 0), a rippled toroidal field (defect ≠ 0; not a vacuum field), normalisations.
  Axiom audit passed (50,609 declarations).

### N-34 A2: spectral bound for the Boozer QA defect, 1 November 2026

- `Theory/Fields/BoozerWirtinger` (default build): in the KAM chart, with no change of variables:
  orthonormality of the Boozer modes in L²(J) via a divergence identity (`torusAvg_jac_boozerMode`, no
  irrationality of ι needed), `boozerCoeff_chartDefect` (c_mn(∂_{φ_B}|B|) = −inN c_mn(|B|)), Bessel for a
  positive functional, hence the **full off-QA spectrum** bound `tsum_normSq_boozerCoeff_le` and the
  oracle-normalised `torus_oracleDefect_le`: oracle defect ≤ √2 δ/(N B_min) (and the L²(J) form
  `oracleDefect_le`). Sharp (`singleMode_bound_attained`; `not_oracleDefect_le_of_lt_sqrt_two`).
  Not formalised: the oracle's field-line Birkhoff mean equals the grid mean (unique ergodicity).
  Concrete tori supply `BoozerChartHyp.of_torus` (C² potential, C¹ |B|, 2π/N periodicity, B^φ > 0).
  Axiom audit passed (50,789 declarations).

### N-34 D4–D7: certified QA defect on the C1 torus, 2 November 2026

- D4/D5: on-demand `Design/DommaschkKamCQSDef*` and `DommaschkKamCQSTransfer` (≈ 8 CPU-min on top of the
  admissibility chain, peak 3.3 GB; generator `scripts/dommaschk_kam/emit_qsdef.py`): on every μ-close
  torus, sup |∂_{φ_B}|B|| ≤ δ_∞ = 0.020642, |B| ≥ 1.04259, D ≥ 0.1578, κ = 2δ_∞/(B_min|ι|) ≤ 0.165, and
  the L²(J) quantity δ₂ ≤ 0.00224; the surrogate is not exactly QA (`surr_G_ne`).
- D6: on-demand `Design/DommaschkKamCQSIdent`: on the exact torus, `VacuumPotentialOn`, **B^φ > 0**,
  regularity and π-periodicity (`BoozerChartHyp`), `torusQADefect_eq` (the D3 formula), hence
  `torusQADefectLe … (21/1000)`, `Bmin_le`, `oracleDefect_le`.
- D7: on-demand `Design/DommaschkKamCQS`: **`dommaschk_C1_qaDefect`** (unconditional: the C1 torus of the
  exact Dommaschk field carries per-torus QA defect ≤ 0.021, |B| ≥ 1.04259, B^φ > 0) and
  **`dommaschk_C1_oracleDefect`** (off-QA Boozer spectral defect, oracle normalisation, ≤ √2 δ/(2B_min)
  < 0.0141, i.e. ≈ 0.058 |ι|: sup route, just outside the moderate tier). The L² route (≈ 0.0063 |ι|,
  strong tier) needs the pointwise identity for F and the torus/strip average identification (open).
- Fix: `DommaschkKamCQSPoly.Qp` renamed `QpQS` (it clashed with `DommaschkKamCAdmFrame.Qp`, so the default
  build could not be combined with the on-demand chain). Standard axioms throughout.

### N-34 complete: strong-tier certified QA defect on the C1 torus, 2 November 2026

- On-demand `Design/DommaschkKamCQSL2`: **`dommaschk_C1_oracleDefect_L2`**: on the certified C1 torus of
  the exact Dommaschk field, the off-QA Boozer spectral defect (oracle normalisation, every finite set of
  off-QA modes, hence the full spectrum) is ≤ (√2/2) δ₂/B_min < 0.0016, i.e. ≤ 0.0063 |ι|
  (`oracleDefect_L2_num`): **strong tier** of the Q-16 criterion (≤ 0.01 |ι|), certified. Key lemmas:
  `torusAvg_eval_psi` (torus box average of a strip element = its constant Fourier coefficient),
  `four_mul_sqJ_eq` and `weightedL2Sq_le_mF`. Standard axioms.
- Q-16 status: for the Dommaschk target, C1 and a strong-tier certified QA defect hold on **one**
  certified torus (thin core, r_eff ≈ 0.02). Open: a nested region (a second certified torus and a
  nesting certificate), and C2 (AC-1, a Boozer model tied to the field; a volume Boozer chart does not
  exist exactly for this non-integrable field).

### Audit fix AC-1: C2 tied to the physical field, 2 November 2026

- `Theory/Contract/BoozerModel` (default build): `BoozerChart`, `BoozerModelOf`; C2 =
  `OmnigeneityContract B Ω c κ := ∃ F, BoozerModelOf B Ω c F ∧ BoozerModelOmnigeneity F c κ`. The old
  predicate is renamed `BoozerModelOmnigeneity` (model level). `exactQA`/`reactorQA` results are Boozer-model
  statements. Field-level C2 instance so far: ∇φ (vacuous, ι = 0). Axiom audit passed (50,921 declarations).

### A nested certified region for the Dommaschk field (Q-16), 2 November 2026

- Torus A certified (on-demand `Design/DommaschkKamA*`, emitters generalised with `--tag`, torus-C outputs
  byte-identical): `DommaschkKamA.dommaschkA_C1_unconditional` (C1 with ι_min = 0.2386; 6/25 is impossible for
  A, `not_C1_iotaMin_A`), `dommaschkA_iotaOnTorus_unconditional`; κ ≤ 8.79 × 10¹², certified e₀ = 6.2 × 10⁻²⁶
  against a requirement ≤ 6.07 × 10⁻²⁴ (margin ≈ 98); same field instance and moving centre as torus C.
- Nesting (`Design/DommaschkKamNested`): `NestedTori` (both tori have a poloidal angle about one reference
  curve, and along every ray C comes strictly before A; consequences `disjoint`, `inside`); `nested_of_exact`,
  **`dommaschk_nested`** (two certified invariant tori, ι_C and ι_A, nested) and **`dommaschk_nested_C1`**
  (C1 on the family {C, A} with ι_min = 0.2386). Certified by positivity via squared approximate inverses and a
  common quadratic gauge (G < 1 near C, G > 1 near A). 77 on-demand modules, ≈ 70 min on the laptop, peak
  5.77 GB. Standard axioms.
- Q-16 vacuum criterion for the Dommaschk target: certified tori on a nested region (C inside A), |ι| ≥ 0.2386
  on both, and a certified strong-tier QA defect on torus C (A's defect not yet certified). Open: the defect
  on A, and C2.

### Q-16 vacuum criterion met on a nested pair of certified tori, 2 November 2026

- Torus-A QA-defect chain (on-demand `Design/DommaschkKamAQS*`; `emit_qsdef.py --tag`, C outputs
  byte-identical): δ_∞ ≤ 0.032, δ₂ = 0.0031, B_min ≥ 1.02656, B^φ > 0;
  `dommaschkA_oracleDefect_L2` ≤ 0.0090 |ι_A| (strong tier).
- **`DommaschkKamQ16.dommaschk_Q16_vacuum`** (on-demand `Design/DommaschkKamQ16`,
  `lake build PlasmaLean.Design.DommaschkKamQ16`): the exact Dommaschk vacuum field has two certified
  invariant tori C and A, **nested**, with |ι| ≥ 0.2386 on both, zero net toroidal current (C1 on {C, A}),
  per-torus QA defect ≤ 0.021 / 0.032, |B| ≥ 1.0426 / 1.0266, and certified off-QA Boozer spectral defect
  ≤ 0.0063 |ι_C| and ≤ 0.0090 |ι_A|; `dommaschk_Q16_strong` (≤ 0.01 |ι| on both). This meets the decided
  vacuum Q-16 criterion (certified tori on a nested region, ι ≥ ι_min, defect small relative to ι, strong
  tier) for a nested pair. Scope: two thin surfaces (r_eff ≈ 0.02, 0.037); not omnigeneity of a region (no
  C2; AC-1 requires a Boozer chart of the field). Standard axioms.

### Notes housekeeping and the add-note skill, 3 November 2026

- New skill `plasmalean-add-note` (`.agents/skills/plasmalean-add-note/SKILL.md`; triggers "add a note",
  "make a note", "record this"): new vs update, template, ID allocation, registration in RG.1–RG.3, §13
  and the theory index, audit items, publishing. The develop-theory skill now requires every file in
  `notes/theory/` to be registered and asks for metadata rewrites instead of append-only updates.
- `kamflow-g-status.md` registered as **N-35** (status log, metadata table, current-state summary);
  N-33 and N-34 added to `notes/theory/README.md` and their metadata brought to the current state; N-31
  gained a current-state summary.

### Metadata for the older theory notes, 3 November 2026

- Metadata added to the 15 older theory notes; all notes in notes/theory/ now follow the template.
  The notes were N-1, N-4–N-17 (all already registered in RG.3, so no new IDs). Each table gives the
  current status from RG.1–RG.3, Lean evidence with names grepped in `PlasmaLean/` (default build or
  on demand), and audit findings from the 30–31 October records. Where a body was outdated, a short
  "Current state" paragraph follows the table (all except N-16, whose integration note is current).
  `notes/theory/README.md` gained index lines for N-8, N-11 and N-13–N-17.

### Implemented notes keep their content: the modify-notes skill, 3 November 2026

- **New skill `plasmalean-modify-notes`** (triggers "modify notes", "add notes"). It surveys the
  notes and their metadata, edits in place only notes with no Lean implementation, and records every
  change to a wholly or partially implemented note as a new note.
  - A *method note* (Kind `method`) records an additional or alternative approach.
  - A *patch note* (Kind `patch`) has a `Patches` row and states its effect on the existing
    declarations.
  - Implemented notes get bookkeeping edits only: real implementation progress and a
    `Patched by / Alternatives` row.
- **Classifier.** `scripts/notes/implementation_status.py` classifies notes as `none`, `partial`,
  `whole` or `check`. On 3 November every registered note has some implementation:
  N-35 (a status log) reads `check`, and the rest read `partial` or `whole`.
- **Updated to match:** the template (new kinds and optional rows), add-note, develop-theory, the
  skills index and README.md.

### Metadata for the topic notes N-18–N-25, 3 November 2026

- The template metadata table now heads N-18–N-21, N-23 and N-25; the groups N-22 and N-24 carry one
  table each in `notes/goals/README.md` and `notes/formalization/README.md` (chapter files unchanged).
- Lean evidence was grepped in `PlasmaLean/` (all cited modules are in the default build); planned but
  absent names are listed as such. Audit evidence comes from the 30–31 October records.
- "Current state" paragraphs were added to N-18, N-19, N-20, N-22, N-23 (the docs-audit VD4 item: the
  rational field is the C1 witness) and N-24. `notes/README.md` gained the N-IDs in its index lines.

### Alignment with the LeanTheory template, 3 November 2026

The LeanTheory template (github.com/siddhartha-gadgil/LeanTheory) was extracted from this project
and then gained structural additions. They are now incorporated here.

- **Docs.** `docs/GettingStarted.md` covers the workflow: the project graph, the architecture, the
  six steps from setup to reporting, the ways to interact, and the agent prompts. It is linked from
  README.md, CONTRIBUTING.md, `notes/README.md` and the skills.
- **Notes.**
  - `notes/goals/method.md`: generic goal-stating guidance with PlasmaLean examples.
  - RG.6: the definition of done for notes, verified results and goals, and the evidence gates.
  - Metadata for N-18–N-25.
  - RG.3 rows N-18 and N-24 corrected: B–D are compiled under other names, and the C1/C2
    definitions are in Lean.
  - Two stale names in `00-model-contracts.md` fixed: `omnigeneityContract_zero_iff` →
    `boozerModelOmnigeneity_zero_iff`; the nonexistent `currentFreeTransform_of_vacuum` replaced by
    per-torus C1 witnesses.
- **Skills.**
  - Every LeanTheory skill already had a PlasmaLean counterpart (`domain-design` =
    `plasmalean-design-stellarator`).
  - Added: the L0–L5 verification ladder and the tradeoff/tolerance section (design); the generic
    hazard list (audit); the exact-phrase rule and reading list (develop-theory).
  - `agents/openai.yaml` added for develop-theory, workstation-update, add-note and modify-notes.
- **README.** New Policies section.

### The update-notes-from skill, 3 November 2026

New skill `plasmalean-update-notes-from` ("update notes from <files>"), the source-driven variant
of "update notes" (`plasmalean-modify-notes`, which now also answers to "update notes"). It works in
five steps:
1. acquire the sources safely and record provenance with a SHA-256 hash;
2. read each source in full and build an extraction table (claim, locator, kind, hypotheses,
   relevance);
3. check each claim against the compiled Lean code, the notes and the audits, and re-derive
   explicit content where cheap;
4. write one source-assessment note (as N-32 did);
5. update the notes under the in-place versus method or patch rule.

README.md, `docs/GettingStarted.md`, CONTRIBUTING.md, the skills index and develop-theory updated.

### Notes updated from the kinetic plasma and coils brief, 4 November 2026

Source: `sources/PlasmaLean_Kinetic_Coil_Research_Brief.pdf` (3 November 2026, prepared for Vamsi
Pingali and the PlasmaLean agents; SHA-256 `0ab99948…d2ecdd`; inspected snapshot `703c406`).
- **N-36** (source assessment): 50 claims extracted, 22 checked and correct, 0 incorrect, 28 unverified (standard or cited
  physics, models, proposals). Exact checks `scripts/kinetic_brief/check_brief.py` passed 12/12: Landau kernel, energy-flux
  decomposition, non-constant-Maxwellian fixture, d³v Jacobian, GK free-energy identity, inward-radius discriminant, Hodge-star
  sign. The brief's description of the repository at `703c406` is accurate. Its packages are cited as KB-P0–KB-P10, to avoid
  clashing with the roadmap gates.
- **N-37** (patch to N-32): the lift β + dt ∧ α is self-dual for orientation dt ∧ vol₃ and anti-self-dual for vol₃ ∧ dt.
  No Lean effect.
- **Method notes:**
  - **N-38** for N-5/N-6: burn dynamics, fuel depletion, kinetic yield, alpha deposition.
  - **N-39** for N-19: additive-residual inward radii and the norm-to-observable step.
  - **N-40** for N-20: kinetic contract fixtures and the free-energy route to a turbulent flux bound.
- **New questions:** Q-26 (a)–(c) lean-ready; Q-27 (a) lean-ready; Q-28 (a) lean-ready, (b)–(c) research.
- **In place:** N-22 (`notes/goals/README.md`) gains the brief's acceptance table and rejection tests. The finite-horizon
  maintained-state goal is recorded there as a proposal only (user decision; no new G-*).
- **Audit:** AK-1 (full prompt alpha deposition unnamed in G-2 scope), AK-2 (fixed density implies fuelling; "or forever"),
  AK-3 (N-32 orientation, resolved by N-37), all low.
- **Rows updated:** RG.1 G-1 (scope: low net current ≠ no current-driven modes), G-2, G-7, G-8.

### Laptop build budget raised to 12 GB, 4 November 2026

User decision: the laptop (WSL2, 22 cores, 23 GB RAM) may use **12 GB of Lean memory at a time**.
Heavy modules build alone and may use up to 12 GB: certificate checks, or any module with a known
peak above 3 GB. Up to 3 light modules may build at once within the total. This replaces the rule
"≤ 6 GB per process, stale dependencies one at a time".
- **Updated:** the skills (develop-theory, audit-domain, lean-proofs, formalize-theory,
  certify-numerics, design-stellarator, workstation-update, skills README), `Workstation.md`,
  `docs/GettingStarted.md`, README, `scripts/README.md` and `scripts/workstation/README.md`.
- **Workstation verdict:** the default `LAPTOP_MAX_RSS_GB` is now 12 (`ws_helper.py`, `run.sh`,
  `TEMPLATE.sh`).
- **Memory is not predictable from source size:** `Design/KamTorusAWeightedCheck` (7.7 KB) peaked
  at 9.05 GB in the 4 November rebuild, above the old 6 GB rule.
- **Rebuild method:** stale modules are rebuilt by frontier, i.e. the modules that
  `lake build --no-build PlasmaLean` lists, each with its own `lake build <M>`. They are never
  rebuilt through one `lake build` of a top module.

### Default build rebuilt and axiom-checked, 4 November 2026

- **Rebuild:** `lake build --no-build PlasmaLean` showed 53 stale modules at the first frontier.
  The modules were rebuilt by frontier on the laptop (WSL2): first one at a time, then under the
  12 GB budget (heavy modules alone, up to 3 light ones at once).
  - **Result:** 747 modules in 33 rounds, no failures, zero warnings, about 562 summed
    module-minutes. It ends at `All targets up-to-date (3888 jobs)`.
- **Peak memory above 6 GB:** `Design/RationalStellaratorGCMuFlow` 9.40 GB and
  `Design/KamTorusAWeightedCheck` 9.05 GB, both within the 12 GB budget and above the old 6 GB
  rule. Twenty more modules peaked at 5.0–5.7 GB: the Solov'ev ballooning cells,
  `GCTorusCheck`/`GCNegTorusCheck` H1/H7/H8/H14, `KamTorusACheck`, `KamTorusATwist`,
  `NearAxisQAAveragedAmp3`, `RationalStellaratorConfinedFaces` and `LandremanFamily2Cert1`.
- **Axiom check:** `lake env lean scripts/check_axioms.lean` passed (84 s, peak 5.7 GB). All 426
  entry points depend only on `propext`, `Classical.choice` and `Quot.sound` (423 on all three,
  1 on `propext` and `Quot.sound`, 2 on `propext` alone).
- **Not run:** on-demand top modules, which are outside `PlasmaLean.lean`.

### TauCeti dependency and Lean v4.35.0, 16 November 2026

User decision: PlasmaLean depends on [TauCeti](https://github.com/TauCetiProject/TauCeti) at tag
`v4.35.0`; Mathlib is a transitive dependency at the commit TauCeti pins (`0740637`); Lean is
`v4.35.0` (TauCeti has no `v4.34.1` tag). Branch `tauceti`.
- **Fixes (15 Lean files, no statement changed):** ten files needed Mathlib imports that were no
  longer reached transitively (`Deriv.Pow`, `Deriv.Comp`, `ContDiff.WithLp`, `FDeriv.WithLp`,
  `SpecialFunctions.Sqrt`); four needed explicit binder types on `MapsTo` lambdas; one
  `positivity` became an explicit `div_nonneg`; two tactics flagged by the unused-tactic linter
  were removed.
- **Build (workstation, 128 GB, plain parallel `lake build`):** default build 3933 jobs, zero
  warnings; the 18 on-demand top modules of `check_axioms_heavy.lean` (933 modules, 38.5 min,
  largest process 7.7 GB), zero warnings.
- **Axiom checks:** `check_axioms.lean` and `check_axioms_heavy.lean` (115 entry points) passed,
  standard axioms only.
- **Docs:** README, `Workstation.md` and the `plasmalean-lean-proofs` skill name the new versions.

### Differential-form kernel (N-45), 16 November 2026

New kernel file `Kernel/Forms` and `Sanity/Forms` (25 theorems), added alongside the existing
kernel (user decision: an addition, not a replacement; degrees of forms chosen naturally).
- **Equivalences:** `flat : Euclid3 ≃ₗ Form 1`, `flux : Euclid3 ≃ₗ Form 2`,
  `density : ℝ ≃ₗ Form 3`, `hodge : Form 2 ≃ₗ Form 1`. B and J are 2-forms, `dp` and `B♭`
  1-forms, `∇ · B` a 3-form.
- **Dictionary:** `extDeriv_flat` (`d(B♭) = flux (∇ × B)`), `extDeriv_flux`
  (`d(ι_B vol) = (∇ · B) vol`), with no differentiability hypothesis.
- **Laws:** `VacuumForm` (`dω = 0`, `d(⋆ω) = 0`) with `vacuumForm_flux_iff`,
  `vacuumField_fluxSymm_iff`; `FormForceBalance` (`ι_B ω_J = dp`) with `formForceBalance_iff`,
  `forceBalance_iff`; `form_field_tangency`.
- **Sanity:** statements afresh in form language, proofs transported; V-1 and E-1 restated
  (`vacuumForm_empty`, `formForceBalance_of_interior`).
- **Build:** default build 3944 jobs, zero warnings; `check_axioms.lean` passed on 51,023
  declarations.
- **Rows updated:** RG.3 N-45. Not audited yet.
- **Site:** a slide (`differential-form-kernel`) and the Rosetta-stone page and Markdown of the
  exposition suite name the new declarations. No new progress report: the latest report stays
  report 15, as for the other work since 30 October, because the slides link into its sections.

### Rosetta-stone page extended from the literature, 16 November 2026

The exposition page `docs/PlasmaLean_Exposition_Suite/rosetta-stone.html` and its Markdown copy
now have 29 entries (was 14): 14 in the library, 12 partly, 3 illustrative sketches. No Lean
change.
- **New entries (15):** Clebsch representation; field lines as a Hamiltonian system; net toroidal
  current as periods of `B♭` (C1); min-B and subharmonicity of `|B|²`; KAM persistence; stellarator
  symmetry; Arnold's structure theorem and Grad's conjecture; Beltrami fields and contact forms;
  helicity and Taylor relaxation (sketch); frozen-in flux (sketch); Noether momentum; Lorentz
  orbits; omnigeneity and `J∥`; Suydam/Newcomb/ballooning as Jacobi criteria; flux-surface average
  (coarea formula).
- **Corrected entries:** rotational transform (the library has `IotaOnTorus`,
  `IotaOnTorus.tendsto`) and Boozer coordinates (the library has `BoozerChart`, `BoozerModelOf`;
  no existence theorem).
- **Sources:** each entry lists its references. About 20 were confirmed by web search (MacKay 2020;
  Burby–Kallinikos–MacKay 2020; Rodríguez–Helander–Bhattacharjee 2020;
  Constantin–Drivas–Ginsberg 2021; Etnyre–Ghrist 2000; Cantarella–DeTurck–Gluck 2001, 2002;
  Cary–Littlejohn 1983; Enciso–Luque–Peralta-Salas 2025; Bruno–Laurence 1996; and others). The
  older classical references and two article numbers are cited from memory and are **not
  checked** against the sources.
- **Checks:** every cited module path and declaration name was grepped in the source; the page
  script renders 29 cards; site checks pass.
- **Open wording:** the Grad entry describes `family1_grad_counterexample` by its statement and
  says Grad's conjecture for smooth fields in toroidal domains of ℝ³ remains open (to be
  confirmed against Q-17).
  **Corrected the same day (N-47):** that sentence was wrong. Grad's conjecture was disproved in
  September 2026 (Gómez-Serrano–Liehr–Taylor, arXiv:2609.24739, with a Lean certification), as
  N-28 records; the page now says so.
- **Rows updated:** N-45 (pointer and further `Kernel/Forms` bridges: Beltrami predicate,
  `SymmetricFlux`).

### Theory-layer form bridges (N-45), 16 November 2026

New module `Theory/Fields/FormBridges` (425 lines, default build), an addition: no existing
declaration changed.
- **Bridges (each an `iff` in both directions):** first integral (`formFirstIntegralOn_flux_iff`),
  `Kinetic.SymmetricFlux` as `ι_K ω_B = -G♭` (`formSymmetricFlux_iff`), weak quasisymmetry
  (`formWeakQS_flux_iff`), Beltrami fields `dβ = λ ⋆β` (`formBeltramiOn_flat_iff`; the
  vector-language predicate `IsBeltramiOn` is new).
- **Contact condition:** `wedge12`, `wedge12_apply` (it is the alternating product),
  `IsContactAt`, `isContactAt_of_beltrami` (`β ∧ dβ = λ|B|² vol`), `VacuumField.not_isContactAt`.
- **Fixtures:** `helicalField_beltrami`, `helicalField_contact`, `helicalField_not_beltrami_one`,
  `const_beltrami`, `const_not_contact`, `formWeakQS_uniform`, `formWeakQS_screw`.
- **Build:** default build 3945 jobs, zero warnings; `check_axioms.lean` passed on 51,094
  declarations (seven entry points added).
- **Site:** the Rosetta-stone entries for flux surfaces, the solenoidal field, quasisymmetry,
  symmetry and Beltrami fields name the new declarations.
- **Rows updated:** RG.3 N-45. Not audited yet.

### Strict audit of the form modules, 16 November 2026

Partial audit (skill `plasmalean-audit-domain`) of `Kernel/Forms`, `Sanity/Forms` and
`Theory/Fields/FormBridges` at `1e5d4f3`, by the author's pass and an independent read-only
sub-audit. Record: `notes/audit/2026-11-16-forms-audit.md`; summary in RG.4.
- **Result:** no false theorem; 1 high (documentation), 7 medium, 5 low findings; all resolved
  except AD-L4 and AD-L5 (low).
- **Definitions changed:** `IsBeltramiOn`, `FormBeltramiOn` (differentiability clause).
  **Renamed:** `not_isContactAt_of_vacuumField`, `vacuumForm_const_smul`. The kernel file's
  global `Fact` instance is now local.
- **Added:** `form_current_tangency`, `formGradient_zero_iff_force_free`, `flux_cross_apply`,
  `FormSymmetricFlux.formFirstIntegralOn`, `isBeltramiOn_iff_curl`,
  `IsBeltramiOn.formForceBalance`, `IsBeltramiOn.isContactAt_iff`; module `Sanity/AuditForms`
  (29 theorems), including checks independent of the dictionary (`extDeriv_x_dy`,
  `div_curl_eq_zero`, `wedge_eq_inner_hodge`).
- **Build:** 3946 jobs, zero warnings; `check_axioms.lean` passed on 51,135 declarations.
- **Still unaudited:** all other changes since `921a8c3`.

### Assessment of Sullivan's fluid models (N-46), 16 November 2026

Source `sources/SullivanFluids.pdf` (J. Differential Geom. 97 (2014) 141–148), assessed at the
user's request with a literature search; note `notes/theory/sullivan-infinity-structures.md`.
- **Result:** no design consequence. As a language, L∞ structures fit the induction equation
  (`∂_t B = -[v, B]`) and the homological data (fluxes, net currents); as a numerical method there
  is no implementation, stability or convergence theory, and the geometry is a periodic cubical
  lattice. Of the five clauses C1–C5 only C1 is natural in these terms; C5 (thermal) is not
  expressible at all, being dissipative transport and not ideal dynamics.
- **Observation (proved in the note):** on the flat 3-torus the dg Lie algebra of multivector
  fields is quasi-isomorphic to an abelian one, so homotopy invariance preserves only homology
  classes; all dynamical accuracy depends on the chosen contraction (Lawrence–Ranade–Sullivan:
  the (k+1)-th bracket is `O(h^k)`).
- **Lean:** new module `Theory/Fluids/EulerianODE` (Part 2 of the source):
  `EulerianODE.energy_conserved`, `EulerianODE.helicity_conserved` (not stated in the source),
  `rigidBody_eulerian`, `eulerianODE_zero`, `not_eulerianODE_id`.
- **Registry:** N-46 added; Q-33 opened (deformation complex for quasisymmetric equilibria,
  speculative).

### Assessment of Issan et al., equilibria with any number of field periods (N-47), 16 November 2026

Source `sources/Non-AxisymmetricMHD.pdf` (arXiv:2611.07672v1), assessed at the user's request
with a literature search and independent numerical checks; note
`notes/theory/issan-arbitrary-field-periods.md`.
- **Checks (untrusted numerics, `scripts/issan_equilibria/`):** for the three families,
  N = 1, …, 5, both signs: the Cartesian equations `∇·B = 0`, `J × B = ∇p`, `B·∇ψ = 0` hold to
  `10⁻³⁷` at random points; the linking number of a field line with the axis is 0 or ±N as the
  paper states; the instability identities hold. 12 of 20 claims checked, none incorrect.
- **Contract:** not candidates. C1 fails (ι = 0, or integer ι with net current), C3 fails (the
  paper proves interchange instability), C4 holds as an exact model statement, C2 and C5 are not
  addressed.
- **For Q-20:** Family 1 with ρ_a = ρ₀ is an exact finite-β equilibrium with zero net toroidal
  current through every surface, and ι = 0.
- **Correction:** the Rosetta-stone page said Grad's conjecture remains open; it was disproved
  in September 2026 (N-28). Page corrected.
- **Leads found by the search:** arXiv:2611.16688 (an analytic equilibrium with trivial Euclidean
  symmetry group), arXiv:2611.10786 (anisotropic equilibria with confined drift orbits); not read.
- **Registry:** N-47 added; Q-20 and N-28 updated. No Lean change.

### Reasoning-loop skills from LeanTheory, 17 November 2026

- **New skills** (adapted from the LeanTheory template, commit `97e5862`): `plasmalean-try-to-prove`
  (`try to prove …`) and `plasmalean-explore-mathematics` (`explore …`) run
  `plasmalean-reasoning-loop` (deconstruct, triage, source study, strategy or probes, execute,
  verify, metacognition, stress tests, synthesis), supported by
  `plasmalean-examples-counterexamples` and `plasmalean-proof-techniques` (16 generic techniques;
  plasma-specific ones such as energy principles, comparison/Riccati arguments and certificate
  reductions are to be added as they recur).
- **Task folders:** every attempt writes to `notes/reasoning/<YYYY-MM-DD>-<slug>/`; Lean drafts in
  its `lean/` are checked within the 12 GB laptop budget. Outcomes are registered with
  `plasmalean-add-note`; evidence states are unchanged (proof-ready, lean-ready; verified only after
  promotion into `PlasmaLean/`).
- **Wiring:** develop-theory (routing, sub-agents, autonomous selection), discover-theory,
  formalize-theory, audit-domain (sanity triad witnesses), certify-numerics, design-stellarator,
  lean-proofs, add-note, modify-notes and update-notes-from (source study, techniques, examples and
  stress tests in a `notes/reasoning/…-source-…` folder) now use the new skills; README,
  GettingStarted, `notes/README.md` and the skills README document them.
- **Plasma proof techniques** (same day): six techniques added under
  `.agents/skills/plasmalean-proof-techniques/techniques/plasma/`, each with worked examples citing
  compiled declarations (names grepped): energy principle and coercivity (`suydamForm_lower_bound`,
  `picone_certificate`, `BartaCertificate.lower_bound`, `displacement_bound`); comparison, barriers
  and Grönwall/Riccati (`le_of_lowerMargin_axisFree`, `fieldLine_sign_preserved`,
  `riccati_le_initial`, `excludes_loss`); reduction to a finite certificate
  (`radii_polynomial_fixedPoint`, `bool_cert`); perturbation margins (`filamentField_perturbation`);
  local obstructions and necessity (`VacuumField.not_closed_fieldLine_minB`,
  `quasisymmetry_not_pde_symmetry`, Sturm necessity); composition on a common witness
  (`compose_branch`, `incompatible_witnesses`).

### Task server and evolutionary search from LeanTheory, 17 November 2026

- **Lean:** `PlasmaLean/ResponseExt.lean` (`@[response "task"]` handlers), `PlasmaLean/Elaborate.lean`
  (elaborating code from strings) and `PlasmaLean/TaskHandlers.lean` (tasks `check`, `eval`,
  `assess`), from LeanTheory `72e8608`–`406a45b`, now in the default build (imported by
  `PlasmaLean.lean`); executables `theory_loop` (JSON lines) and `theory_server` (HTTP on
  127.0.0.1, web page with PlasmaLean examples such as `PlasmaLean.Transport.svFloorF 10`).
  The executables import only `PlasmaLean.TaskHandlers` at build time and load `Mathlib` and the
  built `PlasmaLean` at run time, so building them never rebuilds the library.
- **Checks:** all three modules and both executables build on Lean v4.34.1 with no warnings;
  `scripts/check_axioms.lean` passed (77 s, peak 5.9 GB); `check`, `eval`, `elab_term`,
  `elab_defs`, `assess` and `/reset` tested on the server and on `theory_loop`; the toy
  evolution example ran end to end (optimum 40 found, a `sorry` candidate rejected, a candidate
  using a PlasmaLean function measured and validated).
- **Memory:** the server holds 9.3 GB resident (7.2 GB memory-mapped oleans, 2.1 GB heap) and
  is ready in about 50 s. It counts against the 12 GB laptop budget; `ensure_server.sh` refuses
  a stale library (a stale root misses the task handlers) and checks free memory.
- **Skills:** new `plasmalean-ensure-theory-server`, `plasmalean-check-compilation`,
  `plasmalean-evaluate-on-server`, `plasmalean-evolve-optimize` (scripts `scripts/theory_server/`,
  `scripts/evolve/evolve.py`); `plasmalean-examples-counterexamples`, the existence technique and
  the strategy phase of the reasoning loop now assess and launch evolutionary witness searches;
  develop-theory, design-stellarator, audit-domain and lean-proofs updated (resource rule for the
  server; new libraries must reach the executables' `importModules`).

### Note N-41: where evolutionary search fits, 17 November 2026

- New note `notes/theory/evolutionary-search-suitability.md` (N-41, stated): classifies the goals
  by fit for `plasmalean-evolve-optimize`. Good fits: stability test functions (G-4, Q-3), QS jet
  exploration (Q-24, Q-25 d), burn operating windows (G-2, Q-13, Q-26 a), smaller certificate
  pieces (G-9, Q-12), exact refinement of optimizer-proposed design data (G-5, G-8). Partial: KAM
  budgets (Q-2, Q-4, Q-5) on the workstation, extremal audit witnesses. Unsuitable: PDE evolution
  (G-7, Q-7–Q-11), contract definitions (Q-21, G-11), model adequacy (G-3), all-time claims as
  wholes, G-8 as one search. Pilots ranked: Picone gauge (calibration), Q-3 representation search,
  QS jets, burn window.
- Route tags added to Q-3, Q-12, Q-13, Q-24, Q-26. Bookkeeping: the Q-26 row's `|R(f) − R(F)|`
  bars were escaped; they had split the table cell.



### Notes updated from the complex-geometry and stability note, 20 November 2026

- Source: `sources/fusion_complex_geometry_and_stability.pdf` (18 November 2026, through Vamsi
  Pingali; SHA-256 `4f080749…f7e`). The formulas were read from the LaTeX in
  `sources/fusion_complex_geometry_reproducibility/`; no bundle script was run.
- New assessment **N-42**: 35 claims, 30 checked and correct, 0 incorrect, 5 unverified.
  - Exact: the Laurent form of the Dommaschk candidate (121 monomials, harmonic, real, symmetric),
    reproduced from `candidate.json`. The quoted Lean constants (`dkIotaA`, `dkIotaC`, `tauC`,
    `AdmBoundsG.hτ`) match the code.
  - Symbolic and numeric: the weak-QS homological solution and the exact orbit identity.
  - Numeric: the cylinder window and gap, the unstable branch, and the hot-core constants.
  - Stress test: the cylinder window needs a wall within about 5% of the minor radius (unstable
    `m = 1` from `b/a = 1.1` at β ≈ 0.04).
  - Scripts in `scripts/fcg_source/`; analysis in `notes/reasoning/2026-11-20-source-fusion-complex-geometry/`.
- **Method notes:** N-43 for N-29/N-17 (corrected full-orbit flux for exact weak QS, certificate,
  hot-core moments); N-44 for N-12 (signed cylinder benchmark, toroidal interface criterion,
  transfer).
- **New questions:** Q-29 ((a), (b) lean-ready), Q-30 ((a) lean-ready), Q-31 (numerics on torus A),
  Q-32 (certified harmonic perturbations of the Dommaschk seed).
- **In place:** N-40 gains the hot-core moment fixtures. **Pointers:** N-1, N-12, N-17, N-29, N-31,
  N-32, N-33, N-41. **Audit:** AF-1 (low): `FieldTorus` and `NestedTori` do not assert embeddedness.
- **Rows updated:** RG.1 G-1, G-4, G-6. **Gap:** the earlier handoff
  `sources/complex_geometry_handoff.pdf` (cited for the weak-QS equilibrium obstruction and the weak
  MHD lift) is not assessed yet.

### Form kernel with TauCeti v4.36.0, and the complex-geometry notes (N-48), 23 November 2026

- **Upgrade:** Lean and TauCeti at `v4.36.0` (Mathlib `fc4f59e577`). Proof repairs in 19 Lean
  files, no statement changed; all 1688 modules build, both axiom checks pass.
- **First use of TauCeti.** Until now only Mathlib was imported. Three new theory modules, each
  with a sanity module, all in the default build with standard axioms.
  - `Theory/Fields/FormCalculus` (Cartan's formula, Poincaré lemma):
    `WeakQS.lieDerivForm_flux_eq_zero` (the flux form of a weakly quasisymmetric divergence-free
    field is invariant under the generator; step 1 of N-43), `VacuumField.exists_scalarPotential`
    and `…exists_vectorPotential` on star-convex regions.
  - `Theory/Fields/FormTopology` (the bridge to forms on manifolds): `onOpens`,
    `isSmoothForm_onOpens_iff`, `mextDeriv_onOpens`;
    `VacuumField.exists_scalarPotential_of_simplyConnected`;
    `not_simplyConnected_of_no_potential`. Fixture: the wire field has no potential
    (`wireField_no_potential`), so the complement of a line is not simply connected
    (`wireRegion_not_simplyConnected`).
  - `Theory/Fields/FormContact`: `wedge12_eq_wedge` (the hand-written wedge is TauCeti's),
    `isContactAt_iff_nondegenerate` (the intrinsic contact condition), `IsBeltramiOn.reeb`
    (Reeb equations for `B/‖B‖²`).
- **Assessment (N-48):** the kernel fits the hypotheses of N-43 and the vacuum families of N-42;
  it does not fit the cylinder benchmark of N-44 or the kinetic estimates. TauCeti's symplectic
  directory (64 → 650 files) was assessed from its documentation: `Hamiltonian/Noether` and
  `Cotangent/Fiberwise` apply directly to the compiled kinetic theory; the rest needs phase
  spaces as manifolds. None is used yet. No KAM theorem was found in TauCeti.
- **Rosetta-stone page:** nine entries extended with the new declarations.
- **Completed the same day (second commit):**
  - `Theory/Fields/FormPeriods`: `pathIntegral_onOpens_flat` (TauCeti's line integral of `B♭` is
    the contract layer's `lineIntegral`), `periodHom_onOpens_flat` (the period on a loop class is
    the circulation). Fixture: the wire field has period `2π` (`wire_period`).
  - `lieDerivForm_flux` and `WeakQS.lieBracket_eq_zero` (`[ξ, B] = 0`, step 1 of N-43 in vector
    language); `IsBeltramiOn.reeb_unique`.
  - `bentSet_not_starConvex`, `hyperbolic_scalarPotential_bent`: a simply connected region that
    is not star-convex, as an accepted fixture for the simply connected theorem.
  - `Theory/Kinetic/NoetherLagrangian`: `lorentzOrbit_eulerLagrange` and
    `noetherMomentum_translation_conserved`, from TauCeti's Noether theorem; Landau-gauge
    fixture `landau_momentum_conserved`.
- **Phase 1 of the remaining tasks** (three sub-agents in parallel; rebuilt and axiom-checked
  in the main session):
  - `Theory/Kinetic/NoetherRotation`: `noetherMomentum_linear_gauge_conserved` (skew linear
    generator, gauge term), `canonicalMomentum_rotGenZ_conserved`; fixtures in the symmetric and
    Landau gauges.
  - `Theory/Fields/FormLoopCurrent`: `lineIntegral_comp_affine`,
    `loopCurrent_eq_periodHom_div` (the contract's loop current is a de Rham period over `μ₀`),
    `VacuumField.loopCurrent_eq_zero_of_simplyConnected`.
  - `Theory/Fields/FormContactManifold`: `flatSmoothForm`,
    `isContactForm_flatSmoothForm_iff`, `IsBeltramiOn.reebVectorField_flatSmoothForm`.
- **Phase 2** (two sub-agents in parallel; rebuilt and axiom-checked in the main session):
  - `Theory/Kinetic/MagneticSymplectic`: `canonicalForm_fderiv_kineticMomentumMap_flux` (the
    canonical form pulled back by the kinetic-momentum map is `Ω + q π^*ω_B`),
    `lorentzOrbit_hamilton` (Lorentz orbits are integral curves of the Hamiltonian field of
    `‖p♯ − qA‖²/(2m)`).
  - `Theory/Fields/FormHYMLift` (N-42 S-13): `extDeriv_hymLift_eq_zero_iff` (the lift
    `ω − ⋆ω ∧ dτ` is closed iff both vacuum equations hold), `hymLift_closed_iff_vacuumField`,
    `hymLift_isAntiSelfDual` (in components).
- **Second round, phase 1** (three sub-agents in parallel; rebuilt and axiom-checked in the
  main session):
  - `Theory/Kinetic/NoetherSymmetryBridge`: finite rotational equivariance gives the
    infinitesimal condition (`fderiv_rotGenZ_of_rotZ_equivariant`); with `B = ∇ × A`, the
    hypothesis of the direct proof is equivalent to it (`symmetricFlux_symmetryFluxGrad_iff`,
    `axisymmetricFlux_iff_symmetricFlux_rotGenZ`); each conservation law has two proofs.
  - `Theory/Fields/FormLoopCurrentInterval`: `lineIntegral_eq_periodHom` for curves `C¹` on an
    interval; `CurrentFreeTransform.current_eq_zero_of_simplyConnected`; a poloidal loop around
    a wire with period `2π` (`ring_period`).
  - `Theory/Fields/FormContactOpens`: contact forms and Reeb fields on an open subset; a field
    that is contact on a half-space and not on `ℝ³`.
- **Second round, phase 2** (two sub-agents in parallel; rebuilt and axiom-checked in the main
  session):
  - `Theory/Kinetic/MagneticHamiltonConverse`: `lorentzOrbit_iff_emHamilton` (with `E = −∇Φ`,
    the Lorentz equations are equivalent to Hamilton's equations for
    `‖p♯ − qA‖²/(2m) + qΦ`), `emHamiltonian_conserved`.
  - `Theory/Fields/FormHYMStar`: `liftStar` on 2-forms of `ℝ³ × ℝ`, equal to TauCeti's
    intrinsic Hodge star (`euclidForm_liftStar`); `isAntiSelfDual_iff_liftStar`;
    `liftStar_eq_neg_iff_exists` (every anti-self-dual form is a lift);
    `hymLiftCircle` and `mpullback_hymLiftCircleForm` (descent to `Space × AddCircle ℓ`).
- **Third round, phase 1** (three sub-agents in parallel; rebuilt and axiom-checked in the main
  session):
  - `Theory/Fields/FormPiecewisePeriod`: `lineIntegral_eq_periodHom_piecewise` (closed
    piecewise `C¹` loops), `sum_lineIntegral_segCurve_eq_periodHom` (polygons); a square around
    the wire with period `2π`.
  - `Theory/Fields/FormConvexRegion` and `Sanity/ContractLoopCurrentFixture`:
    `simplyConnectedSpace_of_convex`; **`CurrentFreeTransform.imax_zero_of_meridianHalfSpace`:
    for a vacuum field away from the z-axis the net-current bound of contract clause C1 holds
    with allowance `0`** (every poloidal loop with `R > 0` lies in a convex half-space missing
    the axis). Fixture with `ι > 0`: `rationalStellarator_fixture`.
  - `Theory/Kinetic/NoetherGaugeBridge`: `symmetricFlux_gauge_iff`; the gauge term transforms
    as `χ + ⟪∇Λ, K x⟫` and the conserved momentum is gauge invariant
    (`noetherMomentum_add_gradient`); `rotZ_equivariant_iff_commute`.
- **Third round, phase 2** (two sub-agents in parallel; rebuilt and axiom-checked in the main
  session):
  - `Theory/Fields/FormHYMCircle`: the lifted form on the manifold `U × S¹` is closed iff the
    field is a vacuum field on `U` (`hymLiftRegionForm_closed_iff_vacuumField`); regularity
    (`isSmoothForm_hymLiftCircleForm_iff`); the energy identity
    `∫|ℱ|² = 2ℓ∫|B|²` (`integral_liftInner_hymLiftCircle`).
  - `Theory/Kinetic/CrossedFieldOrbit`: the explicit `E × B` drift orbit
    (`crossedField_orbit`, `crossedPosition_period`); local existence and uniqueness of
    integral curves and of Lorentz orbits (`emHamilton_exists_local`, `lorentzOrbit_unique`);
    global existence and uniqueness for uniform fields
    (`lorentzOrbit_existsUnique_uniform`).
- **Still open:** the complex structure, line bundle, Chern class and Yang–Mills minimality of
  N-42 S-13 (TauCeti has no bundle-from-curvature construction or Chern class); the de Rham
  classes of an embedded flux surface; the C1 consequence on the on-demand Dommaschk instances;
  a strict audit of everything added on 23 November 2026.
- **Registry:** N-48 added; pointers in N-45, N-43, N-42.

### Complete refresh audit, 23 November 2026

- Scope and result: see RG.4 and `notes/audit/2026-11-23-refresh-audit.md`. All changes since
  `921a8c3` audited (304 Lean files; documents). No critical finding; 1 high, 12 medium.
- New sanity module `Sanity/AuditContractC2`; regression theorems in the sanity modules of the
  audited files; `dommaschk_Q16_chart`; the tooling's `assess` gate now requires the three
  standard axioms.
- Documents corrected: README (two overclaims), N-48 (a "Current state" section; stale and
  overstated passages), the Rosetta-stone page (magnetic-form sign, clause C1, gauge invariance,
  a dropped hypothesis), N-37, N-35, N-43.
- Record of the renumbering of 22 November 2026 (not logged then): on merging `main` into the
  branch `tauceti`, the notes numbered N-41, N-42, N-43 on that branch became N-45, N-46, N-47,
  the question Q-29 became Q-33, and the forms-audit findings AF-* became AD-*. Commit messages
  `e2dc6a5`, `1e5d4f3`, `9414b7a`, `63fa5f5` carry the old labels.
- **Contract status after the audit:** C1 is verified for the Dommaschk and rational fields in
  the sense of the predicate (a nonempty family of invariant tori with `|ι| ≥ ι_min` and a
  current bound that carries no information for these vacuum fields, AV-M1). C2 has no non-vacuous instance for
  any field (AV-M7), and its `ι` is not tied to that of C1 (AV-M8).


### Fourth round, phase 1 (N-48), 23 November 2026

After the audit. Three sub-agents, each with its own modules; the lead verified and integrated.

- `Theory/Fields/FormHYMComplex` (+ sanity): `liftJ`, `kahlerForm`,
  `liftStar_eq_neg_iff_isType11_and_isPrimitive`, `isType11_and_isPrimitive_hymLift`;
  closedness on the circle product without a regularity hypothesis
  (`mextDeriv_hymLiftCircleForm_eq_zero_iff'`, `VacuumForm.hymLiftRegionForm_closed`).
- `Theory/Kinetic/LorentzGlobalExistence` (+ sanity): `lorentzOrbit_existsUnique_of_linear_growth`,
  `lorentzOrbit_existsUnique_of_potential_bounded_below`, `…_of_energy_bound`.
- `Design/DommaschkKamLoopCurrent` (on demand): `dommaschk_nested_current_eq_zero`,
  `exists_fieldTorus_loopCurrent_eq_zero` by the topological route.
- Checks: full build of all modules; `check_axioms` 52,306 declarations, heavy 59,506.
- Not audited (added after the audited commit `6ceca0e`).


### Fourth round, phase 2 (N-48), 23 November 2026

- `Theory/Fields/FormHYMEnergy` (+ sanity): `neg_wedgeDensity_le_liftInner_self`,
  `integral_liftInner_extDeriv_eq_zero`, `VacuumForm.integral_energy_hymLift_perturbation`
  (`∫(|ℱ + da|² − |ℱ|²) = ∫|da|²` for compactly supported `a` on `Ω × ℝ`), `liftConnection`,
  `VacuumForm.exists_liftConnection`. Not on `Ω × S¹`; no bundle, no Chern class.
- `Theory/Fields/FormFluxSurfacePeriods` (+ sanity): `poloidalPeriod`, `toroidalPeriod`,
  `PeriodicC2Torus.exists_periodic_potential_of_curl_eq_zero`,
  `PeriodicC2Torus.periods_eq_of_periodic_potential`,
  `FieldTorus.poloidalCirculation_eq_of_curl_eq_zero` (AV-M9, third part, under `C²` surface
  and `C¹` curl-free field). On the parameter plane, not on an embedded surface.
- Checks: `lake build` (11,153 jobs), `check_axioms` 52,527 declarations.
- Not audited.


### Fifth round, phase 1 (N-48), 23 November 2026

- `Theory/Fields/FormFluxSurfaceEmbedded` (+ sanity): `EmbeddedTorus`,
  `EmbeddedTorus.isSmoothEmbedding_torusEmb`, `EmbeddedTorus.of_sections`,
  `PeriodicTorus.homeomorph`, `PeriodicC2Torus.exists_potential_on_torus`; the doubly covered
  torus is a `FieldTorus` that is not embedded (`dbl_fieldTorus`, `dbl_not_embeddedTorus`; AF-1).
- `Theory/Kinetic/LorentzOrbitOpen` (+ sanity): `lorentzOrbitOn_exists_local_of_contDiffOn`,
  `lorentzOrbitOn_unique_of_contDiffOn`, `lorentzOrbit_existsUnique_of_confined` for fields
  `C¹` on an open set, no potential (AV-M4, orbit part).
- Checks: `lake build` (11,697 jobs), `check_axioms` 53,036 declarations. Not audited.


### Fifth round, phase 2 (N-48), 23 November 2026

- `Theory/Fields/FormHYMCircleEnergy` (+ sanity): `integral_slab_energy_perturbation`,
  `VacuumForm.integral_slab_energy_hymLift_le`, `VacuumForm.integral_circle_energy_hymLift_le`
  (periodic variations vanishing near `∂Ω`).
- `Theory/Fields/FormHYMBundle` (+ sanity): `torusPeriod_hymLift_fluxField`
  (`−ℓ ∮_γ B·dl`), `chernNumber_hymLift_poloidal`, `LiftBundleData`,
  `LiftBundleData.IsPeriodic.torusPeriod_mem` (periods in `2πℤ`),
  `wire_exists_periodic_iff` (the wire bundle exists iff `ℓ ∈ ℤ`). Cocycle data, not a
  vector bundle; no `c₁` as a class.
- Checks: `lake build` (11,707 jobs), `check_axioms` 53,307 declarations. Not audited.


### Embeddedness clause of C1 (Q-36), 23 November 2026

- By user decision the contract requires embedded tori. New module
  `Theory/Contract/EmbeddedSurfaces` (+ sanity): `EmbeddedSurfaces S`,
  `EmbeddedCurrentFreeTransform` (C1 extended by the clause),
  `EmbeddedCurrentFreeTransform.isSmoothEmbedding`, `isCompact_isClosed`,
  `PoloidalAngle.sections_injective_of_strictMono`,
  `CurrentFreeTransform.embedded_of_sections`, `CurrentFreeTransform.embedded_of_strictMono`.
- `CurrentFreeTransform` is not changed: no existing C1 instance proves embeddedness, and
  changing the structure would have broken all of them. The strengthened clause is the
  contract's C1 from now on; the existing instances prove C1 without embeddedness.
- **Registry:** Q-36 added (one goal per example: rational stellarator torus A, Dommaschk
  tori C and A, the nested pair and Q-16); rows G-1, G-11 and audit item AF-1 updated.
- Sanity: circular tori accepted; the doubly covered torus and the collapsed circle rejected;
  no instance of the full clause with non-zero transform exists yet.
- Checks: `lake build` (11,711 jobs), `check_axioms` 53,331 declarations. Not audited.


### Assessment against the contract after N-49–N-51, 23 November 2026

- Reviewed the notes N-49, N-50, N-51 and the Lean modules of N-51 against the contract section,
  RG.1, RG.2 and RG.5.
- Recorded: a dated status per clause in the contract section; in RG.5 the status of the approved
  order of 30 October and a proposed order (not yet user-approved); corrected stale status cells
  of G-10 and G-11; dependencies of Q-34 on Q-36; remarks on Q-35 and N-51.
- Main findings: no contract clause changed status for a candidate between 2 and 23 November;
  C2 has no field instance and its Boozer-chart form cannot at present be instantiated by a
  certified field; N-51 is a compiled general theorem without a physical band; finite β (Q-20)
  has no compiled progress.
- **User decisions (23 November 2026):** both forms of C2 are allowed (chart form and band
  form); the order in RG.5 is approved and replaces the order of 30 October.
- No Lean change.

### Conceptual methods for trapped particles and vacuum shape, 23 November 2026

Registered N-49 for approximate momentum, period and bounce-average obstructions, and finite-time
exit on a regular trapped band. P1 now specifies the energy-weighted complement and a diffusion
test. Registered N-50 and Q-34 for the normal shape response of a circulation-normalized field
and recorded a separate fixed-domain linearization for Q-24. N-44 now links its interface test
to the current and transform at a nonzero pressure step. These proposals add no Lean evidence.

### Annular averaged flux and trapped-particle confinement (N-51), 23 November 2026

Q-35 is proved for a regular annulus in periodic phase coordinates. The common volume equations give a closed averaged flux. Its period obstructs winding-one invariant curves. With averaged boundary tangency and no zeros, its normalized primitive gives a radial label. Solving the fibre equation removes first-order drift and gives a uniform time window of order ε⁻². Bounded speed and forward ODE continuation give existence throughout that window for every initial state in each closed interior birth band. Local phase charts suffice for the flux and the normalized stream. Constant transverse drift and an oscillatory radial drift test opposite outcomes. The physical bounce coordinates, coverage and quantitative constants for Q-1 and G-6 remain open. [N-51 and Lean declarations](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/annulus-averaged-flux.md)

Verification: the default build completed (11,679 jobs), and the axiom audit passed for 52,887 PlasmaLean declarations.

### Review of the implementation order, 23 November 2026

Registered N-52 and N-53 following the contract review. The Q-36 target covers the rational stellarator, both Dommaschk surfaces, the pair and Q-16. The candidate bounce and finite-pressure screens can proceed independently.

### Embedded C1 on all Q-36 witnesses, 23 November 2026

A one-turn Grönwall bound for the normalized field propagates coincidence and a vanishing
section derivative. Irrational rotation makes either obstruction persist on a whole section.
Winding one forces any period to be a whole turn and excludes a constant section. This proves
`FieldTorus.embeddedTorus_of_irrational` for C² profiles and a C¹ field near the image. The
winding-one fixture at transform zero demonstrates why rational returns require a separate
argument. [N-52](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/irrational-return-embedding.md)

The rational stellarator torus A and both exact Dommaschk tori satisfy embedded C1. The nested
Dommaschk pair retains zero loop current, |ι| ≥ 0.2386, both Boozer chart hypotheses, the two
strip-closeness bounds and both sharp off-QA bounds on the same surfaces
(`DommaschkKamEmbedded.dommaschk_Q16_embedded`). This closes Q-36 and AF-1 for the named
candidates. The solid-torus and shape-response hypotheses of Q-34, a physical C2 bounce band,
and the finite-pressure interface calculation remain open.

Verification on the workstation passed for the default build (11,731 jobs) and all the
on-demand targets imported by the heavy axiom audit (11,240 jobs). The overlapping axiom
audits checked 53,360 and 59,706 project declarations respectively, all within the three
standard foundations. This includes the rational bounded-ball and nested Dommaschk
loop-current fixtures on the embedded surfaces.


### Trapped birth coverage and the physical radial observable, 23 November 2026

G-10 and G-11 now have a field-level, single-species predicate for the finite-time Littlejohn form of C2. `GuidingCentreBand.radial_loss_le` bounds the birth measure of any excess radial excursion. The physical model, reference population, distribution, axis, positive horizon and tolerance are explicit. `radial_excursion_of_reduction` charges position errors at both endpoints. The uniform field fails the trapped criterion. No candidate value for the fraction or time has been proved.


### Domain audit and band sanity cases, 23 November 2026

The audit at `4b0bf64` reviews the N-51 annular theorem and Q-36 on its actual witnesses. Lean now refutes the former blanket exclusion of coil fields from the meridian Stokes argument. A unit-current circle centred at (−2,0,0) with radius one is entirely outside x > 0, and its field is vacuum throughout that half-space. In the single-species band contract a quadratic mirror supports an exact harmonic oscillator and confines every partial solution of the specified birth. Its birth law is a point mass; its field has divergence 2x₀. The default axiom audit checked 53,440 project declarations. [Audit and scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-23-annulus-embedding-audit.md)


### Two mirror-height screens on the physical Dommaschk field, 23 November 2026

A ripple maximum changes the connected bounce class near two phases in the mid-depth screen. The deeper screen survives angular, trace and radial grid refinements at one common action and two distinct energies. The registered N-54 records its launch strip, failed mid-depth attempt, phase-dependent margins and reproducible data. Generic root and winding-graph theorems state what rigorous continuum estimates would establish. Physical scales and thermal acceptance targets remain open by user decision.

The default build passed with 11,741 jobs; the axiom check covered 53,460 declarations. A second end-to-end run on the workstation reproduced the stored numerical record byte for byte.


### 23 November 2026 — period-uniform close-wall benchmark (Q-30a)

The cylindrical interface coefficient satisfies the floor s²/8 for nonaxisymmetric modes and the period-independent gap s²(1+|m|+κ)/80 for all modes under the source multiplier bounds. The fixed-flux zero mode and the wall condition have explicit checks. The Bessel and Neumann estimates, Fourier energy reduction and transfer to curved geometry are separate obligations. [Cylinder proof](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Stability/CylinderInterfaceGap.lean)


### 23 November 2026 — Q-31 pressure-step obstruction

The signed determinant of the metric and curvature rows has a zero on the θ=0 arc of the exact, embedded torus A. Its field-direction normal curvature is strictly positive there, so every tangent variation that raises the pressure to first order violates the source’s strict curvature test. A separate rational calculation obtains the same determinant signs on torus C. The question of stability of a finite-pressure equilibrium remains open. [N-55](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-interface-obstruction.md)


### 23 November 2026 — launch flux and a two-sided field-line segment (N-56)

On the full deeper Dommaschk strip the oriented launch flux is strictly negative. An independent 131,072-tube calculation continues every launch by ±1/8 geometric toroidal radian while keeping the strength below both proposed mirror heights. Lean proves the interpolated magnetic-flux formula and a rectangular step-existence and enclosure theorem. The finite-dimensional candidate bounds are externally checked. The full mirror-to-mirror action and thermal population remain open. [N-56](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-launch-collar.md)


### 23 November 2026 — local fixed-action mirror cell (N-57)

The centred trajectory checker reaches the first two mirrors of the physical Dommaschk trace for every launch in a positive-width cell and every height between the two deep screening heights. On the finer run the one-way actions lie in [1.32513,1.33227] and [1.37004,1.37752]. Their separation from j=1.3599221876644974 and strict increase in height pick out one regular well height at this fixed action per launch. The candidate inequalities are externally checked. Lean proves the geometric-to-arclength transfer, one-sided trajectory error, height inversion and fixed-domain transverse derivative under stated hypotheses. Pulling the births to a common phase raises the phase half-width to 2⁻¹⁶ radian with both action margins intact. The full-circle band and time-dependent thermal confinement remain open. [N-57](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-regular-mirror-cell.md)

### 23 November 2026 — confinement from two radial face bounds (N-58)

The existing annulus proof and the new action test now share a first-exit lemma for arbitrary radial endpoints. Two face bounds and a finite-time action budget confine a continuous radius even if the action has several roots. For winding graphs, positive radial derivative at every crossing of the target suffices. Disjointness and one ordering witness give uniform separation. The physical application still needs both extrema around the launch circle and a bound on the action drift. [N-58](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/action-faces-and-winding.md)

### 23 November 2026 — outward-rounded action bounds at six phases (N-59)

The moving-frame estimate and the launch-connected action envelope are now proved. On the two radial faces of the physical Dommaschk strip, six positive-width sectors satisfy the strict inequalities at the prescribed action. The angular union for those inequalities has length 14/1024 radians over one period of π. A Lean counterexample shows how merging wells can give a jump in this action. Full-circle coverage, finite-time physical drift and thermal birth coverage remain open. [N-59](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-phase-faces.md)

### 23 November 2026 — separated local fixed-action curves at both symmetry phases (N-60)

For every phase within 1/4096 radian of each symmetry centre, both proposed heights have a unique action root in their respective radius brackets. At zero the brackets are (0.470,0.478) and (0.523,0.531). At π/2 they are (0.456,0.464) and (0.509,0.517), in each case listing the higher energy first. The explicit lower gap is 9/200. Sixteen outward-rounded radial tiles control both the line and its transverse tangent, and eight independent endpoint inequalities bracket the target. The two disconnected sectors leave global winding and thermal confinement open. [N-60 and reproducible records](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-local-action-graphs.md)

### 24 November 2026 — Lean replay of the local mirror certificates (N-61)

The workstation replay uses `bash scripts/dommaschk_kam/check_mirror_replay.sh --jobs 6`. Each batch checks available RAM, and each Lean declaration checks at most 16 slabs of the action quadrature data. All 28 packets passed along with the radial and graph modules. The standard-axiom checks passed for 53,987 default and 80,912 on-demand declarations.

The physical Q-16 launch theorem covers both sectors, the whole radial strip, and 1/64 geometric radian in either direction. The 28 endpoint packets compare the action with the target from directed field and density enclosures. The 16 radial tiles give 12,512 consecutive slab records. The long-trajectory comparison still needs verified residual, frame and first-variation bounds for the same physical field line. See [N-61](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-mirror-certificate-replay.md).

### 24 November 2026 — exact long-trace witness and physical observable identities (N-62)

At the phase-zero radius 0.470 the exact witness reproduces the archived mirror crossings and action estimates and extends to ±391/64 radians. Lean glues a chain of moving-frame steps on one solution and identifies the physical field strength and arclength density. The full candidate-specific proof requires the per-slab enclosures on that solution.

### 24 November 2026 — eight complete endpoint replays (N-63)

Independent exact replay matches the archived action and crossing intervals at four radii per symmetry section. All 16 directed traces reach 391/64 geometric radians. A separate regeneration of the 20 earlier quadrature cases matches the committed Lean sources byte-for-byte.

### 24 November 2026 — physical entries, frame chains and a first reference defect (N-64)

For a single nested Q-16 torus pair every endpoint has a physical entry on a nonzero phase interval. The angular packet covers both physical clocks through 391/64 radians. All 16 scalar chains and their actual start identifiers passed Lean. One forward slab has a kernel-checked physical reference defect within its recorded bound. The one-sided Jacobian bound and the full physical chain remain open.

### 24 November 2026 — first physical moving-frame passage from a Q-16 birth (N-65)

At section zero and u=0.470, a launched physical state from a sub-sector of half-width 2⁻¹⁹ enters the first forward moving tube. Lean proves that its true solution stays within 1.23 × 10⁻⁶ of the prescribed reference on [0,1/64]. The regular field has the actual sparse Jacobian, with its transformed quadratic form bounded by 0.0201. Two other physical reference defects and a 6,256-row exact feasibility screen also passed.

### 24 November 2026 — every Jacobian budget passes the sparse screen (N-66)

An exact sparse field calculation passes all 6,256 moving-tube Jacobian budgets, using up to eight time intervals and 4 × 4 spatial boxes. The physical long-trace theorem now takes only the per-row analytic bounds on those trial balls and the checked scalar chain. Its output starts at the actual section state reached by the Q-16 birth. A cache rechecks the emitted central defect theorems with bounded Lean workers.

### 24 November 2026 — one true trajectory through two consecutive frames (N-67)

The physical exit of the first frame supplies the second initial value. For births near phase zero at u=0.470 the true forward solution reaches 1/32 radian, with dimensionless Euclidean error at most 1.232 × 10⁻⁶ across the join. The second slab uses the actual inherited frame and a transformed Jacobian bound of 0.02022225.

### 24 November 2026 — one physical trajectory through sixteen forward frames (N-68)

At u=0.470 the actual section state of each Q-16 birth with |φ| ≤ 2⁻¹⁹ initiates a forward trajectory with uniform Euclidean reference error below 1.344 × 10⁻⁶ through 1/4 radian. A separate proof gives a single signed-angle trajectory through [−1/64,1/64] and uses the physical field reflection to check the backward Jacobian.

### 24 November 2026 — C1–C5 and geometric research priorities (N-69)

The assessment records C1 and vacuum C4 on the same Dommaschk field. It identifies well continuation and quantitative action control for thermal C2, obstructions to smooth pressure deformation for C4, and whole-interface energy estimates for C3. The thermal operating targets remain open.

### 24 November 2026 — signed four-slab passage and 24 consecutive forward slabs (N-70)

For births near section zero at radius 0.470, the physical forward trajectory reaches 3/8 radian with dimensionless reference error below 1.452 × 10⁻⁶. The signed four-slab theorem bounds one trajectory on [−1/32,1/32] within 1.232 × 10⁻⁶. The second backward step reuses the forward spatial bound through a checked ellipsoid projection. All 1,564 section-zero projection tests reproduce in exact arithmetic.

The 32-slab replay subsequently reached 1/2 radian. The exact uniform error bound is 1960457298773104133/2⁸⁰, below 1.622 × 10⁻⁶. The four generated theorems passed the standard-axiom audit.

The completed Jacobian batch covered rows 17–41. Its 75 theorem audits passed. The connected physical trajectory from the same birth now reaches 21/32 radian across 42 forward slabs with dimensionless Euclidean error below 1.817 × 10⁻⁶. Both mirror passage and thermal guiding-centre confinement remain open.

### 24 November 2026 — one radian forward and 64 slabs on either side of one birth (N-71)

The verified Q-16 trace at u=0.470 reaches one radian forward. The signed result uses a single transferred state across [−1,1]. A tighter rate on eight time intervals closed backward row 42. The 391 forward and 391 backward central residuals all passed. A separate exact screen identifies 387 projected row pairs passing without subdivision, three requiring time panels, and one requiring an additional vertical split.

### 24 November 2026 — a sharp geometric estimate for the bounce action (N-72)

The default library identifies the trace action with integration against arclength. A discrepancy ε between the sublevel lengths changes the action by at most ε√(2(h−b₀)). Flat wells attain equality. Field-line-label Lipschitz bounds give an action derivative estimate at points of differentiability. No physical thermal operating point enters this result.

### 24 November 2026 — finite field-strength thresholds for the action (N-73)

Lean bounds the action difference by the nodal discrepancy times the speed range plus the mesh times the reference length drop. Two flat profiles show why the mesh term matters. A separate exact screen at all eight local-action endpoints retained the archived comparisons on 253–433 adaptive speed intervals.

### 24 November 2026 — physically verified projected Jacobians (N-74)

At section zero and radius 0.470 the joined forward trajectory reaches 9/8 radian with uniform dimensionless error below 2.214 × 10⁻⁶. Row 68 uses time panels on the original square, and rows 69–71 use the actual coordinate projections of the trial ellipsoid.

### 24 November 2026 — signed field line through projected boxes (N-75)

A reflected rectangle lemma transfers the backward trial ellipsoid into the forward Jacobian domain. Lean verifies a single field line through the section on [−9/8,9/8], with uniform dimensionless position error below 2.214 × 10⁻⁶.

### 24 November 2026 — three signed radians and a spatial split (N-76)

At section zero and radius 0.470 the field line reaches ±3/2 radians with error below 2.216 × 10⁻⁶. Lean verifies both physical directions of slab 226 separately, using two vertical half-boxes on the same physical clock.

### 24 November 2026 — physical level contact at both proposed mirror heights (N-77)

Eight endpoint signs give four theorems for the physical field line from any admissible local entry: lower and upper heights in rows 316 and 324, each in the forward and backward clock. The general prefix theorem identifies the earliest level contact once every earlier tube is certified below the height.

### 24 November 2026 — exact adaptive-grid target arithmetic (N-78)

Lean verifies all eight adaptive tables. For each, the endpoint theorem gives a strict comparison with the N-60 action target under directed arclength bounds at the sampled field strengths.

### 24 November 2026 — exclude earlier mirror heights along the signed birth trajectory (N-79)

One Q-16-launched field line stays strictly below the lower height at every signed angle in [−3/2,3/2]. The 192 tube bounds and the ODE hold on the same path. Separate conditional results locate both earliest hits once the trajectory and sublevel estimates reach the brackets.

### 24 November 2026 — time panels bound sublevel arclength (N-80)

The default library now derives arclength tails from a measured partition or from the existing directed quadrature cover. At radii 0.470 and 0.478, complete packet reductions verify an upper and a lower threshold with substantial mass at equality.

### 24 November 2026 — quantitative transverse contacts and four signed radians of exclusion (N-81)

The outward derivative of squared field strength exceeds 1/128 and 1/400 throughout the interiors of the lower and upper brackets respectively. Each local physical crossing is unique. The signed birth trajectory now stays below both heights at every angle in [−2,2].

### 24 November 2026 — complete packet-to-sublevel binding at eight endpoints (N-82)

Each packet is scanned once into a verified threshold tree. Lean derives all adaptive node inequalities and the eight strict one-passage action targets from the original time-panel coverage assumptions, across 250,848 packed time cells.

### 24 November 2026 — both directed reference defects at eight launches (N-83)

Lean checks the initial ODE residual against the archived moving-frame budget at every launch. The opposite section now has a reusable physical harmonic shift. Same-centre Hessian transfer passed 176 of 176 external samples, while a neighbouring centre passed 32 of 88. Retain launch-specific projected Jacobians and use same-centre transfer as a fallback.

### 24 November 2026 — strict signs up to both mirrors and stability of measured wells (N-84, N-85)

All 648 directed signs for the phase-zero, radius-0.470 tubes are kernel-checked and assembled on the correct frames. Connecting the launch through the end of each bracket remains the propagation task. In parallel, a candidate-independent result gives a sharp square-root action estimate for arbitrary measured wells, a linear estimate from small band masses and a quantitative bound on perturbed root locations.

### 24 November 2026 — physical action panels and a regular mirror collar (N-86, N-87)

Two original panels adjacent to the launch hold on one Q-16 field line. The earliest archive panel holds on each admissible local solution of backward row 324, including the same solution’s mirror hit. Extend these panel proofs to whole slabs. For action perturbations across labels, N-87 permits flat or critical well bottoms: it needs short-band mass only near the mirror height.

### 24 November 2026 — action comparison across changing arclength measures (N-88)

The fixed-density estimates now extend to two field lines in a common angle parameter. The cost is the maximum clipped speed times the L¹ change of arclength density. The coefficient is sharp. Bounding the two physical rates remains open.

### 24 November 2026 — five-radian physical trajectory from a Q-16 birth (N-89)

The 160 signed slabs per direction give one physical trajectory with the same maximum position-error numerator as the 128-slab proof. Both strict mirror-height estimates hold throughout this signed interval. The remaining birth-to-contact work uses the already checked full pre-mirror signs.

### 24 November 2026 — complete action cover on both launch-adjacent blocks (N-90)

A compensated sparse polynomial and five radial pieces prove common column bounds across 96 consecutive panels. Both original blocks hold on the same physical birth path. The arclength density equals the norm of the actual Cartesian derivative, including at the two outer panel edges. External seven-channel Horner replay reproduces all 31,200 original 72-bit cells at this endpoint, while subdividing sparse field bounds succeeds on 168 of 325 signed pairs. Verify the native harmonic identities and their connection to the physical field on a difficult slab, then scale that proof.

### 25 November 2026 — both original moving tubes at every launch (N-91)

`DommaschkSignedLaunchesAll.launches` constructs a field line on [−1/64,1/64] through each admissible birth’s section state on one shared pair of nested tori. Five launches use enlarged spatial rectangles to accommodate the reflected backward reference. The signed family passed the kernel axiom audit.

### 25 November 2026 — a six-radian signed path, physical partial action and geometric sensitivity (N-92, N-93)

The same path supports strict submirror signs on [−3,3] and integrable physical action below 0.005587 across its central 96 panels. `CylindricalActionSensitivity.physical_action_window` bounds the geometric part of the action change for two differentiated curves. Concentric circles attain its coefficient.

### 25 November 2026 — exact native arithmetic for the physical action panels (N-94)

Ground Lean output recovers the original squared-speed, speed and density columns throughout both signed tubes at outward row 16. Reflection with the larger outgoing radius preserves all three digits externally across all 31,200 cells. Lean proves the signed-pair model on pilot rows.

### 25 November 2026 — four first mirrors, one-way physical action and arclength births (N-95–N-97)

Every admitted u=0.470 Q-16 birth satisfies `RegularMirrorBirth` at both pilot heights, on a common physical signed trajectory. The first contacts are in rows 316 and 324 in both directions. At the upper height, action between the true mirrors exceeds 553/2000. The signed path covers at least 325 rows each way with position error below 3.327 × 10⁻⁶. The original birth angle lies in the same connected well by uniqueness of the physical approach.

### 25 November 2026 — finite one-way flight times (N-98)

At u=0.470 the integral of inverse parallel speed against physical arclength is finite and strictly positive between the first mirrors at each archived height. The reusable theorem needs regular crossings at the endpoints and continuity in the well. Its application uses the same signed trajectory for both heights. Quantitative times and their conversion to seconds remain open.

### 25 November 2026 — a continuum of physical first mirror wells (N-99)

The closed height interval between the two archived energies now consists entirely of regular mirror births for each admitted QA2R pilot angle. On nine consecutive slabs the derivative of squared strength in each outward direction exceeds 1/400, including at every seam. This controls the first mirror positions uniformly and identifies the moving-endpoint action with a fixed-window integral. The action is continuous and strictly increasing, and the time between the two first mirrors is finite and positive at every height.

### 25 November 2026 — open transverse wells and a pilot parameter area (N-100)

A compact projection proves openness of the transverse mirror test in label and height, with a positive-measure consequence on a physical chart. A smooth counterexample shows uniform accuracy of field strengths alone can reverse the crossing orientation. At fixed QA2R radial label 47/100 and launch poloidal parameter zero, Lean proves an entire measurable rectangle of regular mirror births of area 1292367655761/655360000000000000000 in angle-height coordinates. The thermal birth fraction remains open.

### 25 November 2026 — continuing nonpilot field lines at both sections (N-102)

All admissible births at u=0.478 near zero and u=0.456 near π/2 now follow the true signed field for 1/32 radian on each side after returning to the section. Each comparison with the pilot uses one common pair of nested tori. The reusable step connects the outgoing frame to the next entrance and accounts for both reflected centres at the second section.

### 25 November 2026 — numerical time between the true first mirrors (N-103)

At every admitted pilot angle the dimensionless one-way flight time exceeds 237/40 for every height in the band and is below 34000 throughout its upper half. The upper estimate uses a core speed gap and an integrable inverse-square-root bound at each moving mirror. The same phase proves the arclength inequality L² ≤ JT for length, action and elapsed flight time. Dimensional inputs and a radial-drift estimate remain open.

### 25 November 2026 — shared physical Jacobians for four signed branches (N-105)

A single seven-harmonic evaluation of the three field polynomials and their six spatial derivatives proves the second signed row for both u=0.523 and u=0.531. Each launch retains its own state, error bound and moving frame. Checking both radial labels together took 231.7 seconds after reusable initialization, versus 517.0 seconds for one label by the previous method on that row. The separate u=0.478 trajectory now extends 1/16 radian each way.

### 25 November 2026 — action changes equal integrated flight times (N-104)

The QA2R pilot first-well action has the actual one-way flight time as its height derivative throughout the certified band. On every subinterval the action difference equals the height integral of flight time. At the endpoints Lean differentiates the ambient clipped action. The reusable compact-window theorem yields absolute continuity and an almost-everywhere derivative under continuity of field strength and density. The flat-bottom example verifies that differentiability can fail at a critical height.

### 25 November 2026 — distinct signed frame bounds at the opposite section (N-107)

The first q1r456 witness with unequal reflected frames differs by one integer tick. Four frame-specific Jacobian proofs for the q1r456 and q1r464 pair share one physical field evaluation. Lean checks the actual q1r456 backward ODE step on row 129 for every predecessor ellipsoid entry. Reaching that row from the birth remains a separate chain obligation. The full 6,256-case exact external matrix screen succeeds.

### 25 November 2026 — global toroidal field lower bound and sharper flight times (N-106)

Ten spatial rectangles certify Bφ > 7/8 at every toroidal angle in the pilot region. The exact field at R=1, φ=π/2, z=0 is 0.9550840988, which also rules out a uniform lower bound of one. N-106 uses the new geometric bound to prove T > 14 throughout the admitted band and T < 592 on its upper half.

### 25 November 2026 — a numerical flight-time interval at every pilot height (N-108)

The central field strength stays below the lowest archive height by 1/270000 throughout the 316-slab core on each side. The two outer transverse collars add less than 40 to the central flight-time integral. The physical ground theorem bounds one-way time between 14 and 4450 on the closed band, including the lower endpoint.

### 25 November 2026 — verified defect reflection at the second radial label (N-111)

The phase-zero u=0.478 trace now reaches six signed slabs each way through the same pair of Q-16 tori. For row four, Lean reuses the forward physical defect with its sharpened enclosure and authenticates the backward row’s own budget. The all-391-row exact arithmetic screen finds sufficient margin on each corresponding backward row.

### 25 November 2026 — sharper flight time at every pilot height (N-109)

The 316 integer reciprocal-speed ceilings sum to 5916 on each signed core. With the arclength weight this puts the central time below 223.986. The common-birth theorem gives 14 < T < 264 at every height, including both endpoints, on each admitted physical line.

### 25 November 2026 — the full signed 391-slab pilot trajectory (N-110)

Both complete 391-slab physical chains share the section state and the actual interpolated off-section birth. Their Euclidean position error relative to every indexed reference is below 3.327 × 10⁻⁶ in model coordinates. The same full path carries the four first transverse contacts at the two archived heights. A fresh compilation reproduced the joined proof.

### 25 November 2026 — regular births in an open Cartesian position-height neighborhood (N-112)

One locally smooth physical field-line window with strict caps and transverse contacts gives an open neighborhood of true regular arclength births. Smooth cutoffs on the compact orbit and Picard–Lindelöf supply the neighboring trajectories. The local positive-mass theorem applies without a prescribed family of trajectories.

### 25 November 2026 — action as a coordinate on the physical pilot height interval (N-113)

For every admitted pilot birth, the attainable actions fill the interval between the two endpoint actions. The height change for an action increment ΔJ>0 lies between ΔJ/264 and ΔJ/14. Across the whole band the action increases by strictly between 0.0072372588722616 and 0.1364740244483616.

### 25 November 2026 — first complete physical action comparison (N-101)

At the phase-zero u=0.470 pilot, the one-way action between the true first upper mirrors lies strictly above 553/2000 and at most 1146552112157123/844424930131968. The upper limit is below the specified action level by more than 0.00213. Lean checks the Cartesian density and clipped speed on all 31,200 panels of the original archive and combines them with both first-contact proofs on the same Q-16 field line. The other seven endpoint comparisons still require physical proofs.

### 25 November 2026 — the QA2R regular-birth set has positive Cartesian volume (N-114)

The Cartesian angular velocity field is smooth on the off-axis region of positive angular component. A strict transverse window on each real N-99 trajectory supplies the N-112 hypothesis. Every admitted pilot point is therefore interior in position and height, including at the lower and upper archived heights.

### 25 November 2026 — a five-dimensional trapped reference population (N-117)

For every admitted pilot position and height, any positive mass and positive energy determine the two lifts with opposite parallel velocities and magnetic moment equal to energy divided by mirror height. Both are interior points of the actual reference contract for cuts whose interiors contain them. Every open-positive birth law gives the resulting signed sets positive mass.

### 25 November 2026 — first variation across mirror field-line labels (N-118)

A fixed-base secant estimate for the signed weighted gap allows differentiation through moving transverse mirrors. The change of arclength contributes the integral of parallel speed times the change of arclength density. The change of strength contributes with opposite sign and inverse-speed weight. This gives a separate mathematical target for transverse label variation in C2.

### 25 November 2026 — action and both flight bounds on the same first well (N-116)

Restricting a certified path preserves its pointwise solution and its final exit ellipsoids. The 326-slab upper action certificate and all 316 central flight budgets therefore apply to the identical moving first-mirror pair. The all-height time interval is (54.98668,264), with a sharper lower bound of 57.80606 at the upper endpoint.

### 25 November 2026 — physical mirror brackets on the u=0.478 tubes (N-115)

Five signed endpoint tests give strict opposite signs across each candidate mirror bracket on both directions. Three closed-slab gradient certificates give positive outgoing squared-strength slope above 1/400. The next phase must attach these rows to the actual secondary birth over the complete incoming interval.

### 25 November 2026 — faster signed residuals on the secondary trace (N-119)

At q0r478 the paired central defect on row 4 takes 66.50 seconds with the native harmonic method, compared with 166.95 seconds for sparse forward plus reflected backward. The exact all-row feasibility test passes 391 rows. The physical campaign switched after its previous workers finished. Opposite-section campaigns use separate numerical certificates for the two signed frames.

### 25 November 2026 — signed sensitivity targets for radial action growth (N-123)

The signed first-variation lower bound is kT−AJ. Using the exact N-116 pilot estimates, a relative arclength lower bound of −1/32 and a strength-derivative upper bound of −1/144 would give radial action slope above 1/3. The 512- and 2048-step variational screens satisfy these inequalities at both pilot labels. Rigorous radial-derivative certificates remain open.

### 25 November 2026 — eight signed paths on common nested tori (N-120)

The section-zero paths cover 391, 48, 16 and 5 slabs each way. The opposite-section paths cover 12, 5, 5 and 5. A clean-cache replay with reordered inputs reproduced the same theorem for all 974 signed slabs. The shorter paths still need sufficient propagation to reach their first turning levels. [Durations, ground theorem and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/eight-signed-traces-on-common-tori.md)

### 25 November 2026 — vacuum guiding-centre solutions for both trapped populations (N-122)

At nonzero vacuum points the Littlejohn parallel field equals the field strength for all parallel velocities. Smoothness and local ODE existence yield true guiding-centre trajectories on positive closed time intervals. Each signed QA2R reference population contains an open set of such births for every compatible mass, charge, energy and choice of cuts. A common application-scale horizon, a numerical fraction and radial transport remain open. [Vacuum identity, pilot theorem and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/vacuum-local-littlejohn-births.md)

### 25 November 2026 — continuous submirror exclusion at u=0.478 (N-121)

Twenty whole-tube groups and a radial split of the final row verify the strict sign on the entire closed incoming interval in both directions. Exact coefficient inclusions match each original slab to its group. The signed birth trajectory already stays inside these tubes through one radian each way. [Ground theorems and exact group keys](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-qa2r-submirror-exclusion.md)

### 25 November 2026 — a common local excursion bound on both signed populations (N-125)

N-125 augments the Littlejohn system with constant magnetic moment. Nearby solutions of both signs obey any prescribed positive displacement cap for one common positive time. For a preselected compatible finite measurable reference and a law charging open sets, their union has positive covered fraction and meets the guiding-centre radial-band contract for any nonempty compact axis. Neither the time nor that fraction has a numerical lower bound. [Assumptions, quantifiers and grounded replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/common-local-littlejohn-time.md)

### 25 November 2026 — finite two-line action tests from a shifted pilot height (N-126)

On the joint pilot the action width exceeds 0.0284 and the inverse height modulus is at most the reciprocal of the N-116 flight-time floor. A finite height shift gives a lower action difference > 1/375 for the original radial pair if their field and density comparisons hold. Exact rational screening of the original tubes passes all 325 pairs after enclosing the spatial field gradients. [Grounded calibration, comparison hypotheses and screen](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/finite-radial-action-comparison.md)

### 25 November 2026 — signed observable derivatives at the true pilot birth (N-124)

The same two embedded Q-16 tori with all eight signed traces give the exact affine radial tangent at the section-zero pilot. Nine original checked spatial Taylor models give the two signed derivative bounds there. Transporting that tangent to the first mirrors is the additional ODE problem. [Ground theorem, arithmetic and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/pilot-radial-birth-variation.md)

### 25 November 2026 — secondary mirror roots and their response to height (N-127)

The 20 closed signed outer tubes pass the squared-strength slope test. Combined with the 634 inner tubes and the two exterior caps, this locates and separates the first roots at every height for any joined physical trajectory that reaches past 327/64. Both endpoint displacements lie between 7/64 and 10/64. The inverse derivative at interior heights is positive and below 800h. [All ten slope receipts and exact conditional attachments](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-first-mirror-height-band.md)

### 25 November 2026 — the calibrated pilot on the common endpoint geometry (N-130)

The complete first-well action and time proof now works on every admissible original 326-row pilot path. Restriction of the 391-row trajectory from the common embedded pair gives this calibration at all pilot angles, together with the seven neighboring sectors on the very same surfaces. The snapshot has 1,046 signed slabs. [Common-witness theorem and independent replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/common-torus-pilot-action.md)

### 25 November 2026 — paired launch profiles on the two true field lines (N-128)

At u=0.470 and 0.478, the first pair of signed physical tubes passes both finite-comparison inequalities at every common angle in [−1/64,1/64]. The through-birth theorem names both embedded tori, identifies the original launch at each admitted angle, and expresses the arclength comparison using the two actual Cartesian derivative norms in the interior. [Bounds and two ground packages](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/paired-physical-launch-profiles.md)

### 25 November 2026 — actual submirror paths at the two outer phase-zero radii (N-131)

At u=0.523 Lean proves the strict lower-height exclusion through ±1/2 radian, and at u=0.531 through ±5/64. One common embedded-torus family includes both results and the u=0.478 segment through ±1 radian, for every admitted birth angle. [Three witnesses, quantitative intervals and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/outer-phase-zero-submirror-births.md)

### 25 November 2026 — paired squared field strength near the pilot upper mirror (N-129)

The row with the smallest external margin now passes in Lean in both directions. On the original tubes at equal angle the inner squared strength exceeds the outer one by at least 17/144000. The two centers use the same geometric clock, and a spatial mean-value estimate covers the two independent position errors. [Reusable theorem, two-tube proof and reproduction](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/centered-strength-separation.md)

### 25 November 2026 — physical mirror exclusion at all four opposite-section births (N-133)

A single shared field calculation certifies 128 original tubes at the opposite section. At every admitted birth angle, the true lines on the calibrated embedded pair stay below the lower mirror height through ±1/4 radian at 0.456 and ±5/64 radian at 0.464, 0.509 and 0.517. [Opposite-section theorem and reproduction](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-section-submirror-births.md)

### 25 November 2026 — arclength and strength on paired physical tubes (N-132)

A common-angle polynomial estimate clears both field ceilings and the arclength ratio at the sparse screen’s weakest index, 296. At 324 the two signed proofs and N-129 also give the full field drop of 1/18000. Native action models pass the complete direct external comparison on the first 236 rows and the arclength test on all 325. [Physical arclength and field comparison](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/paired-physical-arclength.md)

### 25 November 2026 — lower action at the second phase-zero birth (N-134)

At u=0.478 the central 322 slabs in each direction suffice for the upper-height target by an exact dimensionless margin exceeding 0.00015632. The inner 321 miss it. All 31,392 archived cells agree with the independent arithmetic replay. Lean checks four physical row pairs including 192 original panels on the same signed birth line. [Lower action proof and complete scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-native-lower-action-cells.md)

### 25 November 2026 — paired observables on continuous signed birth lines (N-136)

The two actual physical lines satisfy the field drop and arclength ratio throughout ±5/16 radian for every admitted launch angle. The inner line retains its full first-well calibration. On this common family, the eight signed lengths total 1,238 slabs. A generic theorem transfers contiguous row pairs to the two enclosed paths and certifies that 325 pairs each way suffice for the first-well action comparison. [Two physical lines and the complete-well test](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/compared-signed-trace-prefixes.md)

### 25 November 2026 — quantified incoming mirror clearance (N-135)

All 634 incoming 0.478 tubes satisfy the strict bound below the lower height by 1/270000. On one pair of embedded tori, the actual birth lines at 0.478, 0.523 and 0.531 have verified clearances of 1/270000, 1/100000 and 1/50000 through ±2, ±3/4 and ±5/64 radians respectively. An independent harmonic estimate checks the last six incoming rows at 0.523. [Quantified signed mirror clearances](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/quantified-grouped-mirror-clearance.md)

### 25 November 2026 — groupwise spatial gradients for paired profiles (N-137)

The final six slabs and the first sixteen indices of the difficult suffix meet the two cross-line inequalities on both physical tube directions. The least-favorable group, indices 319–324, still has a strictly positive centered strength margin. A mixed block also joins five grouped rows to the independent last-slab certificate. [Grouped physical profile comparisons](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/grouped-paired-physical-profiles.md)

### 25 November 2026 — a continuous physical lower-action integral on the second birth (N-138)

Across ±1/4 radian, the actual upper-height action contribution at u=0.478 is at least 151485803144663/1688849860263936. The proof uses the Cartesian arclength derivative throughout 1,536 contiguous original panels. Lean has also checked the full first-well implication whose two outstanding inputs are the continuous 322-pair cover and the 328-row birth passage. [Physical lower-action integral and first-well theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-action-cover-from-birth.md)

### 25 November 2026 — the actual second birth stays submirror through ±2.5 radians (N-141)

The 317-pair clearance proof now transfers to the complete 160-pair signed trajectory from every admitted birth at u=0.478. The field stays strictly below the lower height minus 1/270000, and the theorem retains the actual ODE and both exit enclosures. A projection can also retain a longer physical path with a shorter observation. [Prefix projection and signed 160-row receipt](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/submirror-prefix-projection.md)

### 25 November 2026 — eight smaller action packets and four minimal symmetric windows (N-139)

All eight numerical signs survive with twelve independently enclosed panels per signed slab at six labels and sixteen at two labels. Lean verified every signed mass and each conditional endpoint action comparison. In the original lower archives the first sufficient symmetric counts are 322, 321, 325 and 323 at radii 0.478, 0.531, 0.464 and 0.517. [Eight exact action packets and minimal lower windows](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/eight-action-resolutions.md)

### 25 November 2026 — the lower action persists on a height interval at the second birth (N-142)

At u=0.478, shifting the exact squared-speed bounds extends the lower packet to heights as far as 267/2²⁷ below the upper height. Its full-core margin exceeds 3.17 × 10⁻⁷, conditional on the physical cover and first mirrors. On the actual signed birth line, Lean proves a uniform lower integral over ±1/2 radian from 3,072 original panels. [A positive height interval for the second launch’s lower action](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-action-height-window.md)

### 25 November 2026 — both physical profiles compared across the entire outer suffix (N-143)

Lean now compares field strength and arclength density at radii 0.470 and 0.478 across all 89 difficult outer slabs in each direction, for every angle from 59/16 to 325/64 and its reflection. Completion of the initial comparison and extension of the second birth trajectory will connect this result to both first wells. [The ordered paired comparison on the outer 89 signed slabs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/ordered-paired-profile-suffix.md)

### 25 November 2026 — a first-well secant from two signed field lines (N-144)

At radial labels 0.470 and 0.478 the two physical field lines from the common embedded tori meet both pointwise comparisons throughout ±1 radian. Lean now reduces a same-height first-well action difference greater than 1/375, corresponding to a radial secant greater than 1/3, to completion of the signed 328-slab outer trajectory and the 325 paired physical comparisons. [A finite radial secant between the first wells on two field lines](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/paired-first-well-actions.md)

### 25 November 2026 — physical coarse action cells at all four opposite-section births (N-140)

For every admitted angle near π/2, one embedded pair of QA2R tori supports the four signed launch trajectories. Lean uses 96 independently enclosed intervals to establish all 384 chronological action cells over the central ±1/64 radian. The physical field on each clock uses its own position tube and directed rounding. [Physical coarse action panels at the opposite QA2R section](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-section-coarse-action-cells.md)

### 25 November 2026 — a near-upper action floor greater than 8/25 on the actual signed line (N-145)

On the second physical field line, the Cartesian action integrated over ±3 radians exceeds 8/25 at every height in the near-upper interval. Its first mirrors, once reached by the trajectory, are less than 1/512 radian from the upper-height mirrors on both signed branches. The same-path lower bound between them then exceeds 43/100. [First-mirror locations and a strict action floor near the upper height](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-near-upper-first-wells.md)

### 25 November 2026 — a physical 16-panel route to the second-radius upper-height target (N-148)

At radius 0.478, one reflected set of 16 physical enclosures covers 96 chronological cells across the launch. Lean also checks that the corresponding coarse core of 325 row pairs would exceed the action target by 0.00022923 between the first upper-height mirrors. Original lower cells can feed this cover directly. [Sixteen-panel physical action bounds at the second phase-zero launch](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/second-phase-zero-coarse-action.md)

### 25 November 2026 — a compact arc of regular mirror births on the physical pilot (N-147)

On the physical pilot at radius 0.470, one positive metric radius about the entire Cartesian arc through ±316/64 radians times the closed height band stays inside the regular-birth set. Every point on this arc admits open trapped populations of both velocity signs and local guiding-centre control under compatible cuts. For radius 0.478 the analogous result through ±317/64 follows from its pending signed first-mirror passage. [An open Cartesian tube of regular births about a complete central field-line arc](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/compact-regular-birth-arcs.md)

### 25 November 2026 — the complete two-radius profile comparison (N-146)

On all 325 angular slabs in each direction, the outer field strength at u=0.478 falls at least 1/18000 below the inner field strength at u=0.470, and the outer arclength density is at least 3999/4000 of the inner density. The 650 comparisons cover every point of the original matched tubes. Applying the full interval to actual first wells requires the second birth trajectory to reach its mirror brackets. [Full signed field-profile comparison at the two radial launches](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/full-paired-physical-profiles.md)

### 25 November 2026 — one guiding-centre time for the entire lifted pilot arc (N-150)

For every accepted pilot birth and compatible closed energy interval, a single positive local time works on the whole central field-line arc through ±316/64, across the full mirror-height band and on both parallel-velocity signs. The open controlled set contains a closed five-dimensional neighborhood of positive radius around this compact family. The proof also applies to arbitrary compact families in a regular vacuum field. A numerical time and a lower bound on the covered fraction remain open. [A shared guiding-centre time for a compact family of trapped births](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/compact-littlejohn-arc.md)

### 25 November 2026 — the two physical birth paths compared across seven radians (N-149)

At the same original birth angle the actual lines at u=0.470 and 0.478 satisfy the signed field and arclength inequalities throughout ±3.5 radians. Their calibrated family has 1,482 physical steps shared among eight endpoints on one pair of embedded tori. A 65-pair integral on the second birth exceeds 0.3568 at the upper height. Physical field clearance is also proved along 48 signed pairs at u=0.523 and twelve at u=0.531. [A 3.5-radian field comparison on two physical birth trajectories](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/compared-physical-birth-arcs.md)

### 25 November 2026 — sharing physical field derivatives across twelve original moving frames (N-152)

Four groups of twelve now supply every signed moving-frame Jacobian bound from row 280 through 327 at the second birth, and the original central residuals give both true local ODE steps at row 317. An identical-row replay took 184.743 seconds individually and 29.259 seconds with the shared field cost apportioned over twelve rows. The two proofs have the same mathematical bound. [A shared spatial Jacobian on consecutive physical trial tubes](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/grouped-moving-frame-jacobians.md)

### 25 November 2026 — one local guiding-centre time across every admitted pilot launch and arc (N-154)

A single positive time now serves the full central arcs of physical field lines through every allowed original pilot launch phase. The theorem covers both velocity signs, the whole mirror-height band and a chosen positive closed energy interval. It obtains the same time from a compact regular vacuum enclosure before the compatible support and pitch cuts are chosen. A numerical thermal time and transport estimate remain open. [A common guiding-centre time across all pilot launch phases and central arcs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/common-time-across-pilot-launches.md)

### 25 November 2026 — simultaneous field clearance at three original births on the calibrated tori (N-158)

On one embedded pair Lean proves strict lower-height field clearance at the three original secondary births through ±4, ±3/4 and ±1/4 radians, alongside the calibrated pilot. The actual inner and outer field lines now satisfy the paired field and arclength bounds throughout ±4 radians. At the outer birth the near-upper Cartesian action over that interval exceeds 47/125. [Field-strength margins on four physical births of one phase-zero torus family](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/common-original-birth-margins.md)

### 25 November 2026 — the signed continuation campaign for all remaining launches (N-157)

At the opposite section a common physical field calculation now feeds two independently checked moving frames. Both physical ODE steps on the nonconjugate row 129 at u=0.456 passed. Exact arithmetic proposes 171 shared groups for the six further trajectories (2,007 original indices); their full through-birth paths require the ensuing Lean replays. The resource-limited campaign has started following the 328-pair u=0.478 proof. [Independent signed moving frames on a shared group of physical slabs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/signed-moving-frames-beyond-mirror-caps.md)

### 25 November 2026 — the second physical first well exceeds the archived action target (N-156)

At the upper mirror height, 37 checked degree-seven polynomial lower bounds and 110 central slab pairs give a one-way Cartesian action of at least 1.3618404 at u=0.478. This exceeds the archived target by more than 0.0019182, while the pilot ceiling at u=0.470 lies below the same target. The second line has 328 signed slabs in each direction from its original birth. [Polynomial lower bounds for the second QA2R first-well action](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/second-first-well-polynomial-floors.md)

### 25 November 2026 — physical first-well secant through the second pair of mirror points (N-161)

The second original field line now extends 328 slabs each way, past both first mirrors. On the same embedded torus pair, the action change from u=0.470 to u=0.478 is greater than 1/375 and the radial secant exceeds 1/3 whenever h and h+1/18000 both lie in the archived height band. The common eight-launch family has 1,720 signed ODE steps. [Action variation between two physical QA2R first wells](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/two-physical-first-well-actions.md)

### 25 November 2026 — topology of first contact and a quantitative estimate on shallow mirrors (N-159)

A continuous capped profile has strictly increasing, left-continuous first-contact times. Differentiable profiles have transverse mirrors on both sides at almost every height. For the archived band and two brackets each at most 10/64 wide, the area formula gives more than half the heights with both outward physical slopes greater than 1/1250, conditional on the two profiles and their differentiability. [First mirror heights from topology and the area formula](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/first-mirrors-regular-values.md)

### 25 November 2026 — one local time on two physical radial birth families (N-160)

Lean checks one positive local guiding-centre time across both true central arcs, through ±316/64 at u=0.470 and ±317/64 at u=0.478, for every admitted phase, both velocity signs and the chosen height and energy intervals. The common time depends on the displacement cap and has no numerical lower bound yet. [One guiding-centre time for two radii and all launch phases](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/joint-regular-launch-arcs.md)

### 25 November 2026 — upper-height secant greater than one half on the same two field lines (N-162)

At h_U the action difference between the two original phase-zero births exceeds 1/250. The radial secant is at least 0.50624 at this endpoint. The pilot and outer actions lie on opposite sides of the archived target. Lean identifies the same two chosen physical trajectories in this estimate and in N-161. [Equal-height radial action secant at the upper mirror height](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/upper-height-radial-action-secant.md)

### 25 November 2026 — faster signed physical trajectory proofs on the opposite section (N-163)

On opposite-section slab 129 at u=0.456, both physical harmonic defect proofs took 120.51 seconds together against 373.02 seconds for the sparse calculation on the identical pair. The two original physical continuation steps passed. All 2,664 proposed signed residuals also fit their original allowances in exact external arithmetic. [Independent harmonic ODE residuals at the opposite section](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/independent-harmonic-central-defects.md)

### 25 November 2026 — all four opposite-section launches have checked mirror caps (N-153)

All 32 signed endpoint inequalities passed on the four original π/2 launch models. The resulting sixteen intermediate-value theorems give crossings for continuous physical paths through their paired cap tubes. Continuing the original field lines and excluding earlier roots remain necessary to identify these as their first mirrors. [Signed physical mirror brackets at the opposite section](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-section-physical-mirror-caps.md)

### 25 November 2026 — two more signed lower-height first-mirror branches conditional on passage (N-151)

For u=0.523 and u=0.531 the complete earlier field exclusion, signed cap tests and closed lower-bracket derivatives now imply simple first lower mirrors on both sides of a through-going trajectory. Lean places them in (322,324)/64 and (323,325)/64 radians. The actual continuations from the two original births are running. [First lower-height mirror brackets at two further phase-zero radii](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/lower-mirror-branches-at-two-more-radii.md)

### 25 November 2026 — all opposite-section incoming field signs up to their first mirror brackets (N-155)

Twenty-five shared harmonic enclosures verify all 2,586 signed incoming tubes at the four opposite-section launches. The common family attaches the strict field clearance to the certified physical prefixes at u=0.456, 0.464, 0.509 and 0.517. Their long signed ODE continuations are still in progress. [Field strength before the first mirror brackets at all four opposite-section launches](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/four-opposite-incoming-field-profiles.md)

### 25 November 2026 — first-well containment and action separation at every archived height (N-165)

Lean proves that at every height in the closed band the pilot first well lies in the neighboring first well. At u=0.478 the action exceeds the u=0.470 action by more than 2/625 and the radial secant exceeds 2/5. An affine lower bound on the square-root density uses the certified field drop and an exact arclength floor above 9.309. This includes the previously uncovered upper interval. [An equal-height action gap throughout the closed mirror-height band](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/closed-height-band-action-secant.md)

### 25 November 2026 — an actual first-mirror height budget from the geometry of two signed clocks (N-164)

At every admitted birth angle at u=0.478, the measure of heights at which both outward first-contact slopes exceed 1/1250 is at least 51.639% of the archived band. The proof uses positive toroidal field, smoothness, the incoming field signs and two exterior caps. The four opposite-section archived sign and smoothness checks also passed, leaving the signed through-going ODE paths as the sole missing finite input there. [First-mirror height measure on physical QA2R field lines](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/physical-first-mirror-values.md)

### 25 November 2026 — shared higher-order fields accelerate physical continuations at the other two phase-zero launches (N-166)

On six original q0r523 rows, a shared higher-order polynomial verifies twelve signed residuals in 199.813 seconds versus 465.098 seconds for the separate calculations. Both physical row-60 steps passed. The 675 paired rows at the two outer phase-zero launches fit 91 proposed groups in exact screening. The live campaign has accepted a grouped signed reference at row 96. [Grouped physical central defects for the phase-zero continuations](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/grouped-physical-central-defects.md)

### 25 November 2026 — continuation of a prescribed first-well action through a connected family (N-167)

In any continuous capped family, two first-well actions on opposite sides of a target force a parameter with that action or a first contact that is a local field maximum. The proof follows just the first contacts and tolerates later pockets. The physical attachment uses both original QA2R lines and all admitted birth angles, leaving the radial interpolation and its caps as explicit hypotheses. [A prescribed first-well action or a grazing first mirror](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/prescribed-first-well-action-or-grazing.md)

### 25 November 2026 — normalized probabilities of two steep first mirrors (N-168)

At u=0.478 the verified probability of two outward slopes above 1/1250 is at least 51.6391% under uniform height. A normalized law with density at most twice the uniform density on failed heights retains at least 3.27829%. Under the required through-passage, the opposite-section uniform bounds are 61.3113%, 61.3113%, 56.4752% and 51.6391%. These probabilities concern sampled heights on a selected line. [Sampling heights with two steep first mirrors](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/height-sampling-first-mirrors.md)

### 25 November 2026 — independent opposite-section groups accelerate the original signed ODE proofs (N-170)

For q1r456 rows 49–56, sixteen independent signed central defects took 380.668 seconds together, compared with 1,206.442 seconds on the same rows separately. The forward and backward physical row-49 ODE steps passed. The four live opposite-section campaigns are using their validated group plans. [Grouped independent ODE residuals on both clocks at the opposite section](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/grouped-opposite-section-ode-defects.md)

### 25 November 2026 — Physical launch and caps for the radial interval (N-169)

All four closed radial tiles between 0.470 and 0.478 now share certified launches on the original nested tori, including arbitrary birth phases of magnitude at most 2⁻¹⁹. The true field exceeds the upper mirror height on all eight signed cap tubes at 331/64. Exact screening covers 2,720 signed rows. Propagating the original launches through the tubes remains open. [Four physical entry balls and a common high cap for the upper radial bracket](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/upper-radial-ribbon-entry-and-caps.md)

### 25 November 2026 — Two-sided physical continuation across the action bracket (N-171)

The true field-line ODE now supplies continuity in launch radius and uniquely identifies both archived first-well actions even when their integration windows differ. The verified candidate theorem gives a prescribed action or a grazing first mirror once the radial trajectories reach both high caps. Nonzero derivative at the two first contacts excludes grazing. [Continuous field-line families across the upper action bracket](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-field-line-continuation.md)

### 25 November 2026 — Eight physical launches reach a common 1,998-slab checkpoint (N-174)

Six secondary launch intervals were replayed together with the 391- and 328-row physical lines. This adds 278 signed slabs since the 1,720-slab snapshot. The actual lower-height margin now holds through two radians in each direction at radius 0.523 and half a radian at 0.531. The opposite-section margins and all 325 paired field and arclength comparisons also compile against this snapshot. [Eight original launches on a common pair of tori through 1,998 signed slabs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/eight-launch-signed-checkpoint.md)

### 25 November 2026 — All four signed central inlet segments checked (N-173)

Lean verifies the first 64 central ODE defect inequalities across the four widened launch balls, including both clock directions. An exact group plan covers the 2,656 signed estimates needed through 332/64. Each accepted group exports individual physical theorems for composition with the spatial and scalar enclosures. [Central ODE defects for the continuous radial birth interval](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-ribbon-central-defects.md)

### 25 November 2026 — Prescribed-action births reduced to four section checks (N-176)

The candidate theorem now takes four section-ball checks as its sole remaining hypothesis. It recovers the original birth phase by ODE uniqueness, chooses paths across the whole radial interval and concludes an exact target action with two transverse first mirrors for each allowed phase. The signed field and ODE campaigns are verifying the inputs. [Four section checks suffice for an original birth at the prescribed action](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/four-section-prescribed-action-criterion.md)

### 25 November 2026 — All four radial launch balls propagate through sixteen steps each way (N-175)

Every point of the four section balls has a single true two-sided QA2R line through sixteen slabs each way. The original ODE holds with ordinary derivatives through the joins on the closed ±15/64 window. Lean also verifies the regular cylindrical domain on all 2,656 downstream tubes. Full through-cap propagation is running. [Two-sided physical field lines from four radial birth intervals](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-ribbon-through-chains.md)

### 25 November 2026 — Outward upper-height mirror orientation on all four radial intervals (N-172)

The outward angle derivative of squared field strength exceeds 1/16384 on all 112 signed mirror-collar tubes, including all possible upper-height contacts in the external screen. The first eight signed rows on each tile are below the mirror height. The full long-path and earlier-field attachments continue independently. [Outward orientation of both mirror collars across the radial bracket](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-ribbon-mirror-orientation.md)

### 25 November 2026 — Integer Taylor certificates accelerate physical row proofs (N-177)

On the same signed eight-slab group, integer Horner checking reduced complete proof time from 215.099 to 142.558 seconds with the same 1,081 Taylor models and sixteen original defect theorems. The analogous shared spatial field and gradient check improved from 171.807 to 90.873 seconds for identical outputs. New groups can use the faster route while earlier accepted proofs remain reusable. [Integer Horner certificates for rounded Taylor models](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/integer-horner-taylor-defects.md)

### 25 November 2026 — Compact prescribed-action level across phase and radius (N-178)

Continuous birth clocks and compact ODE enclosures now give joint continuity in launch phase, radial label and observation time. The first mirror positions and action remain continuous across simple first contacts. On the original embedded QA2R pair, the four section checks therefore imply a compact target-action set projecting onto the entire narrow phase sector. [A compact target-action set over launch phase and radius](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/compact-sector-first-well-actions.md)

### 25 November 2026 — Original births belong to the same low-field component as the section (N-179)

On one common pair of embedded tori, every radius from 0.470 to 0.478 and every allowed original launch angle has a true trajectory with field strictly below the upper height throughout ±1/8 radian. The same line solves the physical ODE on the closed ±15/64 window. A further uniqueness theorem transfers a section-centered first well to the original birth phase on any regular continuation. [The original radial births share an accessible interval around phase zero](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/accessible-radial-birth-window.md)

### 25 November 2026 — Full orientation and first-mirror proof on every proposed radial tube (N-181)

For each of the four tiles, a physical trajectory following the canonical 332 rows in each direction has two transverse first mirrors at the upper height. The kernel checked the entire incoming history, the full mirror collar and both exterior caps. The same proof exports the precise signs and nonzero first derivatives required for action continuation. [First-mirror signs on the four complete radial tube sequences](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-ribbon-through-cap-signs.md)

### 25 November 2026 — Connected action-level continuation on a rectangle (N-180)

Lean proves a finite-dimensional Browder continuation theorem and its rectangular level-crossing consequence. Opposite radial-face inequalities give a single compact connected set of target points meeting every phase. Strict signs keep it inside the open radial interval. This gives a topological criterion independent of root uniqueness or radial monotonicity. [A connected action level across a radial launch bracket](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/connected-rectangle-action-level.md)

### 25 November 2026 — Strict physical action signs on both radial faces (N-182)

The original endpoint action inequalities now transfer to any enclosed candidate family at every admitted launch phase. The same embedded tori carry the four-tile entries, the field-line continuation theorem and the two strictly opposite radial face signs needed to apply the connected-level result. [Strict endpoint actions on both radial faces of the phase sector](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-sector-face-actions.md)

### 25 November 2026 — Sector action attainment reduced to the long signed ODE solve (N-183)

The physical sector action proof now depends on a single family of long signed trajectory certificates. On the stated original QA2R packets the verifier checks every remaining sign, derivative, endpoint and continuity step against the kernel. The unconditional release consumes a complete through-trajectory receipt for these same four tiles. [The signed trajectories are the remaining input to physical radial action attainment](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-sector-through-trajectory-criterion.md)

### 25 November 2026 — Connected true birth-centered target wells across the radial sector (N-184)

The physical endpoint signs, actual birth positions, compact ODE family and Browder continuation theorem now compose. Once the four prescribed signed trajectories reach both caps, a single compact connected set of original births carries the exact target action and meets every phase in the sector. All its radii are uniformly interior, and the two mirror times are continuous. The through-going membership is the only remaining input. [A connected set of original births at the prescribed first-well action](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/connected-original-birth-action-level.md)

### 25 November 2026 — Faster signed spatial bounds with original moving frames (N-187)

The full 1,328-row-pair screen needs 2,417 rational time panels for the principal-minor checks. On the first eight pairs, exact integer frame arithmetic and adaptive panels reduced spatial verification from 44.678 to 24.592 seconds. All sixteen final physical ODE steps recompiled. A cross-radius transfer of the central defect still exceeds every original budget tested. [Integer frame arithmetic and smaller time covers for the radial family](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-ribbon-matrix-certificates.md)

### 25 November 2026 — A full-period action level meeting every boundary passage (N-185)

For any continuous action strictly bracketing the target on both radial faces throughout a periodic annulus, Lean proves that one compact connected target level meets every path between the faces. Its inclusion into the annulus is essential. The QA2R sector result supplies local data. Extending it around the circle requires global physical inputs. [A connected periodic action level separating the two boundary circles](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/connected-periodic-action-separator.md)

### 25 November 2026 — First mirrors and flight-time bounds over a closed height interval (N-186)

Lean checked two first mirrors over the interval from hU − 1/50000 to hU + 1/30000, conditional on the four long trajectories tracking their tubes. On that interval their angles vary Lipschitz continuously in height, and the one-way flight time measured using the Cartesian path derivative lies strictly between 14 and 10000 in normalized units. [Transverse first mirrors and physical flight times over a height band](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-ribbon-mirror-height-band.md)

### 25 November 2026 — Strict endpoint margins for a full interval of action prescriptions (N-188)

At the upper mirror height the two physical endpoint actions strictly bracket a closed interval of width 1/250. Any continuous phase-dependent target in that range therefore has one connected set of exact original births covering the sector, conditional on the long physical trajectories. [A common interval of prescribed actions across the original launch sector](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-sector-prescribed-action-band.md)

### 25 November 2026 — Another 592 signed physical slabs on the eight original launch labels (N-193)

The eight original launch families on one pair of nested embedded QA2R tori now have 2,590 signed physical slabs. All four opposite-section field exclusions hold on the longer physical paths. The six remaining endpoint traces continue toward their mirror brackets. [Eight original launches through 2,590 signed physical slabs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/eight-launch-signed-continuation.md)

### 25 November 2026 — Full-period obstruction to the narrow radial action bracket (N-190)

At the upper mirror height, seven directed-arithmetic cells on the opposite section put the true first-well action above the target by more than 3/2000 throughout radii 0.470–0.478. Lean verifies the covering argument and the exact numerical slack conditional on the physical cell floors. The wider 0.44–0.54 bracket remains a candidate for full-period verification. [The original radial action strip misses the target on the opposite section](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-section-excludes-pilot-action-strip.md)

### 25 November 2026 — Faster matrix verification for the six long signed endpoint continuations (N-189)

On twelve opposite-section rows, 24 independently signed matrices and their kernel checks took 224.699 seconds with the new verifier and 628.054 seconds on the same original inputs with the earlier verifier. All six endpoint labels passed their own pair of signed physical ODEs before using the optimized route. [Faster signed endpoint matrix certificates on the six original launches](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/fused-signed-endpoint-matrices.md)

### 25 November 2026 — Joint height and action prescriptions on the original launch sector (N-192)

For any continuous phase-dependent height within 10⁻⁷ of the upper reference and any continuous target in a common action interval of width 1/500, one compact connected set of actual birth parameters attains the prescriptions across the sector, once the four signed paths are verified. The physical identity dJ/dh = T gives the required adjustment of the endpoint action bounds. [A rectangle of prescribed heights and actions on the radial birth sector](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/height-action-rectangle.md)

### 25 November 2026 — A true nonturning passage for the full radial launch family (N-191)

All 1,024 signed ODE steps through row 128 on the four radial tiles are joined. Every original birth in the sector now has an ordinary ODE through ±127/64 and normalized parallel speed above 1/12 throughout ±59/32 for any height at or above the lower archived value. [A uniform parallel-speed floor along the original radial family](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-passing-speed-core.md)

### 25 November 2026 — Original births stay below both heights on two wide phase sectors (N-196)

On the same two nested embedded invariant tori, every original launch label between 0.44 and 0.54 has field strength below both archived mirror heights when the phase is within 1/32 radian of zero or π/2. This verifies the field at launch over 3.98% of a full field-strength period. First-well action along the corresponding trajectories is a separate input. [The original QA2R births lie below both mirror heights on two wide sectors](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/wide-original-birth-strength.md)

### 25 November 2026 — Quantitative normalized travel time on all original radial-sector trajectories (N-194)

Every original birth in the small sector and every archived mirror height has a continuous strictly increasing physical parallel clock on ±59/32. Every signed normalized time of size at most 966655/1048576 has a unique angular position there. The proof uses the Cartesian path derivative and the actual signed ODE. [A physical travel clock on the nonturning segment of each original birth](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/original-radial-passing-time.md)

### 25 November 2026 — A quantified physical endpoint action budget for radial exits (N-199)

On the completed pair of physical faces, all independent measurements of the birth-centered first-well actions lie strictly outside the closed interval of radius 19/10000 about the target. Lean applies this to a proposed motion with bounded action drift and a physical face measurement at a potential first exit. Verifying that drift for actual guiding centres remains open. [A measured action-drift budget for a first radial exit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/physical-face-action-exit.md)

### 25 November 2026 — 2.55 times as many physical row pairs at the same measured CPU use (N-197)

The workstation's balanced controller checked 224 genuine physical row pairs over eight minutes, compared with 88 over the earlier eight-minute interval. Both CPU samples used 7.97 cores for this campaign. Immutable chain segments now enter checking as soon as their local ODEs have passed. [Balancing the central and spatial proofs of the long radial trajectories](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/balanced-ribbon-defect-campaign.md)

### 25 November 2026 — An opposite-section action obstruction before the mirrors (N-195)

For the original quarter-turn inner radius 0.470, all 15,360 exact positive quadrature panels on the core through ±5 radians give a strict floor above the target by more than 3/10000. Lean checks the common original birth seed, four physical observable rows and the implication for a first well. The remaining physical covers on this new launch are explicit inputs. [A positive action core at the opposite-section inner birth](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-inner-action-subwell.md)

### 25 November 2026 — The original launch chart is accessible at every phase (N-198)

For every real phase and radial label from 0.44 through 0.54, the QA2R field strength at the original birth on one pair of nested embedded tori is strictly below the lower mirror height. Thirteen exact field groups and a periodic reduction on the Fourier chart prove the result in Lean. Full-period action bracketing and transport remain open. [Submirror strength at every original birth over the full QA2R field period](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/periodic-original-birth-strength.md)

### 25 November 2026 — The whole radial family through 1,920 signed physical slabs (N-200)

The four radial tiles now have 240 signed physical slabs in each direction. Every initial birth in the small sector has positive parallel speed through ±237/64 and a unique position for every signed normalized time of magnitude at most 1941503/1048576. [The full radial birth family through 240 slabs in both directions](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/radial-passing-240.md)

### 25 November 2026 — Uniform positive radial sampling mass for near-target first-well actions (N-201)

Every positive action tolerance admits a positive radial interval length uniformly over the QA2R sector, height sub-band and supported target values once the four long physical trajectories are verified. The theorem concerns uniform sampling of the radial launch label. A numerical lower bound follows from an explicit radial Lipschitz constant, which is still open for this candidate. [Uniform radial measure for approximate first-well action](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/uniform-radial-action-windows.md)

### 25 November 2026 — An unconditional variable-height action margin on the physical outer face (N-202)

On the completed original outer face, the derivative of the first-well action equals the Cartesian one-way flight time throughout the height band. The time is below 452 within 10⁻⁵ of the upper reference. The outer action therefore still exceeds the target throughout the last four millionths of height. [Flight time and action response on the completed outer radial face](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/outer-physical-face-flight.md)

### 25 November 2026 — Both signed ODE clocks and the first physical panels at the opposite inner radius (N-204)

At the original quarter-turn inner birth label 0.470 the two separate physical ODE steps and their 48 near-birth action panels now pass Lean on the same tori. A two-worker verifier resumes the remaining 320-row campaign after the primary four-tile join is accepted. All proposed central and spatial groups pass exact planning preflight. [An original opposite-section action trajectory and a resumable physical campaign](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-inner-physical-trace.md)

### 25 November 2026 — The four signed trajectories close the original first-well action theorem (N-205)

Lean has joined all 2,656 physical ODE steps and discharged the through-cap hypothesis. On one pair of original nested embedded QA2R tori, a jointly continuous three-parameter family has true birth-centered first mirrors, compact connected target-action levels spanning the small phase sector, and positive radial sampling mass at every positive action tolerance. The thermal confinement and full-period action goals remain open. [Connected first-well action levels on one actual QA2R radial sector](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/completed-original-radial-sector.md)

### 25 November 2026 — A true signed field-line interval around every birth over the whole period (N-203)

Across the full birth phase circle and all labels 0.44–0.54, Lean now proves a true QA2R field-line segment through ±1/256 radian, with strength below hL−1/1000. Each poloidal coordinate moves by at most 1/1536, and the Cartesian magnetic field-line equation holds on the interior. [A signed nonturning field-line collar for every original QA2R birth](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/periodic-original-fieldline-collar.md)

### 25 November 2026 — The first-exit test permits different mirror heights along a trajectory (N-206)

On the original two radial faces Lean certifies a closed first-exit budget of 249/250000 for every height from h_U−1/500000 to h_U. The measured action must come from an actual first well in the certified phase sector at a possible first exit. An independent bound on pre-exit action drift is still required for a particle confinement conclusion. [A radial first-exit bound with varying mirror height](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/varying-height-first-exit.md)

### 25 November 2026 — C1–C5 after completion of the local physical action sector (N-210)

The updated assessment puts the 2,656-step local first-well theorem, the all-phase short field-line collar and the conditional first-exit budget on the same C1–C5 map. The thermal C2 problem now has an explicit action-drift target. Finite-pressure structure, stability and thermal performance remain open. [Stellarator conditions after the first-well sector proof](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/stellarator-conditions-after-sector-closure.md)

### 25 November 2026 — Another physical line reaches two first mirrors throughout the height band (N-207)

For u=0.523 and every original birth phase within 2⁻¹⁹ of zero, the physical line reaches the section and has both first-mirror branches in 337 signed angular slabs per direction. Both mirror times are measured from that section. Their endpoint brackets and derivatives are verified. The numerical action of these wells is still open. [First mirror branches from the original phase-zero birth at 0.523](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/original-endpoint-first-mirror-continuations.md)

### 25 November 2026 — A compact action level can follow two moving radial faces (N-212)

Lean proves an angularly essential compact connected target-action set between continuous moving radial graphs with strict bracketing. A separate first-exit theorem handles physical paths between moving faces. For QA2R the global well family and face inequalities remain to be supplied. [Action levels between phase-dependent radial faces](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/phase-dependent-radial-faces.md)

### 25 November 2026 — Refresh audit of all changes since 23 November (AW-*)

Audited `0bec221`: 531 Lean files, the generated-module pipeline and 180 documents, with six independent read-only sub-audits. No false or vacuous theorem and no unsound checker in the repository. Three high findings: the headline QA2R C2 declarations are generated outside the repository and are not audited by its axiom scripts (AW-H1); they cannot be replayed from the repository (AW-H2); the band form of C2 admits a point-mass population with an existential horizon (AW-H3). README, progress, N-210, N-48 and the G-10 row were corrected; two missing copyright authors were added. Two user decisions are recorded in the audit. [Audit record](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-25-refresh-audit.md)

### 25 November 2026 — The band form of C2 with fixed inputs (N-213)

Patch to N-53 and the C2 band-form clause, from audit findings AW-H3, AW-M3 and AW-M4. A specification (`BandSpec`) fixes species, birth law, support, windows, axis, horizon, excursion and required fraction, all symbolic; `BandSpec.Admissible` requires an absolutely continuous birth law, a support with interior, a closed `C¹` axis and a positive fraction; `MeetsBand` requires a `C²` divergence-free field on a region containing every partial orbit and `GuidingCentreBand` with the specified inputs. `BandContract` is the band form of C2. Regressions reject the point-mass fixture and the non-Maxwell mirror field. The status of C2 is unchanged (open). [N-213](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/band-form-fixed-inputs.md)

### 25 November 2026 — The generated QA2R modules are in the repository build and axiom audit (AW-H1, AW-H2)

The 184 script-generated modules cited in the notes, with their import closure, are now the on-demand Lake library `QA2RGenerated`: 43,435 Lean sources, copied unchanged from the workstation caches and stored as 258 compressed archives with a SHA-256 manifest and the campaign receipts (`generated/qa2r/`). A cold `lake build` of all of them passed on the workstation (about 8.7 hours on 22 jobs; largest module 34 GB). The axiom audit, run once for each cited module because alternative versions declare the same names, found standard axioms only in 4,974,523 declarations and all 70,219 receipt theorems. One command replays this: `python3 scripts/qa2r/replay.py`. The statements are unchanged: they remain field-line results, and C2 is open. Generated modules that no note cites stay outside the repository and support no claim. [Sources and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/generated/qa2r/README.md)

### 26 November 2026 — Opposite-inner campaign closeout (N-204)

The existing 320-pair campaign and its queued independent-observation theorem have completed. All 15,360 panels lie on the same certified signed field line. At u=0.470 near π/2, any qualifying observation at the upper height has action strictly greater than the target plus 0.0003. The archive adds these two roots and their dependencies. [Exact statement and receipt keys](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/generated/qa2r/README.md#opposite-inner-campaign-closeout-26-november-2026)

### 26 November 2026 — Label drift of guiding centres and the scales of the QA2R sector (N-214)

Work on RG.5 item 2 (C2 on the actual field). Lean proves that a function constant on field lines changes along a Littlejohn orbit only through the cross-field drift (`LabelDrift.label_hasDerivAt`), gives the vacuum form of the rate (`rate_vacuum`), its bound by the energy (`abs_rate_vacuum_le`) and the direct first-order displacement bound (`label_displacement_le`); default build, standard axioms. An untrusted screen on the certified sector finds a banana excursion of about 25 ε and a precession of about 55 ε per half bounce (ε = ρ/R₀), against a radial strip of 8.4·10⁻⁵ and a phase window of 9.2·10⁻⁹. At 10 keV both deuterons and electrons leave the certified phase window after about 5·10⁻¹⁰ s, so the local sector cannot be the basis of a thermal band; C2 remains open. A usable certificate needs section-coordinate labels with certified gradients, radial windows wider than the banana excursion, wells at every precession phase with moving faces (N-212) and an averaged drift estimate. [N-214](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/label-drift-and-sector-scales.md)

### 26 November 2026 — Lipschitz labels and the missing backward bound (N-215)

Method note and correction to N-214. Lean proves the drift bound for labels that are only Lipschitz and constant on field lines (`LipschitzLabel.displacement_le`, by a Dini-derivative comparison with the field line through the current point), the vacuum decomposition of the Littlejohn velocity (`LabelDrift.velocity_vacuum`, `norm_drift_le`) and the guiding-centre corollary (`lipschitz_displacement_le`); default build, standard axioms. The claim in N-214 that label gradients follow routinely from the existing Jacobian certificates was wrong: `FieldBounds.quadratic` is an upper one-sided bound, which controls separation away from the section, and the label needs the lower bound. An untrusted screen gives a label Lipschitz constant of about 1.86 along the well and a direct bound of about 93 ε per half bounce, against an actual motion of 25 ε and 55 ε. A QA2R instance needs a lower bound per slab, a two-sided Grönwall step and a thicker certified region. C2 remains open. [N-215](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/lipschitz-labels-and-backward-bounds.md)

### 27 November 2026 — Wide-tube label campaign: screen and design (N-216)

The campaign requested for C2 was costed first. From the receipts, a certified slab step costs minutes of CPU, and covering one electron half-bounce window with the present tubes (radius below 1/300000) would need of the order of 10⁵ to 10⁶ CPU-hours. An untrusted screen (`scripts/dommaschk_kam/screen_wide_tube.py`) shows the flow is almost linear on much wider tubes: at frame radius 10⁻³ (physical radius 1.9·10⁻³) the reduced Jacobian has |μ| ≤ 0.034 and the label Lipschitz constant is 1.98. The campaign is therefore redesigned around one coarse trace per direction with a two-sided bound. Target by default: thermal electrons for about one bounce period. Stages and a stop rule are in the note. No certificate yet; C2 remains open. [N-216](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/wide-tube-label-campaign.md)

### 27 November 2026 — Backward distance estimate (N-216 stage 2a)

`Fields.BackwardDistance`: from a lower one-sided bound `−ℓ‖x−y‖² ≤ ⟪x−y, F x − F y⟫` on the slices visited, two solutions satisfy `‖x a − y a‖ ≤ exp(ℓ(t−a)) ‖x t − y t‖` (`norm_sub_le_exp_mul_of_lower`), with the Jacobian criterion (`lowerOneSidedOn_of_jacobian`), a chain over consecutive slabs (`norm_sub_le_exp_sum_mul_of_lower`) and an example where equality holds. Default build, standard axioms. This is the Lipschitz constant of the section map once a certificate supplies the lower bounds. Written by a sub-agent; statements, build and axioms checked by the coordinator.

### 27 November 2026 — Wide-tube certificate scoped (N-216 stage 3)

Scoping with exact rational intervals in Python (`scripts/qa2r_wide/`, no Lean compiled). The existing slab enclosure keeps the whole ball in a Taylor remainder and is too loose on wide balls (|μ| up to 2.6 at radius 10⁻³). A mean-value form (central-line enclosure plus radius times an interval bound on the spatial derivative of the Jacobian) gives |μ| ≤ 0.051 at radius 3·10⁻⁴ on all 332 slabs of the label-0.474 trace; the lower bound comes from the same data. The stage 1 screen had omitted the affine-frame term, so its values of μ and growth were too small (corrected in the note). Radius 3·10⁻⁴ is adopted; the expected horizon for the illustrative electron is about a quarter of a bounce period. Next: field-independent Lean lemmas for the mean-value form and a chain over `PositionFrameWide.valid`, then an 8-slab pilot. C2 remains open. [N-216](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/wide-tube-label-campaign.md)

### 27 November 2026 — Wide chain and lower Jacobian bound (N-216 stage 3, field-independent parts)

On-demand modules, standard axioms: `Certificates.PositionFrameWideChain` (`Steps`, `Steps.of_run`, `Steps.trajectory`: one trajectory through a list of steps checked by `PositionFrameWide.valid`, with the same `FieldBoundsOn` hypotheses as the narrow chain) and `Design.DommaschkJacobianLower` (`quadratic_ge_of_trace`, `spatial_log_norm_lower_of_bounds`, `spatial_log_norm_abs_of_bounds`). Written by a sub-agent; statements, build and axioms checked by the coordinator and added to `scripts/check_axioms_heavy.lean`. Still to do before the pilot: the mean-value lemmas for the Jacobian entries.

### 27 November 2026 — Mean-value step for the frame-reduced Jacobian (N-216 stage 3)

`Fields.FrameJacobianVariation` (default build, standard axioms): on a convex tube, a bound `γ‖w‖‖x‖²` on the quadratic form of the directional derivative of the Jacobian in frame directions gives `|⟪x, Ã(z₀+Mv)x⟫ − ⟪x, Ã(z₀)x⟫| ≤ γ‖v‖‖x‖²` (`abs_quad_sub_le`), hence a two-sided bound `(μ₀ + γρ)‖x‖²` on the tube from a central bound (`abs_quad_le_of_center`); for the plane, bounds `g₀, g₁` in the two frame directions give `γ = √(g₀² + g₁²)` (`directional_bound_of_basis`). Written by a sub-agent; statements, build and axioms checked by the coordinator. Remaining before the pilot: the derivative identities for the QA2R quotient-rule entries and the generator.

### 27 November 2026 — Second derivatives of the QA2R field-line Jacobian (N-216 stage 3)

On-demand module `Design.DommaschkJacobianSecond`, standard axioms: the derivative of each quotient-rule Jacobian entry over the common denominator D³ (`secondEntry`, `entry_derivative`), the Fréchet derivative of the position Jacobian (`velocityHessian`, `jacobian_derivative`, needing only D ≠ 0), and the bridge to the mean-value step: a two-sided central bound and bounds g₀, g₁ on the frame-conjugated directional derivatives over a convex set give `(μ₀ + √(g₀²+g₁²) ρ)‖w‖²` on the displaced points (`abs_quad_le_of_center`; with the central bound from the trace and disk data in `abs_quad_le_of_central_bounds`, forward clock only). The hypotheses g₀, g₁ are not yet discharged by any enclosure, and there is no link yet to `FieldBounds` or the Step records. Written by a sub-agent; statements, build and axioms checked by the coordinator.

### 27 November 2026 — Wide-tube pilot passed on 8 slabs (N-216 stage 3)

At frame radius 3·10⁻⁴ on the label-0.474 forward trace, Lean proves for slabs 0–3 and 268–271 the two-sided bound on the frame-reduced Jacobian over the whole trial ball (μ between 0.025 and 0.038), the full `FieldBounds`, the wide step check and a chain per group of four (generated modules `DommaschkWideTubeF000…F271`, `DommaschkWideTubeRows000Chain`, `…Rows268Chain` in the workstation cache; hand-written `Design.DommaschkWideTubeHessian` and `Design.DommaschkWideTubeStep`, on demand, standard axioms). Measured cost 23 CPU-minutes per slab, so the 332-slab forward trace costs about 127 CPU-hours; it has been started. Not yet done: a connected chain from a real entrance set, the backward direction, the label and the band statement. C2 remains open.

### 27 November 2026 — Wide-tube forward trace: all 332 slabs (N-216 stage 3)

On the label-0.474 forward trace with frame trial radius 3·10⁻⁴ and entrance radius 2.3·10⁻⁴, Lean proves for every one of the 332 slabs the two-sided bound on the frame-reduced Jacobian over the whole trial ball (μ between 0.0204 and 0.0524, integral 0.1761) and `FieldBounds`, and joins them into one chain: `DommaschkWideTubeRows000Joined.trajectory` gives, for every point of the entrance set, one field line through all slabs inside the recorded tubes. 11,290 generated modules, 167 CPU-hours, standard axioms only. The sources are archived in `generated/qa2r_wide/` as the on-demand library `QA2RWide` with a replay script. The rebuild under `lake` from that archive finished on 28 November 2026 (7.9 hours at 22 jobs) and the axiom audit passed on all 11,290 modules (`generated/qa2r_wide/replay-report.json`). `PositionFrameWideChain` gained `Steps.append` and `fieldBoundsOn_append`. Open: backward direction, the entrance-set theorem, the label on the tube, the drift bound and the band statement. C2 remains open.

### 28 November 2026 — Flow label on space-time, generic theorems (N-216 stage 2b)

Default build, standard axioms: `Fields.FlowLabel` (`Tube`, `label`, `norm_label_sub_le`, `label_invariant`, `displacement_le`: the section point of the solution through a space-time point is Lipschitz, constant along the flow, and drifts at most C(1+M)·sup‖w‖ per unit time along a perturbed path), `Fields.CylindricalLift.exists_lift` (lifted cylindrical coordinates of a path off the axis, no branch cut) and `Fields.PiecewiseTube.isOpen_region_inter` (a slab-wise tube is open). Not yet connected to the QA2R slab certificates. Scoping (untrusted): with the crude drift bound the expected horizon for the illustrative electron is about 13 R₀/v (2·10⁻⁶ s), and stage 4 needs certified bounds on |B|, ∇|B| and the planar speed on the tube. C2 remains open.

### 28 November 2026 — Two-sided tube structure for QA2R (N-216 stage 2b)

The slab certificates are connected to the flow label. Hand-written (on demand unless noted): `Fields.MovingFrameBackward` and `Fields.FlowLabelSymmetric` (default build), `Certificates.PositionFrameBackward`, `PositionFrameTube`, `PositionFrameHalfTube`, `Design.DommaschkTubeCheck`, `DommaschkTubeSymmetry`. Generated library `QA2RWide` (11,292 modules): `DommaschkWideTubeRows000Lower.lower` and `DommaschkWideTubeRows000Tube.tube`, `isOpen_region`: on toroidal angles (−3.5, 3.5) around the label-0.474 line, field lines from the inner tube reach the section inside the trial tube, are unique, and are at most e^{223/2000}·1.741 ≈ 1.95 times further apart at the section. The planar speed bound on the envelope is still a hypothesis. No particle statement yet; C2 remains open.

### 28 November 2026 — Stage 4 parts: envelope field bounds, continuation, guiding-centre lift (N-216)

Compiled, standard axioms: on the QA2R envelope `Region`, planar field-line speed ≤ 9/25 and 47/50 ≤ |B| ≤ 141/100 for every angle (`DommaschkRegionFieldBounds`), regularity (`DommaschkRegionRegularity`); `FlowLabel.stays` (no exit while the label stays in a section set); `PositionFrameCore` (forward core inside the inner tube); `Kinetic.CylindricalDrift.exists_lift_decomp` and its QA2R instance (lifted orbit = field-line motion plus a drift bounded through ‖∇|B|‖). A bound on ‖∇|B|‖ over the whole envelope is false at the needed size (numerically 5.3 against 1.35 on the tube); a per-slab certificate is in progress. No assembled particle theorem yet; C2 remains open.

### 28 November 2026 — Orbit theorem on the QA2R tube (N-216 stage 4)

`DommaschkWideTubeRows000Orbit.stays_in_tube` (library `QA2RWide`, 11,322 modules; replay and axiom audit passed at `da3f8e4`): a Littlejohn orbit of the QA2R field born over the inner tube around the label-0.474 line, with label within r of the reference point, stays over the tube on [0, T] and its field-line label moves at most κt, where κ ≥ 3.86·2H/|q|, r + κT ≤ 2.3·10⁻⁴ and an explicit angle condition holds. Certified on the tube: ‖∇|B|‖ ≤ 11/8, |B| ≥ 1.039 (`DommaschkWideTubeRows000Field`). At the illustrative electron scale the horizon is about 1.5·10⁻⁶ s. The orbit's existence is a hypothesis and there is no population statement, so C2 remains open; this is the first compiled confinement statement for guiding centres of this field with physical constants.

