# PlasmaLean implementation plan: theory → proof techniques → successively realistic models

**Proposed review amendment, 24 October 2026:** section 11 adds a sourced evolution, symmetry and thermal-verification programme and contribution targets. It does not mark new mathematical work complete.

Prepared 2026-10-20 against `8dcf3a2` (baseline: 14 Oct 2026 run, 53 modules, standard axioms only). Updated after each phase; see §9.
This is a plan. Nothing listed here as a target is implemented until a progress report says so. Status marks (✅ ◐ ○) reflect the latest report.

Sources: [domain-libraries](domain-libraries.md) (run protocol), [roadmap](formalization/08-roadmap.md) (gates P0–P9, research problems R1–R8),
[PDE bounds](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/pde-bounds-and-verification-roadmap.md) (Stages 1–7, Milestones A–G),
[microturbulence](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/microturbulence-and-available-energy.md), [holomorphic/KYM/Wick](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/holomorphic-bundles-kym-wick-rotations.md),
[BKM/Perelman](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/bkm-regularity-and-perelman-burn-bounds.md).

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

Sequencing inside a cycle: A and C start at once. B takes A's outputs from the previous cycle, plus any sourced theorems. D uses whatever B and C have merged. E runs last. The cycle closes with a progress report, `status.json`, slideshow, `README.md`, site regeneration and `check_site.mjs`.

Recommended size: 4–6 sub-agents per cycle (within the workflow guideline of fewer than 10).

---

## 4. Theory tracks (with technique companions)

Status legend: ✅ done · ◐ partial · ○ not started.

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
