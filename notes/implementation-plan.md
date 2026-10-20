# PlasmaLean implementation plan: theory → proof techniques → successively realistic models

Prepared 2026-10-20 against `8dcf3a2` (baseline: 14 Oct 2026 run, 53 modules, standard axioms only). Updated after each phase; see §9.
This is a plan. Nothing listed here as a target is implemented until a progress report says so. Status marks (✅ ◐ ○) reflect the latest report.

Sources: [domain-libraries](domain-libraries.md) (run protocol), [roadmap](formalization/08-roadmap.md) (gates P0–P9, research problems R1–R8),
[PDE bounds](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/pde-bounds-and-verification-roadmap.md) (Stages 1–7, Milestones A–G),
[microturbulence](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/microturbulence-and-available-energy.md), [holomorphic/KYM/Wick](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/holomorphic-bundles-kym-wick-rotations.md),
[BKM/Perelman](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/bkm-regularity-and-perelman-burn-bounds.md).

---

## 0. The two goals, and where we are

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
2. **The magnetic 2-form vanishes on flux surfaces.** B is tangent to Σ_ψ, so ω_B restricted to Σ_ψ is zero. The line bundle on a flux torus is therefore **flat (degree 0)**, and `flux_degree > 0` in the [holomorphic note](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/holomorphic-bundles-kym-wick-rotations.md) is physically wrong. `holomorphicSectionDim` is also true by definition, so it checks nothing. What survives is that the flat bundle's holonomy (in the Jacobian of the torus, which is the torus itself) encodes the rotational transform ι(ψ), and τ(ψ) is the conformal modulus. Re-target this module on that statement (compare `Challenge6_ConformalTorusModulus`).
3. **2-D ideal MHD global regularity is open.** [BKM §2.2](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/bkm-regularity-and-perelman-burn-bounds.md) claims that helically symmetric MHD is globally regular. That is known only with dissipation (viscosity and resistivity). The Riccati law dY/dt ≤ −νY + CεY² is a heuristic, not a theorem. Keep only the *conditional* statement: if the differential inequality holds, then Y stays bounded below the threshold. Mark the inequality itself as research (R3).
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
| **T1 Elliptic/vacuum** (Milestone A) | Bochner: Δ\|B\|² = 2\|∇B\|² for vacuum fields ✅. Weak maximum principle for C² subharmonic functions on bounded open sets in ℝ³ (elementary ε\|x\|² proof using Mathlib's `laplacian`) ✅. Boundary-to-interior bound for \|B\|² and \|B₁−B₂\|² ✅. Corrected min/max obstruction (§1.1) ✅ (no interior max; interior-min counterexample); toroidal curvature obstruction ∇⊥B = Bκ ✅ (vacuum; finite-β ○). | 2-D surface cover with proof-term checker ✅ (volume error from face samples) | Coil error fields: the volume error follows from the surface error; M5/M6 |
| **T2 Sturm–Liouville** (Milestone B) | Picone, Riccati, Jacobi ✅. Ballooning operator with weight W and Barta certificate ✅. Sturm necessity: contrapositive ✅, constant-coefficient iff ✅, conjugate point ⇒ no supersolution ✅. Mercier criterion: cylindrical ⇔ Suydam ✅, general index (supplied, Landreman–Jorge) reduces to Suydam ✅; helical equilibrium Mercier-unstable (a = 0 proved); Solov'ev exact index certified on all surfaces ✅ (validated quadrature). Newcomb uniformly in m ✅ (screw-pinch example: all integer (m,n), m ≠ 0). Infinite-line ballooning with asymptotic tails ✅ (tail ⇔ −1/4 threshold, sharp). | Polynomial interval checker ✅. Piecewise and Taylor-model checker with sqrt/exp enclosures ○ | MHD stability of M2–M5 |
| **T3 Parabolic comparison** (Milestone D, core of G2) | Nagumo first-crossing lemma (the sanity check in PDE §4.2) ✅. Weak comparison for the quasilinear radial transport operator, with an axis condition and edge Dirichlet data ✅ (semilinear; quasilinear D(T) ○). Steady lower/upper barriers bounding T(ψ,t) for all t ✅. Time-dependent barriers ◐ (core lemma allows them); two-sided quasilinear bands ✅ (K2: D(ψ,T)). Relative-entropy dissipation: corrected identity derived (notes/theory) ◐. | Barrier checker: N[T_sub] > 0 on [0,1] via the interval checker. Rational barrier profiles produced by a solver oracle. | G2 directly: M1–M5 |
| **T4 ODE invariants** | Invariant intervals for 0-D power balance dW/dt = P_α(T) + P_aux − P_br − W/τ_E, with thermal-stability and ignition window theorems ✅. Grönwall consequences (`Mathlib.Analysis.ODE.Gronwall`) ✅. Burn-yield lower bound (BKM §3.2, conditional) ✅. | Root isolation for the cubic-like balance curve; exact Bosch–Hale enclosures | M1 and the T3 sources |
| **T5 Discrete energy** (Milestone C) | SBP identity giving discrete energy ✅ (all N). FEEC d∘d = 0, hence discrete div B = 0 ○. M-matrix discrete maximum principle for the transport scheme ✅ (linear scheme). Consistency estimate linking discrete and continuum barriers ○. | `decide` on rational matrices | T3 (verified discretization), M2 |
| **T6 Functional-analytic validation** (Milestone G) | Contraction and radii inequalities ✅. ℓ¹_ν Banach algebra with convolution bounds ✅. Radii polynomial for ODE BVPs ✅ (generic validated BVP); 1-D (slab) Grad–Shafranov with exponential profile validated ✅ (classical C², kernel ForceBalance), then 2-D Grad–Shafranov fixed boundary, then a 3-D near-axis/DESC equilibrium ○. | Exact computation of Y₀, Z₁, Z₂ with tail estimates (truncation in ν-weighted norms) | M3–M5 equilibria |
| **T7 Field-line Hamiltonian** (Stage 5) | First-integral barriers ✅. Approximate-first-integral confinement for the exact rational stellarator field ✅ (95 toroidal transits, certified). Pendulum island-width bound with explicit remainder ○. Chirikov non-overlap ○. A posteriori KAM (de la Llave form) ○ (long term). Converse KAM / Greene residue as an obstruction certificate ○. | Fourier coefficient enclosures for b_{m,n} | M4/M5 confinement |
| **T8 Guiding centre and kinetics** (microturbulence note) | Guiding-centre equations; finite-time full-orbit versus guiding-centre error (R6) ✅ (crude, constant 1); Boozer GC model, gyro-Noether identity and iterated averaging lemma ✅; rigorous amplitudes for near-axis QA ✅ (passing alphas 0.19 s); trapped: single well and non-resonant bounce sums ✅, kick form ○. Bounce action J_∥ and the ∂_ψ identity (careful endpoint differentiation) ○. Min-B ⇒ max-J (sanity check 1) ✅ (for the integral expression; = ∂J/∂ψ ○). Available-energy kernel lemmas ✅ (note's opposite-sign claim refuted). Integral Â bound under precession dominance ○. Omnigeneity implies zero bounce-averaged radial drift ○. | Quadrature with remainder for bounce integrals (√ endpoint singularity) | Alpha confinement (3.5 MeV obstruction), and χ upper bounds for T3 |
| **T9 Hyperbolic energy** (Stage 6, holomorphic §4) | Elsässer energy and cross-helicity identities ✅ (conservation under skew transport). Null-structure identity ⟨(z∓·∇)z±, z±⟩ = 0 for divergence-free tangent fields ○. Abstract commuted-energy Grönwall theorem in Hilbert space, with the commutator bound as hypothesis ○. Sobolev step stated as an explicit interface (§1.5). | none | Long-time linear bounds, M5 |
| **T10 Exploratory geometry** (holomorphic/KYM/BKM) | Discovery only until vetted: flat-bundle holonomy ↔ ι(ψ) (§1.2); Futaki-type obstruction for a *specific* near-axis QS ansatz (an honest test: does it reproduce the Garren–Boozer O(r³) obstruction?); conditional BKM continuation. Each needs a verdict note before any Lean code. | none | Possibly T6/T7 |

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
