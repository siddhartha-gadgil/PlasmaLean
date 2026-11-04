# Assessment of the kinetic plasma and coils research brief

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-36` |
| Title | Assessment of "Coils, kinetic plasma and a maintained fusion state: a research brief for PlasmaLean" (3 November 2026) |
| Kind | source assessment |
| Addresses | `G-2` (C5), `G-3`, `G-5`, `G-7`, `G-8`, `G-11`; new questions `Q-26` (burn dynamics and kinetic yield), `Q-27` (residual-based invariant neighbourhood), `Q-28` (kinetic model contract and turbulent flux bound); touches `Q-10`, `Q-16`, `Q-22`, `Q-25` |
| Depends on | N-19 (verified evolution), N-20 (available energy), N-2 (relative entropy), N-5, N-6 (burn and coupling), N-16 (coil KAM), N-21, N-32 (holomorphic/QS assessments), N-22 (goal proposals); Lean: `Kernel/Fusion` (`DTPlasma.alphaPower`), `Theory/Stability/RiccatiComparison.riccati_le_initial`, `Theory/Fields/QSLinearSystem` (`cross_fqsVec`, `eq_fqsVec_of_cross_of_inner`, `StrongQSAt.fqsAt`), `Theory/Transport/RelativeEntropyCoercive.relEnt_le_mul_fisher`, `Theory/Kinetic/AvailableEnergy` |
| Dependency requirement | none for the assessment; the lean-ready items of Q-26 and Q-27 need only real analysis already used in `RiccatiComparison` and `Kernel/Fusion` |
| Produces | extraction table (50 claims), exact checks `scripts/kinetic_brief/check_brief.py` (12/12 pass), verdicts, patch note N-37, method notes N-38–N-40, questions Q-26–Q-28, audit items AK-1–AK-3, the in-place addition to N-22 |
| Difficulty | routine (assessment); routine to moderate (Q-26, Q-27 in Lean); research (Q-28) |
| Status | assessment complete |
| Lean evidence | none new; existing declarations cited per claim below |
| Audit evidence | brief checked against commit `5d435ea` (the brief inspected `703c406`, 8 commits earlier; only notes and skills changed in between); explicit content re-derived in sympy; audit items AK-1–AK-3 |
| Last updated | 4 November 2026: created |

## Source

- **Path:** `sources/PlasmaLean_Kinetic_Coil_Research_Brief.pdf` (25 pp., pdfTeX, committed in `609358e`).
- **Title:** "Coils, kinetic plasma and a maintained fusion state. A physics specification and
  mathematical research programme for PlasmaLean."
- **Authors:** none named; "Research brief prepared for Vamsi Pingali and PlasmaLean", "prepared for
  Vamsi Pingali and the PlasmaLean agents". Supplied by the user, 4 November 2026.
- **Date / version:** 3 November 2026; repository snapshot `703c406c7cc4a5885651429e14cdb0941ebd7f0e`.
- **SHA-256:** `0ab99948d7937c11ffaa9442d2604ff7d2b413399aec10c57c8a7de328d2ecdd`.
- No arXiv ID or DOI. The whole text was read (no scanned pages or missing figures). The brief claims
  no new theorem, no operating point and no endorsement by a plasma physicist (p. 1).

## Summary of the brief

The brief sets the problem as: one coil set and one operating plasma that produce useful fusion
power while confined and within temperature, density, field and wall limits, for a specified
neighbourhood of initial data and manufacturing errors. Its route is geometry for the background
field, a self-consistent plasma in that field, and estimates for perturbations that need not share
the background symmetry. It supplies:
1. a multispecies kinetic–Maxwell parent system (Landau collisions, fusion, atomic, radiation,
   neutral and wall interfaces) with an exact energy ledger (§§1–5);
2. a kinetic-to-transport flux interface and an electrostatic gyrokinetic pilot (§§5.2, 6);
3. QS and complex-geometric representations, largely the content already assessed in N-32 (§7);
4. a realistic reading of BKM, entropy/hypocoercivity, Wick rotation and GR analogies (§8);
5. a description of PlasmaLean at `703c406` (§9);
6. a finite-horizon a posteriori theorem architecture and an all-time variant (§10);
7. work packages P0–P10, acceptance criteria and sanity checks (§§11–12, App. A–B).

To avoid clashing with the roadmap gates P0–P9 and the §12 labels P1–P4, its packages are cited
here as **KB-P0 … KB-P10**.

Its three standing distinctions (p. 1) agree with the project's existing policy:
- vacuum orbits are not a finite-pressure plasma;
- smoothness ≠ stability ≠ confinement ≠ favourable heating balance;
- a theorem for a PDE is not evidence that the PDE predicts the experiment.

## Extraction table

Kinds: thm = published theorem with proof; sketch = proof sketch; asym = formal asymptotic; def =
definition or model; prop = proposal or plan; open = open question; obs = observation (elementary,
proved in the brief or by hand here).

| # | Claim (paraphrased) | Locator | Kind | Model, hypotheses, units | Relevance |
| --- | --- | --- | --- | --- | --- |
| 1 | Landau collisions + collective fields form a kinetic approximation, not an N-body description | §1 | def | classical, weakly coupled DT; SI, T in J | G-3 |
| 2 | An operating claim must fix horizon, admissible perturbations, controls, uncertainties; one scalar T is insufficient | §1 | prop | — | G-2, G-8 |
| 3 | Filament Biot–Savart field (2.1) is div- and curl-free away from wires | §2.1 | thm (standard) | closed smooth curves | G-5 |
| 4 | Finite winding packs (2.2) and all return paths are needed; a return at astronomical distance is not engineering | §2.1 | def/prop | — | G-5, Q-2 |
| 5 | Circuit law (2.3) is a magnetoquasistatic reduction; do not count Lİ twice | §2.1 | def | slow currents | G-5 |
| 6 | Maxwell system (2.4)–(2.7) and constraint propagation (2.8) | §2.2 | thm (standard) | charge continuity | Q-28 |
| 7 | Zero net toroidal current does not mean j_pl = 0 and does not exclude local current-driven modes | §2.2, §9 | obs | finite β | C1 scope (G-1, G-4) |
| 8 | Multispecies Landau operator (3.2); conservation (3.3)–(3.4); H-theorem (3.5) | §3.1 | thm (cited [1]) | regular, decaying f; symmetric ln Λ | Q-28 |
| 9 | D–T rate (3.6) and its weak form (3.7); R = n_D n_T⟨σv⟩ needs Maxwellians | §3.2 | def | nonrelativistic | G-2, `BoschHaleDT` |
| 10 | Do not add the full 3.5 MeV × R_DT as local heat; deposition comes from slowing down (3.8) | §3.2 | obs | — | G-2, Q-26 |
| 11 | Heating, atomic and radiation channels with one energy ledger (4.1)–(4.2); optically thin closure | §§3.3, 4.1 | def | — | G-3 |
| 12 | Wall inflow kernel (4.4), sheath, interface conditions; a perfect conductor need not have zero normal B | §4.2 | def (standard) | — | G-3 |
| 13 | Wall heat equation is a thermal interface, not a damage qualification | §4.2 | def | — | G-8 |
| 14 | Energy-flux decomposition (5.5); moment equations (5.6)–(5.8); Poynting (5.9) | §5.1 | thm (standard) | moments exist | Q-28 |
| 15 | Flux-surface divergence identity (5.10) and profile equations (5.11)–(5.12) with all omitted terms accounted | §5.2 | asym | fixed nested surfaces | G-2, Q-15, Q-22 |
| 16 | Electrostatic GK energy flux (5.13) | §5.2 | asym | leading order | Q-28 |
| 17 | A heat-flux bound does not control its divergence; a pointwise barrier needs an operator-defect bound or a monotone scheme | §5.2 | obs | — | Q-26, Q-28 |
| 18 | Integral core energy does not give a pointwise hot core | §5.3 | obs | — | G-2 |
| 19 | sup_x ‖⟨v⟩^ℓ(f − f̂)‖_{L²_v} with ℓ > 9/2 controls moments of order ≤ 3 | §5.3 | obs | fixed reference speed | Q-27 |
| 20 | T is locally Lipschitz in the first three moments given a density lower bound | §5.3 | obs | n ≥ n_min > 0 | Q-27 |
| 21 | Kinetic yield bound (5.14) for a kernel bounded by K_max | §5.3 | obs | bounded kernel; tails separately | Q-26 |
| 22 | Scientific gain Q = P_fus/P_aux ≠ plant gain | §5.3 | def | — | G-2, G-8 |
| 23 | Hierarchy: coil equilibrium, nonlinear EM gyrokinetics, transport, edge | §6.1 | prop | GK orderings | Q-28 |
| 24 | Electrostatic pilot (6.1)–(6.4), d³v = 2πB₀ dv∥ dμ/m | §6.2 | asym (cited [4, 5]) | local δf, fixed B₀ | Q-28 |
| 25 | Near exact QS the ambipolarity condition can be degenerate; E_r is not fixed by it | §6.2 | obs (known) | — | G-10, Q-22 |
| 26 | Evidence list before accepting a small heat loss; available energy correlates with but does not bound flux | §6.3 | prop | — | N-20, Q-28 |
| 27 | QS is a condition in Boozer coordinates and must be measured in a volume, not one surface | §7.1 | def | — | Q-16 |
| 28 | Vacuum strong QS (7.2): B·u = C, u = (∇Ψ × B + CB)/‖B‖², B × u = ∇Ψ | §7.1 | sketch | connected vacuum region | Q-25 |
| 29 | Fixed solid torus: the normalised tangent harmonic field is unique | §7.2 | sketch | b₁ = 1, Neumann | Q-24 |
| 30 | F = dτ ∧ α − ∗₃α is ASD and closed iff α harmonic; primitive (1,1); H²(X) = 0 | §7.3 | sketch | orientation dτ ∧ vol₃ | N-21, N-32 |
| 31 | Winding-surface current potential; REGCOIL | §7.3 | def (cited [12]) | — | G-5, Q-2 |
| 32 | A non-constant local Maxwellian is not an exact zero-flow source-free stationary solution | §7.4 | obs | full kinetic model | Q-28 |
| 33 | Static isotropic MHD with total vacuum field forces constant pressure | §7.4 | obs | connected domain | Q-14, Q-20 |
| 34 | BKM (Caflisch–Klapper–Steele) is conditional and model-specific; Luk–Strain not applicable unchanged | §8.1 | thm (cited [18, 19]) | periodic, ideal | N-19 |
| 35 | Relative-entropy functional (8.2); GK free energy (8.3); balance (8.4); Helander–Plunk bounds are not decay bounds | §8.2 | def / thm (cited [14–16]) | local GK, gauge fixed | Q-28 |
| 36 | An external OU bath is not fusion heating; the Perelman analogy must yield a coercive identity | §8.2 | prop | — | N-2, N-19 |
| 37 | Cauchy–Schwarz flux bound (8.5); Research target 1: Q ≤ C_Q W, Ẇ ≤ −λW + C W^{3/2} + ε | §8.3 | obs / open | electrostatic | Q-28 |
| 38 | Wick rotation not equivalent without a reconstruction theorem | §8.4 | obs | — | N-21 |
| 39 | He–Xu–Yu Alfvén-wave stability as a GR-method precedent | §8.5 | thm (cited [21]) | ℝ³, near background | N-19 |
| 40 | C Ṫ = G(T): equilibrium T* is unstable if G′(T*) > 0 | §8.6 | obs | 0-D | Q-26, G-2 |
| 41 | Finite fuel and no refuelling: fusion power bounded below for all time is impossible | §8.6 | obs | particle balance | Q-26, G-2 |
| 42 | Description of PlasmaLean at `703c406` (contract, transport kernel, relative entropy, available energy, polygon coil, coil KAM) | §9 | obs | — | all |
| 43 | A pressure budget is not equality of stresses | §9 | obs | — | Q-10 |
| 44 | Research target 2: residual-based estimate D⁺‖e‖ ≤ a‖e‖ + b‖e‖² + ϵ on an admissible set | §10.1 | prop | chosen model and norm | G-7, Q-27 |
| 45 | (10.1): an inward radius exists when λ² ≥ 4Lϵ (L > 0) | §10.2 | obs | — | Q-27 |
| 46 | A stability theorem certifies a burn only with a norm-to-observable step | §10.2 | prop | — | Q-27, G-2 |
| 47 | Work packages KB-P0–KB-P10 | §11 | prop | — | G-3, G-8, G-11 |
| 48 | First milestone and acceptance table; three rejection tests | §12 | prop | — | G-3, G-8 |
| 49 | Weak-form reaction kernels (A.1) | App. A | def | — | Q-28 |
| 50 | Sanity checks B.1–B.8 | App. B | prop | — | Q-28, G-2 |

## Checks

Exact checks, `scripts/kinetic_brief/check_brief.py` (sympy 1.14, `.venv-ws`, run with `-I`): **12/12
pass.**
- **Claim 8 (partial):** U(z)z = 0 and |z|³ a·U(z)a = |a × z|² ≥ 0 (App. B item 1).
- **Claim 14:** F = (½mn|u|² + (3/2)nT)u + Πu + q, on a rational five-point distribution.
- **Claim 32:** the Vlasov operator on a local Maxwellian is f · v·[∇log n + (m|v|²/2T − 3/2)∇log T −
  qE/T] for arbitrary n, T, E, B. The magnetic term drops out, and the cubic coefficient is
  (m/2T)∂log T, so ∇T = 0 is forced.
- **Claim 24:** d³v = 2πB₀ dv∥ dμ/m.
- **Claim 35:** the two forms of W_k agree under quasineutrality (two species, symbolic), and
  Γ₀ = I₀(b)e^{−b} ∈ (0, 1] at sample points. This gives W_k ≥ 0 in the η form.
- **Claim 45:** the discriminant of Lr² − λr + ϵ is λ² − 4Lϵ, and the minimum value ϵ − λ²/(4L) is
  attained at r = λ/(2L).
- **Claim 30:** in ℝ⁴ with orientation dτ ∧ dx₁ ∧ dx₂ ∧ dx₃, ∗(dτ ∧ α − β) = −(dτ ∧ α − β), so the
  brief's form is ASD. **N-32's form β + dt ∧ α is self-dual in that orientation.** It is ASD for the
  orientation vol₃ ∧ dt, which N-32 does not state. This is a convention gap in N-32, not an error of
  substance (patch note N-37).

By hand:
- **Claim 19:** ∫|v|^k|g| ≤ ‖⟨v⟩^ℓ g‖₂ ‖⟨v⟩^{k−ℓ}‖₂, and the last factor is finite iff 2(ℓ − k) > 3. For
  k = 3 this gives ℓ > 9/2. Correct.
- **Claim 20:** T = (2/(3n))(K − ½mn|u|²), with nu the first moment, is smooth in (n, nu, K) for
  n ≥ n_min > 0. Correct.
- **Claim 21:** add and subtract F_D f_T. Correct as stated (L¹_v norms, bounded kernel).
- **Claim 33:** a vacuum field has j = ∇ × B/μ₀ = 0, so ∇p = j × B = 0. Correct on a connected domain.
- **Claim 37:** write E h v = (h√(T/F₀))(E v√(F₀/T)) and apply Cauchy–Schwarz. Correct.
- **Claim 40:** linearisation of a scalar ODE. Correct.
- **Claim 41:** with Ṅ_D = −∫R_DT and no source, ∫₀^∞∫R_DT ≤ N_D(0) < ∞. Hence R_DT cannot stay above
  a positive constant. Correct.
- **Claim 28:** B × u = (∇Ψ‖B‖² − B(B·∇Ψ))/‖B‖² = ∇Ψ when B·∇Ψ = 0. This is already compiled:
  `Fields.QSLinear.cross_fqsVec` and `eq_fqsVec_of_cross_of_inner`, and `StrongQSAt.fqsAt` for the
  equivalence (default build).

Against the code (claims 10, 42, 43, 45):
- **Claim 42 (§9 description):** accurate.
  - The transport kernel takes supplied D ≥ 0 and R, with solutions as hypotheses.
  - `relEnt_le_mul_fisher` assumes boundary anchoring `S.T a = S.Ts a`, a lower bound k₀ on κT* and
    an upper bound T ≤ M T*.
  - The `AvailableEnergy` header says the kernel is unchecked against Mackenbach–Proll–Helander and
    records the sign correction.
  - The polygon-coil result is conditional on field-line existence, with the toroidal-field return
    at 10⁶ R₀ (README).
  - The `CoilKamCert` bound is ≈ 10⁹ (N-16).
- **Claim 10:** `Kernel/Fusion` defines `alphaPower = (E_α/4)(f_fuel n)²⟨σv⟩ V` with E_α = 3.5 MeV,
  i.e. deposition fraction 1 and prompt. The module docstring lists "alpha slowing-down delay" and
  "fuel burn-up, helium ash dilution" as neglected, but the full-deposition assumption is not named
  as a hypothesis of the G-2 claims. Audit item AK-1.
- **Claim 41:** the fixed-density burn models (0-D window, `solovev_one_plasma_*`) implicitly assume
  refuelling and ash removal. G-2 says "over [0, T_burn] (or forever)". Audit item AK-2.
- **Claim 43:** already recorded: Q-10, and N-19 §3.2 ("`p_thermal ≤ p_eq` is only a pressure-budget
  screening inequality").
- **Claim 45:** `riccati_le_initial` covers Y′ ≤ −νY + CεY² (multiplicative small parameter, no
  additive residual). The brief's (10.1) with an additive ϵ is not in Lean. This is Q-27.

Not re-derived (standard physics or cited results, recorded with the brief's own caveats): claims 3,
6, 8 (conservation and H-theorem beyond the kernel algebra), 9, 11–13, 15, 16, 23, 24 (drifts and
(6.3)), 25, 29, 31, 34, 35 (Helander–Plunk bounds), 39, and the proposals.

**Tally.** 50 claims extracted; 22 checked (12 by exact computation, 10 by hand or against the code);
22 correct, 0 incorrect; 28 unverified (standard or cited content, models and proposals). One
convention gap was found in our own N-32. Two unnamed assumptions in our C5 models become audit
items AK-1 and AK-2.

## Verdicts by section

- **§§1–4 (parent system):** correct as a specification. These are the standard equations with
  careful bookkeeping warnings (no double counting of Lİ, Ohmic, alpha or radiation energy;
  charge-balanced injection). It is a model contract, not a theorem. Useful as the target of a
  kinetic model contract (Q-28, part a). Not lean-ready beyond algebraic identities (Landau kernel,
  moment algebra, reaction-count moments).
- **§5 (energy, flux, observables):** correct. This section matters most for G-2.
  - The kinetic yield bound (5.14) and the moment-norm control (claim 19) are elementary and
    lean-ready (Q-26, Q-27).
  - The point that a flux bound does not preserve a pointwise barrier (claim 17) applies directly to
    our barrier theorems, which take supplied coefficients. A kinetic bridge must supply an
    operator-defect bound. Recorded in N-38 and N-40.
- **§6 (gyrokinetics):** standard and correctly caveated. It describes numerical programmes (KB-P4)
  that are outside the laptop budget and the project's present scope. The pilot equations are
  usable as a Lean model contract later (Q-28).
- **§7 (QS and geometry):**
  - Repeats N-32 (fixed-domain uniqueness, the FQS system, the abelian ASD lift) with a cleaner
    orientation convention. Adds nothing new for Q-24 or Q-25. Patch N-37.
  - The volume-measurement point (claim 27) agrees with the stated scope of `dommaschk_Q16_vacuum`
    (two certified surfaces, not a volume).
  - The Maxwellian and vacuum-pressure negative fixtures (claims 32, 33) are cheap sanity theorems.
- **§8 (analytic routes):** a sober and correct assessment.
  - Its free-energy identity checks out.
  - Research target 1 (a flux bound from a coercive free-energy inequality) is a genuine open
    research question (Q-28 b).
  - §8.6 gives two elementary obstructions that our G-2 statements must respect (Q-26, AK-2).
- **§9 (our repository):** accurate at `703c406`. Its two amendments are already in our notes:
  - low net current ≠ no current-driven modes, a scope remark for C1;
  - budget ≠ equality, which is Q-10.
- **§10 (theorem architecture):** consistent with N-19 §2.3 (Pizzocchero–Tassi supersolution) and
  the §11 gates E2–E8. It adds:
  - the additive-residual form with an explicit inward radius (Q-27, lean-ready scalar part);
  - the norm-to-observable step (N-39).
- **§§11–12 (packages, acceptance):** a useful organisation. KB-P0 (one shared candidate record)
  coincides with the `StellaratorContract` common-witness item of G-11/AR-L. KB-P5 is N-20's open
  part. KB-P1 is G-5/Q-2. The acceptance table and rejection tests are added to the goal proposals
  (N-22, in place).
- **Proposed goal (not adopted):** a maintained operating state on a finite horizon. The user chose
  on 4 November 2026 to record it as a proposal only, linked from G-7 and G-8. It consists of a coil
  candidate, a self-consistent reference with a continuum residual, a kinetic flux bound and a
  coupled thermal, fuel, alpha and radiation balance on the same candidate. An all-time state is a
  later, stronger target.

## Resulting changes to the graph

| Source item | Note | Class | Result |
| --- | --- | --- | --- |
| whole brief | — | — | this note (N-36) |
| §7.3 orientation (claim 30) | N-32 | partial | patch note N-37 |
| §5.3 (5.14), §8.6, §3.2 alpha deposition (claims 10, 21, 40, 41) | N-5, N-6 | partial | method note N-38; new Q-26 |
| §10, §5.3 moment norms (claims 19, 20, 44–46) | N-19 | whole | method note N-39; new Q-27 |
| §§3, 5, 6, 8.2–8.3 (claims 8, 14, 17, 24, 32, 35, 37) | N-20 | whole | method note N-40; new Q-28 |
| §12 acceptance and rejection tests (claim 48) | N-22 | none | edited in place |
| claims 10, 41 | `Kernel/Fusion`, G-2 | — | audit items AK-1, AK-2 (low) |
| claim 30 | N-32 | — | audit item AK-3 (low, prose) |
| claim 7 | C1 scope | — | recorded here and in G-1's row; no contract change |
| claims 4, 31 (coil realizability) | N-16, G-5 | partial | no change: the idealized return and vacuous bound are already stated |
| claim 43 | Q-10 | — | no change: already recorded |

## Difficulty, barriers and readiness

The assessment is complete. The lean-ready outputs are:
- Q-26 (a)–(c): the kinetic yield perturbation bound, the thermal-instability criterion and the
  finite-fuel obstruction;
- Q-27 (a): the scalar inward-radius comparison lemma with an additive residual;
- the negative fixtures of claims 32 and 33 (Q-28 a).

The kinetic and gyrokinetic content (Q-28 b) is research. The numerical packages (KB-P4, nonlinear
gyrokinetic benchmarks) need external codes and compute far beyond the laptop budget. They are not
planned.

## Outputs and next dependencies

N-37 (patch of N-32), N-38, N-39 and N-40 (method notes); Q-26, Q-27, Q-28; AK-1–AK-3; the in-place
addition to N-22.
