# PlasmaLean: deterministic additions and transferable techniques

**Status:** proposed research and implementation targets, 24 October 2026. No new theorem, Lean module, physical validation or numerical improvement is claimed by this note.

This note expands the existing implementation plan's G3 and D/K packages. It preserves G1 (confinement and stability) and G2 (sustaining useful temperature and thermal performance). The companion [probabilistic goals](probabilistic-goals-and-techniques.md) treats ensemble observables, uncertainty and randomized computation. A kinetic density equation can be deterministic: increasing physical detail and adding probability are independent choices.

## 1. Decisions and priorities

The new deterministic work should answer three questions: how much an omitted effect can change the chosen prediction; what smallest correction is justified when it matters; and what conclusion the resulting evidence actually supports. These are refinements of G3, not a replacement for G1/G2.

| ID | New deterministic output | Practical priority | Completion evidence |
| --- | --- | --- | --- |
| **N1 — Observable error from model and closure defects** | A finite-time bound connecting a named baseline prediction to a selected refined description, including numerical error. | **High for any prediction used in a design decision.** Start with one consequential discrepancy. | A produced defect bound, a stability estimate and an observable estimate at the actual parameters; unresolved terms remain explicit. |
| **N2 — Smallest justified deterministic correction** | A corrected closure, perturbed orbit model, selected kinetic species or hybrid model that resolves the N1 uncertainty. | **Conditional.** High once the omitted effect can alter the decision; otherwise defer. | A specified improvement for the same observable, with remaining uncertainty and computational cost recorded. |
| **N3 — Applicability and decision certificates** | A precise statement of what is proved, compared, measured, assumed or unresolved, and whether the decision margin survives those uncertainties. | **High and lightweight from the first candidate.** | A reviewable decision record and, where possible, a theorem connecting supplied bounds to the decision. |

N1 can succeed without activating N2: a sufficiently small bound may justify retaining the baseline. **N3 is shared decision-certification and applicability infrastructure supporting G1/G2 and N1/N2, rather than an independent physical objective.** It can conclude that the evidence is inconclusive. Neither outcome requires a microscopic derivation or a stochastic equation.

**Scope decision:** a complete particle-to-MHD derivation, its formalization, and a general adaptation of Deng–Hani–Ma's proof are outside the active and presumed future programme. A specific estimate can be revived for a named need. The purpose is useful, justified predictions at finite parameters.

## 2. What changes for the existing deterministic goals?

G1/G2 still require their original model-specific existence, geometry, orbit, stability, thermal and numerical results. Two priority techniques can improve that work immediately:

1. **D1: modified energies and residual propagation.** Seek smaller verified error tubes, longer verified intervals or a larger admissible perturbation set for an existing evolution problem.
2. **D2: driven relative entropy.** Seek a useful stability or error estimate relative to a selected hot profile while retaining the sources, losses and boundary fluxes of the actual thermal problem.

These are new methodological tasks serving old objectives. They should not be advertised as new physical goals or as evidence that extra kinetic variables are necessary. Their practical value must be measured on the selected destination problem. A general comparison lemma or an attractive toy-model decay estimate is preparatory work.

Four different statements remain separate:

| Statement | What it establishes | What still needs proof or evidence |
| --- | --- | --- |
| Global well-posedness of the selected equation | Existence, uniqueness and the specified continuous dependence for that mathematical model. | Quantitative stability constants, practical approximation accuracy, physical adequacy and desired operation. |
| Quantitative stability | Controlled response to specified perturbations in stated norms and over a stated horizon. | Whether model defects are bounded in those norms, and whether the norm controls the required output. |
| A verified numerical solution | A calculation approximates the selected mathematical solution within a certified error. | Whether the equation represents the physical regime adequately. |
| Model adequacy for a decision | The available evidence supports using the selected prediction within its decision margin. | Adequacy for different regimes, observables or longer times. |

Even a future global well-posedness theorem would therefore leave N1–N3 useful. Conversely, finite-time verified operation may be possible without solving an unrestricted global regularity problem.

## 3. N1: propagate the omitted effect into the actual output

### 3.1 A theorem template, with its proof obligations visible

Let the selected deterministic model be

$$
\partial_t U=F(U).
$$

Let a more detailed deterministic description have state \(f\). Choose a projection or reconstruction \(V=\Pi f\) into the **same admissible state space** as \(U\). Suppose its exact evolution is proved to be

$$
\partial_t V=F(V)+d.
$$

Here \(d\) is the closure or model defect. A validated numerical reconstruction \(U_a\) has residual

$$
\partial_t U_a=F(U_a)+r_{\rm num}.
$$

For \(e=V-U_a\), subtraction gives

$$
\partial_t e=F(V)-F(U_a)+d-r_{\rm num}.
$$

This identity requires no particle-to-kinetic limit. It compares two already selected mathematical descriptions. It does require an actual derivation of the projected equation. Kinetic moments are not automatically divergence-free states of incompressible MHD; projection, field compatibility, constraints and boundary liftings may add defects of their own.

If a suitable stability estimate reduces the error to

$$
\partial_t e=A(t)e+\mathcal N(t,e)+d-r_{\rm num},
$$

and gives, in the required norm,

$$
D^+\|e\|_P
\le -\lambda(t)\|e\|_P+C(t)\|e\|_P^2
       +\delta_{\rm model}(t)+\epsilon_{\rm num}(t),
$$

then a nonnegative comparison function satisfying

$$
R(0)\ge\|e(0)\|_P,
\qquad
R'\ge-\lambda R+CR^2+\delta_{\rm model}+\epsilon_{\rm num}
$$

is a candidate error bound. Here \(D^+\) denotes an upper right derivative; use an appropriate absolutely continuous comparison theorem in the formal statement. All inequalities must hold throughout the certified state region. Existence, continuation and the bootstrap that keeps the solution in that region remain separate obligations.

For an observable Lipschitz on that region,

$$
|Q(V)-Q(U_a)|\le L_Q\|V-U_a\|_P\le L_QR.
$$

This is the desired finite-time bridge. It is a proposed reusable contract, not a claim that the needed estimates are known for arbitrary MHD or a reactor.

### 3.2 What has to produce the inputs?

Every application must supply:

- **A defect producer:** bounds on the omitted stress, heat flux, electromagnetic response or other term in the norm used by the stability theorem. A small stress amplitude alone does not bound its divergence.
- **Initial and boundary compatibility:** discrepancies in initial data, conserved quantities, wall data and constraint enforcement, including tail or domain truncation effects when present.
- **A stability producer:** estimates derived from the selected operator, nonlinear terms, geometry and boundary conditions.
- **An observable producer:** continuity, trace, integration or comparison estimates for the required quantity. An energy norm does not automatically control pointwise core temperature, wall heat flux or an orbit hitting event.
- **An evidence classification:** theorem-backed, controlled comparison, empirical, assumed or unresolved. An empirical bound gives a conditional mathematical certificate when supplied as a hypothesis; it does not become a proved bound on nature.

The first useful application should be small: for example, propagate an explicitly bounded heat-flux discrepancy into a thermal performance margin, or propagate a prescribed field perturbation into a finite-time orbit-clearance estimate. Selecting the numerical defect envelope is part of that application, not a free assumption made to obtain a preferred answer.

## 4. D1: modified energies for the old equations and N1

Work in a stated Hilbert space \(H\), with any derivative regularity included in the definition of \(H\). Seek a positive self-adjoint operator or quadratic form satisfying

$$
m\|e\|_H^2\le\langle e,Pe\rangle\le M\|e\|_H^2,
\qquad 0<m\le M<\infty.
$$

For fixed \(P\), the useful dissipation statement is the quadratic-form inequality

$$
2\operatorname{Re}\langle Pe,Ae\rangle
\le-2\lambda\langle e,Pe\rangle
$$

on the required operator domain and admissible subspace. In finite dimensions this is the familiar matrix inequality \(A^*P+PA\preceq-2\lambda P\). For a time-dependent \(P(t)\), include \(\langle e,\dot P e\rangle\) on the left. For a PDE, a matrix check on retained modes needs a proved reconstruction and tail argument before it certifies the PDE.

Given also \(\|\mathcal N(t,e)\|_P\le C(t)\|e\|_P^2\), Cauchy–Schwarz yields the scalar error inequality in §3. Strict decay is not always possible or necessary: an improved growth bound can still reduce error amplification over the operating interval.

### 4.1 Why cross terms can help

The elementary deterministic system

$$
x'=y,\qquad y'=-x-y
$$

has Euclidean energy derivative \((x^2+y^2)'=-2y^2\), which does not directly damp \(x\). But

$$
E=\tfrac12(x^2+y^2+xy),\qquad E'=-E,
\qquad
\tfrac14(x^2+y^2)\le E\le\tfrac34(x^2+y^2).
$$

The cross term exposes transfer of dissipation through the coupling. This is a useful formal sanity fixture. The project contribution is establishing the corresponding useful estimate for a selected PlasmaLean model.

### 4.2 A negative fixture that must remain

For the periodic linearized system with viscosity \(\nu>0\) and zero magnetic resistivity,

$$
u_t=B_0\cdot\nabla b+\nu\Delta u,
\qquad b_t=B_0\cdot\nabla u,
$$

the choice \(B_0=e_3\), \(u=0\), \(b=e_2\cos x_1\) is a nonzero, divergence-free, mean-zero stationary perturbation. Consequently no equivalent norm can decay strictly on a space containing this state. A claimed decay estimate must remove justified invariant modes, target another observable, weaken its conclusion or use dissipation already present in the physical model. Adding artificial damping simply to invoke a theorem changes the question.

Villani's hypocoercivity framework provides a systematic source of modified Lyapunov functionals and commutator arguments [R1]. Its transfer is especially promising when transport couples undamped directions to genuine dissipation. It is not a universal mechanism that stabilizes every MHD equation.

**D1 completion criterion:** improve a named baseline bound at the same model and data. Report the comparison, the constants and the remaining boundary/tail/regularity assumptions.

## 5. D2: relative entropy in a heated, open system

Use a reference profile \(\bar U\) chosen for the thermal operating problem. For a convex entropy density \(h\), a typical relative functional is

$$
\mathcal H(U\mid\bar U)
=\int_\Omega\big[h(U)-h(\bar U)-Dh(\bar U)\cdot(U-\bar U)\big]w\,dx.
$$

The variables, nonnegative weight \(w\), coercivity region and thermodynamic meaning must be specified. A norm-coercivity conclusion needs the corresponding positive lower bounds and convexity hypotheses. Different thermal and MHD models require different functionals; the expression alone proves nothing about their evolution.

Derive the full balance from the actual equation. Keep dissipation, heating, fusion source, radiation, transport coefficients, wall exchange and reference-profile residual terms. A closed equilibrium entropy identity cannot be copied into a driven burn problem with those terms dropped. The target might be an estimate of the form

$$
\mathcal H'\le-\kappa\mathcal H+\mathcal R(t),
$$

but the sign and value of \(\kappa\), and the meaning of \(\mathcal R\), must be produced. A nonuniform or time-dependent reference adds terms that need control. Entropy control is usually integrated; preserve pointwise lower/upper temperature barriers or prove the additional regularity/interpolation that yields the desired pointwise conclusion.

There is direct deterministic precedent. Villani's Theorem 53 treats conditional convergence for periodic compressible Navier–Stokes. It assumes global smoothness, uniform all-order derivative bounds and positive lower bounds on density and temperature; it does not prove those assumptions [R1, §16]. This supports using the method, without implying that global MHD regularity or sustained hot operation follows.

**D2 completion criterion:** an identity with correct source and boundary signs, a useful estimate in a named norm, and a demonstrated contribution to an existing thermal error bound or operating margin. An equilibrium relaxation theorem alone is insufficient.

## 6. N2: add the smallest useful deterministic correction

Potential corrections include a specified nonlocal heat-flux closure, pressure anisotropy, a prescribed wave perturbation in orbit dynamics, a selected kinetic species, or a kinetic response coupled to a fluid background. These are choices to evaluate, not commitments to implement every model.

For each proposed correction record:

1. The missing mechanism and the observable it may change.
2. The regime and why the simpler model plus a justified allowance is insufficient.
3. The corrected equation, conserved quantities, boundary data and energy exchange.
4. The comparison or error estimate that could establish the correction's value.
5. The cost and the remaining omissions.

The kinetic distribution should be introduced only if its extra velocity-space information matters. A deterministic fluid moment model with a justified closure may suffice. Hammett–Perkins provides an instructive precedent: a moment closure approximates Maxwellian kinetic linear response and Landau damping, with one-dimensional and slab instability comparisons. That source does not establish a general nonlinear stellarator error bound [R2].

For a chosen kinetic extension, useful methods include macro–micro decomposition, weighted velocity estimates, collision-invariant projections, entropy production and electromagnetic energy cancellation. Zhang uses hypocoercive estimates in a specifically scaled two-species Vlasov–Maxwell–Boltzmann problem, obtaining an incompressible viscous/resistive MHD limit. Its hypotheses include small Maxwellian perturbations, equal masses, opposite charges of equal magnitude, hard Boltzmann collisions, periodic geometry and normalized data including zero mean magnetic field. It is not a reactor-wall or electron–ion Coulomb theorem [R3].

Arsénio–Saint-Raymond supplies a broader electromagnetic-fluid-limit framework, with a rigorous part conditional on the appropriate renormalized kinetic solutions [R4]. These sources can provide individual estimates without turning their full limit theorems into PlasmaLean milestones.

**N2 stop rule:** stop expanding the model when the named decision is adequately resolved. If a correction improves a toy regime but does not transfer to the target, record that limitation rather than continuing automatically toward a full kinetic reactor simulation.

## 7. Mixing methods and Deng's work: useful, conditional sources

Mouhot–Villani's nonlinear Landau damping work is deterministic. It combines phase mixing, transport-adapted norms and nonlinear-echo control near suitable homogeneous stable Vlasov states in analytic or specified Gevrey settings [R5]. Its decay concerns appropriate macroscopic response; collisionless phase mixing is not collisional relaxation to a Maxwellian.

For an existing MHD or transport problem, D4 should first identify the transport mechanism, the dissipative directions and neutral modes. Only then ask whether a mixing estimate improves the needed observable or stability bound. A general three-dimensional toroidal damping claim is not a present deliverable.

Deng–Hani–Ma's hard-sphere-to-Boltzmann and fluid derivations remain reference material for correlation control, collision-history organization and composition of approximation errors [R6–R7]. The fluid corollary concerns well-prepared near-Maxwellian data and assumes a smooth fluid solution. Hard-sphere gas scaling is not Coulomb plasma scaling. These results do not supply a ready-made MHD stability estimate or a Gaussian stochastic field centred on MHD.

Their techniques could still help a selected deterministic comparison: for example, organizing accumulated approximation errors or extracting a needed correlation bound from an actually applicable particle model. The transfer must end in a named lemma with checked hypotheses. General resemblance is a research analogy, not an established technique improvement. Independent Monte Carlo trajectories do not require propagation-of-chaos machinery merely because they are called particles.

## 8. N3: keep the decision and the evidence precise

For an upper-limit decision about a scalar observable, a possible certificate is

$$
Q_{\rm computed}+\Delta_{\rm num}+\Delta_{\rm input}
 +\Delta_{\rm model}\le Q_{\max}.
$$

Each term must refer to the same candidate, scenario, physical quantity and interval. Avoid double counting. A worst-case input envelope is deterministic; a probability law for the inputs creates a different claim, treated in the companion note. For simultaneous probabilistic bounds, combine confidence levels by a justified rule. Unknown model uncertainty cannot be replaced by zero.

Verification, validation, sensitivity and uncertainty are distinct parts of evaluating a fusion prediction [R8]. A theorem about supplied bounds can be formally proved even when the supplied model envelope is empirical; its practical interpretation must retain that provenance.

| Finding | Allowed conclusion |
| --- | --- |
| A sufficient theorem hypothesis fails | That theorem does not certify this case. |
| A proof does not close, or its upper bound is too large | The certificate is inconclusive; no lower bound on the actual error follows. |
| A neglected term may be comparable to retained terms | Targeted investigation is warranted; output sensitivity and possible cancellations remain relevant. |
| A controlled discrepancy changes the decision after uncertainty accounting | Evidence that this model is inadequate for this observable and regime. |
| A limiting PDE loses regularity | Reassess the approximation and continuation claim; this alone does not prove microscopic physical failure. |

The first N3 deliverable is an applicability record and a conservative arithmetic decision lemma. The substantial scientific contribution comes from producing its inputs, especially N1's defect and stability estimates.

## 9. Crosswalk and first deliverables

The identifiers below supplement rather than renumber the existing plan. References to K3 here mean **§12 K3**, not earlier historical KAM milestones with the same label.

> **Editorial note (26 October 2026).** The identifiers "§12 D0–D4", "§12 K0–K6" and "§12.10" refer to a version of the implementation plan that was not supplied; they do not exist in [the current plan](../implementation-plan.md). The nearest current equivalents are the evidence gates E0–E8 (plan §11.2), the deterministic additions N1–N3 and probabilistic items P1–P4 (plan §12), and the phases of plan §10. No mapping of individual D/K items to these is implied; the D/K labels below are kept only as written.

| New note item | Existing plan destination | First reviewable deliverable |
| --- | --- | --- |
| N1 | §12 K0/K3; E2/E3 and E5/E6 as applicable | One exact projected error equation, produced residual/defect bounds and an observable transfer theorem. |
| N2 | §12 K1/K4/K6, only when activated | One minimal correction with a controlled same-observable comparison. |
| N3 | §12 K0/K3 and §12.10 | Candidate-specific evidence record, decision margin and failure classification. |
| D1 | §12 D1 (unsupplied plan version); T9/E2/E3 | Modified-energy pilot with one positive fixture, one neutral-mode rejection fixture and a destination-model improvement. |
| D2 | §12 D2 (unsupplied plan version); T3/E5/E6 | Correct driven relative-entropy identity and a useful thermal estimate. |
| Mixing | §12 D4 (unsupplied plan version) | A feasibility result identifying the mechanism and obstruction before a larger proof effort. |

Suggested formal interfaces, with names treated as proposals, are `ProjectedModelDefect`, `ModifiedEnergyBound`, `ObservableErrorBound` and `DecisionMarginCertificate`. Each must be accompanied by a producer from the stated equations or a clearly labelled external assumption. Merely assuming the desired defect bound or dissipation law and proving an arithmetic consequence is not completion of N1 or D1.

Proceed with one D1 or D2 pilot and one targeted N1/N3 adequacy question alongside the existing G1/G2 programme. Add N2 only when that question needs it. Preserve negative fixtures and reject unsupported transfers early.

## References

- **[R1]** Cédric Villani, [Hypocoercivity](https://arxiv.org/abs/math/0609050), Memoirs AMS 202 (2009), no. 950; [full text](https://arxiv.org/pdf/math/0609050), especially §16, Theorem 53.
- **[R2]** Gregory W. Hammett and Francis W. Perkins, [Fluid moment models for Landau damping with application to the ion-temperature-gradient instability](https://w3.pppl.gov/~hammett/gyrofluid/papers/1990/Hammett_90_PRL_Landau_fluid_corrected.pdf), Physical Review Letters 64 (1990), 3019–3022; corrected author-hosted version.
- **[R3]** Xu Zhang, [From two species Vlasov–Maxwell–Boltzmann system to magnetohydrodynamics system](https://arxiv.org/abs/2104.01843), v2 (2021); [full text](https://arxiv.org/pdf/2104.01843), §§1–3 and Theorems 3.1/3.4.
- **[R4]** Diogo Arsénio and Laure Saint-Raymond, [From the Vlasov–Maxwell–Boltzmann System to Incompressible Viscous Electro-magneto-hydrodynamics, Volume I](https://ems.press/books/emm/166), EMS (2019).
- **[R5]** Clément Mouhot and Cédric Villani, [On Landau damping](https://arxiv.org/abs/0904.2760), Acta Mathematica 207 (2011), 29–201.
- **[R6]** Yu Deng, Zaher Hani and Xiao Ma, [Long time derivation of the Boltzmann equation from hard sphere dynamics](https://arxiv.org/abs/2408.07818).
- **[R7]** Yu Deng, Zaher Hani and Xiao Ma, [Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory](https://arxiv.org/html/2503.01800v1), especially Theorems 1 and 2.
- **[R8]** P. W. Terry et al., [Validation in Fusion Research: Towards Guidelines and Best Practices](https://arxiv.org/abs/0801.2787), Physics of Plasmas 15 (2008), 062503.
