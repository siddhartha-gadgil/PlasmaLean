# Contributing to PlasmaLean

The project needs mathematical and physical review as well as Lean development. A useful
contribution can be a precise theorem with a paper proof, a counterexample to a proposed
implication, a clearer explanation of an existing verified result, or a reproducible numerical
candidate. Lean experience is not a prerequisite for those contributions.

Choose one concrete target and identify the model and theorem it advances. The
[implementation plan](notes/implementation-plan.md) is the plan of record; the
[progress ledger](progress/README.md) records subsequent results. Older discovery notes retain
their history, so compare proposed targets with the current source before starting.

## Working with agents

Much of the work is done with coding agents using the project skills (`.agents/skills/`, entry
point `plasmalean-develop-theory`). Open a checkout and say **`start`**: the agent strictly audits
the existing code (every kernel declaration first), records the audited commit and findings, and
offers ready choices. Then use **`status`**, **`work on G-…`/`Q-…`/`N-…`** (or a topic) for one
work unit, or **`keep working`** for autonomous mode.

Goals, questions and research notes form the **research graph** in the
[implementation plan](notes/implementation-plan.md); new notes follow the
[note template](notes/note-template.md). **Lean is the validity gate**: only a compiled declaration
(standard axioms) is an established dependency; everything else stays conditional. The process
exists to prevent **research drift** (losing the question, repeating abandoned approaches,
silently changing definitions) and **validity drift** (treating a plausible argument, sampled
computation or cited result as checked). Human contributions enter the same graph: a theorem with a
paper proof, a counterexample or a source can be recorded as a note or question and picked up by
an agent or a person.

## Three reading paths

### 1. Understand what a verified statement means

Read the [model contracts](notes/formalization/00-model-contracts.md), then the short
[force-balance kernel](PlasmaLean/Kernel/Equilibrium.lean) and its
[sanity examples](PlasmaLean/Sanity/Equilibrium.lean). Continue with
[neutral modes](PlasmaLean/Sanity/NeutralMode.lean),
[a non-confining probe field](PlasmaLean/Sanity/ProbeEscape.lean), and
[common-witness composition](PlasmaLean/Bridge/Contracts.lean).

These examples distinguish a correct deduction from a stronger physical interpretation.
For an advertised result, locate the Lean declaration and read its hypotheses before reading
the proof. In particular, distinguish an assumed solution from a constructed solution, a
reduced stability diagnostic from nonlinear stability, and a model trajectory from a full
particle orbit.

### 2. Follow one complete geometric result

Start with the [rational stellarator model](notes/theory/first-stellarator-rung.md) and the
[KAM strategy](notes/theory/kam-route.md). Follow the present code through:

1. [Exact vacuum field](PlasmaLean/Design/RationalStellarator.lean).
2. [Diophantine estimates](PlasmaLean/Theory/KAM/Diophantine.lean) and
   [cohomological equation](PlasmaLean/Theory/KAM/Cohomological.lean).
3. [Concrete exact KAM torus](PlasmaLean/Design/KamTorusAExact.lean), whose hypotheses are
   discharged by the preceding certificates.
4. [Torus trapping](PlasmaLean/Theory/Fields/TorusTrapping.lean) and
   [global field-line existence](PlasmaLean/Design/RationalStellaratorFieldLines.lean).

Write a short ordinary-mathematics account of one link, including the quantitative constants
and exact hypotheses. Such an account is a valuable contribution even when the Lean proof
already exists. For particle dynamics, continue with the
[Littlejohn model](PlasmaLean/Theory/Kinetic/GuidingCentreLittlejohn.lean) and the scope stated in
[the passing-particle theorem](PlasmaLean/Design/RationalStellaratorGCMuConfined.lean).

### 3. Contribute a numerical certificate or Lean proof

Read [verified-numerics contracts](notes/formalization/05-verified-numerics.md), then
[polynomial interval checking](PlasmaLean/Certificates/PolyInterval.lean) and the
[radii-polynomial theorem](PlasmaLean/Certificates/RadiiPolynomial.lean).

The intended chain is: an untrusted search proposes data; a proved checker validates bounds,
coverage and remainders; an analytic theorem converts the bounds into a continuum conclusion.
Document that whole chain. A dense numerical grid alone is not a uniform bound. An exact
certificate for an approximate model also needs a separate model-error estimate before it
supports a claim about a more detailed model.

## Starting points for geometers

The following are proposed tasks, not claims that the corresponding research problems have
already been solved. Begin with the small deliverable; agree on a larger extension after it
has been reviewed.

| Background | Small first deliverable | Larger target and existing entry point |
| --- | --- | --- |
| Topology | Explain exactly how the present invariant torus separates the trapping region and where uniqueness and compactness enter; give an example showing why tangency alone without the required regularity is insufficient. | Extend the profile-specific geometric interface to suitable embedded separating tori, reusing [invariant barriers](PlasmaLean/Theory/Fields/InvariantBarrier.lean) and [torus trapping](PlasmaLean/Theory/Fields/TorusTrapping.lean). State the embedding, separation and boundary hypotheses explicitly. |
| Topology and symplectic geometry | Trace one flux/exactness identity used in KAM and its period conventions. | Generalize the exactness and obstruction calculations to additional coil fields or torus families; begin with the [KAM route](notes/theory/kam-route.md) and [flux-period note](notes/theory/flux-surface-holonomy.md). |
| Differential geometry | Derive the symmetry commutators for one selected PDE, recording the metric, volume form, boundary and constitutive coefficients that the symmetry must preserve. | Establish a genuine invariant ansatz or a quantitative defect estimate. Quasisymmetry of magnetic-field strength does not by itself establish invariance of the full MHD equations; see the [regularity plan](notes/bkm-regularity-and-perelman-burn-bounds.md). |
| Differential geometry and PDE | Give a precise counterexample showing that a pointwise pressure upper bound does not imply force balance for the bounded pressure. | Replace the present [transport pressure budget](notes/theory/transport-mhd-coupling.md) by pressure equality for a steady solution, or by a proved field-response/force-residual estimate for an evolving solution. |
| Complex analysis or complex geometry | Prove a bound for a small symmetric group of coil segments that preserves cancellation and improves the sum of individual absolute bounds. | Sharpen complexified Biot-Savart estimates and anisotropic Fourier tails enough to meet a KAM smallness budget; see the current end of [coil-KAM status](notes/theory/coil-kam-status.md), [BiotSavartComplex](PlasmaLean/Theory/Fields/BiotSavartComplex.lean), and [StripPaleyWiener](PlasmaLean/Theory/KAM/StripPaleyWiener.lean). |
| Geometric analysis | Extract one continuation or coercivity theorem from its primary source, with the exact model, spaces, boundary conditions and every quantitative hypothesis. | Close one verified continuation or stability estimate for a specified model. An abstract certificate must not assume its intended conclusion as a field; use the [regularity plan](notes/bkm-regularity-and-perelman-burn-bounds.md). |

For complex-analysis work, several foundational pieces already exist:
[two-variable Cauchy estimates](PlasmaLean/Theory/KAM/CauchyTwoVar.lean),
[holomorphic Fourier sums](PlasmaLean/Theory/KAM/FourierSumHolo.lean), and
[analytic composition](PlasmaLean/Theory/KAM/AnalyticComposition.lean). The immediate bottleneck
in the coil-KAM example is quantitative sharpness, not merely the existence of holomorphic
extensions. A spectral curve or other auxiliary complex structure becomes useful only after
its relation to a realizable three-dimensional field and the required estimates is established.

## Result card for a theorem, numerical result or proposed task

Include this information in the note or pull-request description. It can be brief for a small
lemma, but the model and quantifiers must be unambiguous.

```text
Title and status: proved / conditional / numerical observation / research target
Exact Lean declaration(s), or proposed statement:
Model, domain, boundary conditions, units and time interval:
Candidate / equilibrium / trajectory shared with other claims:
Input assumptions, with primary sources and theorem/equation locators:
Conclusion, including all quantifiers and parameter ranges:
Existence: proved here / proved elsewhere / supplied as a hypothesis
Physical reductions or empirical data still supplied:
Proof outline and dependencies:
Positive example and relevant failure case:
Numerical generation command, dependencies, seeds and artifact hashes, if applicable:
Verification command and observed resource requirements:
Remaining bridge to the next practical claim:
```

## Review the model and the proof separately

**Mathematical/model review** checks that the statement represents the intended problem, that
the cited theorem has the right hypotheses, and that fields, pressure, geometry and operating
parameters refer to the same candidate. It checks units, approximation errors, quantifiers,
boundary conditions, and whether assumptions can actually be met.

**Formal review** checks the definitions, theorem statement, dependency closure and proof,
including the bridge from generated numerical data to the quantities in the theorem. Lean
checking and the axiom audit establish the formal deduction. They do not establish the physical
accuracy of a supplied model or empirical law.

Keep the domain kernel small, but make every modeling assumption discoverable wherever it is
defined. New kernel laws or model reductions should come with an ordinary-language statement,
a source or explicit modeling rationale, and useful consistency/failure examples. When a
research attempt fails, record the obstruction and correct the active statement; do not leave
a refuted formula as the current specification.

## Reproducing numerical searches

Committed Lean certificates can be checked without trusting their numerical generators.
Regenerating them is a separate task. Several current scripts still use session-specific
temporary inputs or absolute paths, so portability improvements are useful contributions.

For a generator, provide pinned Python dependencies, configurable input/output paths, the
initial data or a reproducible way to obtain them, and commands that work from a clean checkout.
Record precision, truncation, rounding direction, tail bounds and output hashes. Include a
small example whose entire search-to-certificate chain can be reproduced cheaply before
documenting the large calculation. Avoid depending on an undocumented file in `/tmp`.

## Build and check

Use the Lean version in [lean-toolchain](lean-toolchain) and the pinned dependency revisions in
[lake-manifest.json](lake-manifest.json). From the repository root, build a small target first:

```sh
scripts/setup.sh --no-build        # elan if missing, the pinned toolchain, the Mathlib cache
lake build PlasmaLean.Kernel.Equilibrium PlasmaLean.Sanity.Equilibrium
```

For an integrated change, the standard checks are:

```sh
lake build
lake env lean scripts/check_axioms.lean
node scripts/generate_handbook.mjs
node scripts/check_site.mjs
```

The axiom audit imports `PlasmaLean` and checks its loaded project declarations. An optional
module outside that import closure needs an explicit build and audit import; document those
commands with its result. Use targeted imports while developing. Large generated certificates
can take substantial CPU time and several gigabytes of memory per process; consult their
progress reports before launching many parallel jobs. Report the checks actually completed.

Update the relevant note and progress entry when a target is completed or refuted. Keep the
headline claim and result card consistent with the precise theorem, and let the maintainer
integrate the change into the plan of record.
