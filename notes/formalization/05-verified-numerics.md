# Verified numerics and continuous certificates

External computation proposes candidates. A small proved checker and analytic soundness theorems turn selected candidates into mathematical evidence. The chapter was written on 12 October 2026 as a development specification, before any checker existed. Its exposition still states the method. Many of the checkers now exist, and a status layer, last revised on 30 October 2026, records what is compiled, what remains open and what was corrected. Sources for the status layer are the [implementation plan](implementation-plan.md) (the stellarator contract, the research graph and the §13 log), the [30 October progress report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md), [`Certificates/README.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Certificates/README.md) and [Workstation.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/Workstation.md).

## Contents

- [Status in PlasmaLean and the stellarator contract](#status-in-plasmalean-and-the-stellarator-contract)
- [The certificate toolkit and the no-decide policy](#the-certificate-toolkit-and-the-no-decide-policy)
- [Exact inputs and interval arithmetic](#exact-inputs-and-interval-arithmetic)
- [Continuous geometry and quadrature](#continuous-geometry-and-quadrature)
- [Finite-dimensional certificates](#finite-dimensional-certificates)
- [Continuum equilibrium validation](#continuum-equilibrium-validation)
- [Continuum stability validation](#continuum-stability-validation)
- [KAM and orbit certificates](#kam-and-orbit-certificates)
- [Uncertainty and certificate identity](#uncertainty-and-certificate-identity)
- [Laptop budget and the workstation pipeline](#laptop-budget-and-the-workstation-pipeline)
- [Theorem backlog](#theorem-backlog)

## Status in PlasmaLean and the stellarator contract

Verified numerics serves every clause of the [stellarator contract](implementation-plan.md#the-stellarator-contract-30-october-2026). Under the contract a candidate must satisfy:

- C1, a current-free rotational transform;
- C2, omnigeneity for thermal particles;
- C3, MHD stability at finite β;
- C4, existence;
- C5, thermal performance on the same candidate.

Each of these needs certified numbers about a concrete field. Present uses:

- **C1 and C4 in vacuum.** The a posteriori KAM certificate for torus A of the exact rational vacuum field is the main heavy certificate (`torusA_exact`, `rationalStellarator_confined_forever_exists`). The planned Dommaschk QA field (Q-16) reuses the same pipeline for further tori, for ι ≥ ι_min and for Boozer and ε_QS diagnostics.
- **C2.** Nothing is certified yet. Q-19 (bounce-averaged drift and ε_eff on the rational field) and Q-16 need validated bounce integrals and Fourier bounds on certified surfaces. The toolkit below provides the arithmetic; the C2 definitions (Q-21) do not exist yet.
- **C3.** Certificates exist only on test beds that fail C1: the Landreman family-2 Mercier band and Solov'ev ballooning. The checkers are designed to transfer to a current-free equilibrium.
- **C5.** Bosch–Hale windows (`BoschHaleFine`) and the burn-window arithmetic are certified. The transport solution itself is supplied.

All certificate entry points use the standard axioms only. `scripts/check_axioms.lean` covers 122 entry points. `scripts/check_axioms_heavy.lean` covers the on-demand tops, including `CoilKamCert`, and since audit M-4 it fails on any non-standard axiom.

## The certificate toolkit and the no-decide policy

**Pattern.** Every certificate format consists of four parts:

- exact data;
- a checker, or an inductive certificate predicate;
- a soundness theorem: certificate ⇒ the mathematical statement for every real point, mode or cell;
- a proof-term builder.

Large checks are built as explicit proof terms whose leaves are small kernel facts. This is the SubsetSum pattern (reference example [`PlasmaLean/SubsetSum.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/SubsetSum.lean): an inductive predicate, a computable checker characterized by `fun_induction`/`grind`, and a `meta` builder). **New code uses no `decide` of any kind.** `eval_decide` and `fiv_decide` are evaluation certificates of `decide p`; the tactic `decide` itself is not run.

All the modules below are in `PlasmaLean/Certificates/` and in the default build, unless another location is given.

| Tool | Module | Use |
| --- | --- | --- |
| `kernel_fact` | `KernelFact` | Closed side conditions, conjunctions and list quantifiers, as explicit proof terms |
| `bool_cert` (`BCert`) | `BoolCert` | A Boolean checker over lists, unfolded one definition or matcher at a time, with one step per item |
| `eval_cert`, `eval_decide` (`ECert`) | `EvalCert`; builder in `PlasmaLeanMeta/EvalCert` | Evaluation of a closed term (balls, intervals, rationals, polynomials, records, recursion): one leaf per operation, with shared subterms evaluated once |
| `fiv_cert`, `fiv_decide` | `EvalCertFIv` | The same, with the fixed-point interval operations `FIv` as leaves |
| `kron_proof`, `kron_lt` (`SCert`, `PCert`) | `KronProof` | Kronecker ball checks of the KAM families (signed images, digit reading in blocks of 2⁹ rows) |
| `kron2_proof` (`PCert2`) | `KronProof2D` | Two-dimensional Kronecker checks (Torus and NegTorus families, the weighted KAM checks `wcheck_*`) |
| `l1kron_cert` (`DCert`) | `DigitSumCert` | Kronecker digit sums `l1Kron` |
| `icc_cert`, `icc_close` | `IccListCert` | Finite sums and quantifiers over `Finset.Icc` as list computations |
| `fampack_cert` (`FPCert`) | `FamPackCert` | Kronecker images of stored families, row by row (`famPack_eq_of_cert`) |
| `f2_arc_cert` | `Design/LandremanFamily2ArcCert` | The 136 outer-arc quadratures of Landreman family 2 (Q-6, done 30 October) |
| `oned_cert` | `Design/LandremanFamily2Quad` | The family-2 one-dimensional quadratures, with fast enclosures as leaves |
| `line_cert` | `Design/PolygonCoilCubicLineCert` | Per-segment line certificates of the cubic polygonal-coil cover |
| `bl_cert` | `Design/SolovevBallooningEvalCert` | Solov'ev ballooning boxes |

**Legacy `decide +kernel` (Q-12, audit M-5).** Phase 16 has been replacing the old whole-checker `decide +kernel` evaluations with these certificates. The count of lines containing `decide +kernel` in the default build fell 1,407 → 690 → 475 → 381 → 297 over stages 6–9. It then fell to **130** after the 136 Landreman outer arcs were converted to `f2_arc_cert` (Q-6). **1,971** lines remain overall, most of them in frozen on-demand families. Audit L-1 corrected an earlier slide figure of "2,507 / 690", which was a stage-6 count. The remaining default-build items are:

- the `NearAxisQAAveraged` parts;
- the fast side `famTB − famO`;
- `nodeFin` and `famL1` leaves;
- `KamTorusACheck`, `SurrogateCheck` and `FrameCheck`.

Some on-demand Adm modules use `decide_cbv`.

**Opaque-leaf audit.** A `kernel_fact` leaf can be as opaque as `decide` when it is one big `Eq.refl` on a whole checker. `scripts/audit_kernel_fact.py` walks the built proof terms and classifies each leaf:

- class a: literal facts;
- class a-data: data definitions without recursion;
- class b: a recursive PlasmaLean definition is reached.

With `--time`, it also times each class-b leaf on its own. Results:

- **Default build:** 6,098 class-b leaves, none taking 0.1 s or more (stage 8 had 34), about 20 s of opaque kernel time in total.
- **Overall:** 18,518 class-b leaves; the 64 leaves of 0.1 s or more are all in the frozen on-demand Ew and Mu2–5 chains.

**Low-memory kernel checks.** The memory of the KAM-family checks is in the kernel: whnf caches keep every big intermediate number. Elaboration and literals are not the cost. Three changes fixed this (`KronLowMemCompute`, `KronBallLowMem`):

- sign–magnitude integers;
- per-row masks placed by divide and conquer;
- row block sums by two multiplications.

The peak per process fell from 8.8 GB to 4.3 GB. Bridge lemmas re-prove the original statements, so no theorem changed.

## Exact inputs and interval arithmetic

Use rational/dyadic endpoints and a semantic predicate `x ∈ [l,u]` with `l≤u`. Prove soundness of arithmetic, comparison, powers, roots, and transcendental enclosures. Exclude zero for reciprocals. Rational arithmetic avoids floating-rounding trust initially; faster arithmetic requires its own soundness bridge.

Decode a decimal token as the exact rational it denotes, or as an uncertainty interval if it represents a measurement/rounded quantity. A float converted to a real without a declared interpretation does not identify a physical coefficient.

For a checker `check` prove

$$
\operatorname{check}(c)=\mathrm{true}
\quad\Longrightarrow\quad
\operatorname{Claim}(\operatorname{decode}(c)).
$$

Keep all semantics, domain coverage, and remainder obligations in this theorem. Treat results returned by Python, CUDA, SMT, an optimizer, or an external interval package as certificate data rather than assertions accepted by Lean.

Inspect axioms and execution trust of certificate entry points. Prefer proof-producing arithmetic and a kernel-checked soundness theorem. [Rump](09-literature.md#validated-computation-and-analysis) is the general validated-computation reference.

**Status in PlasmaLean.** Three arithmetic cores are compiled in the default build:

- **Exact rational intervals** (`Certificates/RationalIntervals`): `RationalInterval`, with `check_sound`, `add_sound`, `neg_sound`, `mulNonneg_sound`, and exact decimal decoding (`decodeDecimal`). There is no text parser for certificate files; data enters as Lean literals emitted by the generators.
- **Fixed-point intervals** `FIv` with scale 2³² (`Certificates/ValidatedQuadrature`). The containment theorems `mem_add`, `mem_mul`, `mem_inv` and `mem_sqrt` cover the arithmetic. A reciprocal of an interval containing 0 is rejected (`fixture_inv_rejected`).
- **Validated transcendental functions** (`Certificates/ValidatedTrig`, `ValidatedTrigFast`): arctan, arcsin, cosh and sinh on fixed-point enclosures, for example `atanTabN_check`.

Ball arithmetic in the strip algebra (`KronBall*`) carries the KAM computations. Every Python oracle in `scripts/` proposes data only, and every certificate is re-checked by the Lean kernel. The axiom scripts cover the "inspect axioms" requirement above.

## Continuous geometry and quadrature

For a Fourier curve `c(t)`, bound `c,c',c''` on every parameter box. Prove regularity `|c'|≥v_*>0` and use

$$
\kappa(t)=\frac{|c'(t)\times c''(t)|}{|c'(t)|^3}.
$$

For disjoint coils/surfaces, cover the entire product parameter domain and bound squared distances. For self-clearance, distinguish neighboring parameters from genuinely separate curve segments and use a tubular-radius/reach argument where necessary.

A simple between-sample lemma is already useful: if `c₁,c₂` have derivative bounds `L₁,L₂`, their parameter grids have fill distances `h₁,h₂`, and every grid-pair distance is at least `d₀`, then

$$
|c_1(t)-c_2(s)|\ge d_0-L_1h_1-L_2h_2.
$$

Prove grid coverage and the mean-value bounds. The same idea certifies a scalar inequality from sampled values plus a Lipschitz bound. Sampling without those ingredients is not a proof.

For integrals use interval quadrature with explicit remainder, or analytic bounds on Fourier tails. For `‖f‖_ν=Σ_k|f_k|ν^{|k|}` with `ν>1`,

$$
\sum_{|k|>N}|f_k|\le\nu^{-N}\|f\|_\nu.
$$

Derivatives require weighted factors `|k|^j` and generally a narrower analyticity strip/weight. Prove convolution-algebra and derivative-loss estimates before using them in a PDE proof. A finite Fourier polynomial has no unknown coefficient tail, but the exact equilibrium validated near it generally does.

For Biot–Savart, prove a positive distance to conductor sources before using integrand derivative and quadrature bounds.

**Status in PlasmaLean.**

- **Between-sample lemma.** It is compiled as `clearance_of_lipschitz_cover` (`Theory/Geometry/ParametricBounds`). The surface versions are `le_of_grid` and `GridBound.sound` (`Theory/Geometry/SurfaceCover`). The vacuum demonstrator uses them for coil and tube clearance (`coil_clearance`, `manufactured_tube_clearance`).
- **Validated quadrature.** Cell sums with sound remainders are in `integral_mem_sumIv` and `cell_bounds_of_lipschitz` (`Certificates/ValidatedQuadrature`). `ValidatedQuadratureArcs` treats periodic integrands with a sharp peak. These carry the Solov'ev Mercier quadrature and the Landreman family-2 quadratures.
- **Fourier tails and algebra.**
  - `WeightedEll1`: ℓ¹_ν(ℤ) as a Banach algebra.
  - `ConvAlgebra`: ℓ¹(ℤ) and its exponential.
  - Strip tail sums: `hasSum_tailZ` (`Theory/KAM/StripPaleyWiener`).
  - From coefficient equations to classical solutions: `classical_of_coeff` (`Certificates/FourierRegularity`).

  All of these are one-dimensional or two-dimensional Fourier only. A 3-D Fourier–Chebyshev algebra is missing (see the Q-16 analysis in the [quasisymmetric-solution note](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/quasisymmetric-solution.md)).
- **Biot–Savart.** The field bound `filamentField_bound` requires an explicit source distance.
- **Not done:** curvature and self-clearance certificates for Fourier coils, and embedded winding packs.

## Finite-dimensional certificates

For a symmetric exact matrix `A`, validate an exact factorization

$$
A=LDL^\mathsf T,\qquad D_{ii}>0,
$$

with diagonal `D` and invertible `L`. This proves positive definiteness. For a claimed quantitative margin use a factorization of `A-cM`, where `M` is the positive inertia/Gram matrix.

If a numerical matrix approximates an exact matrix, prove the enclosure or form error and subtract it from the margin. A floating Cholesky success flag is not a certificate.

For nonlinear finite systems validate a contraction/Newton/Krawczyk-style inclusion with its precise existence and uniqueness theorem. Handle gauge and phase symmetries so that the intended Jacobian/inverse is nonsingular. A root of projected equations is only a projected solution until the continuum/tail conditions are supplied.

**Status in PlasmaLean.**

- **Polynomials.** Exact positivity certificates on intervals are in `Certificates/PolyInterval`.
- **Block positivity.** The two-block checker `BlockCertificate` (`Certificates/BlockBounds`) is sound (`BlockCertificate.sound`). It accepts the sanity example of the next section, (a, b_*, γ, c) = (5, 2, 2, 1) (`BlockCertificate.example_accepted`), and rejects a larger coupling or a zero margin. The real-variable lemma is `two_block_margin` (`Theory/Stability/BlockBounds`).
- **Scalar Newton validation.** `validated_scalar_root` validates x² = 2 on [1, 2].
- **Not in the toolkit:** a general LDLᵀ checker for symmetric matrices.

## Continuum equilibrium validation

Let `X` be a complete Banach space, `F:X→X` the gauge-fixed continuum equation, `x̂` a candidate, and `A` a bounded linear approximate inverse. Require `F` to be continuously Fréchet differentiable on an open neighborhood of the closed ball used below, so its derivative bound yields a Lipschitz bound along segments. Put

$$
T(x)=x-AF(x).
$$

On the closed radius-`r` ball around `x̂`, prove:

$$
\|T(\hat x)-\hat x\|\le Y,\qquad
\sup\|DT(x)\|\le Z(r)<1,\qquad
Y+Z(r)r\le r.
$$

Then `T` has a unique fixed point in that ball. To conclude `F(x)=0`, additionally prove `AF(x)=0 ⇒ F(x)=0`, for example by injectivity of `A`. Uniqueness is in the certified ball and gauge; it is not global uniqueness of equilibria.

With `Z(r)=Z₀+Z₂r`, an admissible `r>0` satisfying

$$
p(r)=Y+(Z_0-1)r+Z_2r^2<0
$$

implies the required strict inequalities when the bounds are nonnegative and the map/domain hypotheses hold. One needs a negative value at a positive radius, not a “negative root.”

Include:

- finite modes and analytic infinite-tail bounds;
- boundary/interface residuals;
- flux/current/profile constraints;
- coordinate Jacobian and embedding control throughout the ball;
- regularity sufficient to interpret the resulting solution;
- approximate-inverse and derivative estimates in the actual norm.

The equilibrium operator may have derivative loss, small divisors, or lack a bounded inverse in the chosen space. In that case an elementary radii-polynomial argument may be unavailable. Explore an appropriate a posteriori KAM/Nash–Moser theorem, a weaker equilibrium class, or a restricted model; do not invent invertibility.

[Nakao–Plum–Watanabe](09-literature.md#validated-computation-and-analysis) and [Lessard's tutorial](09-literature.md#validated-computation-and-analysis) are entry points for validation methods. Transferring their machinery to full three-dimensional MHD is a research task.

**Status in PlasmaLean.**

- **The abstract theorems are compiled.**
  - `radii_polynomial_fixedPoint`, `radii_polynomial_zero` and `radii_polynomial_fderiv` (`Certificates/RadiiPolynomial`). The rejection fixtures `radii_polynomial_rejects_small` and `radii_polynomial_rejects_identity` check that the theorem does not accept bad inputs.
  - `local_fixedPoint` and `fixedPoint_equation` (`Certificates/Contraction`), the latter being the injectivity bridge from AF(x) = 0 to F(x) = 0. `zero_inverse_counterexample` shows that the bridge cannot be dropped.
- **Two continuum examples are validated** (default build):
  - `validated_bvp_classical`: a periodic nonlinear boundary-value problem with a classical C² solution.
  - `validated_slab_equilibrium`: a slab equilibrium.

  Neither is a stellarator equilibrium.
- **Small divisors.** For the stellarator the project used the a posteriori KAM route that the paragraph above recommends when invertibility fails. That route is described under [KAM and orbit certificates](#kam-and-orbit-certificates).
- **Full 3-D MHD.** Validating full 3-D MHD by a Newton–Kantorovich boundary-value formulation was assessed for Q-16 and judged not feasible on the laptop: a dense approximate inverse of about 5·10⁷ entries would be needed. The recommended route, an explicit Dommaschk vacuum field, moves the work to tori (see [06](06-coils-and-design.md)).
- **Finite β.** A finite-β current-free equilibrium (Q-20, via Q-14) has not been validated.

## Continuum stability validation

First validate an actual equilibrium `e` or carry the difference from a valid reference explicitly. Take a Hilbert energy space `V` and a proved orthogonal decomposition `V=V_N⊕V_tail`, so `‖u+v‖²_V=‖u‖²_V+‖v‖²_V`. Suppose the symmetric form satisfies

$$
q(u+v)=q_N(u)+2b(u,v)+q_{\rm tail}(v),
$$
$$
q_N(u)\ge a\|u\|^2,\quad
q_{\rm tail}(v)\ge b_*\|v\|^2,\quad
|b(u,v)|\le\gamma\|u\|\|v\|.
$$

If `a>0`, `b_*>0`, `γ≥0`, and `γ²<a b_*`, then `q(ξ)≥c‖ξ‖²_V`. One explicit margin is

$$
c=\frac{a+b_*-\sqrt{(a-b_*)^2+4\gamma^2}}2>0.
$$

For another decomposition/norm, prove `‖u+v‖_V≤C_d√(‖u‖²+‖v‖²)` and use margin `c/C_d²`. With ambient norms and only the triangle inequality, `C_d=√2` gives `c/2`. Convert the margin to the advertised norm before subtracting form errors.

A rational checker can avoid the square root by accepting a proposed `c>0` when `a-c≥0`, `b_*-c≥0`, and `γ²≤(a-c)(b_*-c)`. For an exact orthogonal two-block sanity example, `a=5`, `b_*=2`, `γ=2` and `c=1` satisfy these inequalities, and

$$
5x^2-4xy+2y^2=x^2+y^2+(2x-y)^2\ge x^2+y^2.
$$

This is finite block algebra; it supplies no missing MHD tail estimate.

This elementary block lemma is an early reusable theorem. For MHD, proving the tail bound in the correct space is the difficult part; ideal MHD is not a uniformly elliptic operator with an automatic increasing high-frequency spectrum.

Subtract rigorous form errors for coefficient enclosure, quadrature, geometry, and approximate-equilibrium replacement. If

$$
|q_e(\xi)-q_{\hat e}(\xi)|\le\varepsilon_{\rm eq}\|\xi\|_V^2,
$$

and every other nonnegative form-error bound is in the same norm, define `ε_tot=Σ_j ε_j`, including `ε_eq` once. The full-space bound is `q_e(ξ)≥(c_eff-ε_tot)‖ξ‖²_V`, with `c_eff=c` in the orthogonal case or `c/C_d²` otherwise. Require `c_eff>ε_tot`; separately exceeding each error is insufficient. Derive the equilibrium estimate from enough derivative/trace control of the validated solution; a small force residual alone is not such control.

Treat generalized eigenproblems with the actual mass/Gram form. Account for neutral modes and boundary/interface terms. Retain the label “finite-dimensional stability” if any continuum transfer ingredient is missing.

**Status in PlasmaLean.** The block lemma and its rational checker are compiled, with the sanity example above as a fixture (`block_example`, `BlockCertificate.example_accepted`). No MHD tail estimate is proved, so no all-mode continuum stability certificate exists for a 3-D equilibrium. The compiled stability results are local criteria or reduced forms, each with its reduction named; details are in [03](03-mhd-stability.md).

- Mercier: the Landreman family-2 band, with the Mercier index supplied (`family2_mercier_stable_derived`).
- Ballooning: the Solov'ev result `reactor_ballooning_all`, certified over 825 boxes; family-2 ballooning is reduced to one certificate (Q-3).
- Screw pinch: `stable_all_modes_equilibrium`. It covers every mode with m ≠ 0, with Newcomb's reduced form supplied. Audit M-3 corrected the earlier "all-mode" wording.

Under the contract every C3 certificate so far is on a test bed that fails C1. The certificate machinery is what is meant to transfer.

## KAM and orbit certificates

For a selected KAM theorem, prove regularity, symplectic/flux-preserving structure, nondegeneracy, residual bounds, and the infinite Diophantine condition. An interval containing an unknown frequency does not certify that every value in it is Diophantine. Use the theorem's frequency/parameter setup correctly.

For finite-time trajectories, enclose the full initial set and every time segment, bound the vector field/Jacobian on the enclosure, and prove the integration remainder and boundary separation. Distinguish numerical integrator error from guiding-centre/full-orbit model error.

**Status in PlasmaLean.**

- **Field-line KAM (vacuum, default build).** `torusA_exact` (`Design/KamTorusAExact`) certifies an exact invariant torus of the rational vacuum field `RationalStellarator.field (1/4)` from an a posteriori KAM theorem with explicit constants (modules `KamTorusA*`, `KamFlow*`, `Theory/KAM/*`). `rationalStellarator_confined_forever_exists` turns it into all-time confinement of field lines inside the torus. The rotation number (ι ≈ 0.137) is a specific number with a proved Diophantine condition, not an interval of frequencies, which respects the caveat above. This is the C1 + C4 evidence in vacuum.
- **Guiding-centre KAM.** The alpha results of [04](04-particles-and-transport.md) use tori of the guiding-centre field for explicit quadratic-irrational rotation numbers, for example (75 + √5)/562 in `alpha_gc_confined_forever_pm`. The Littlejohn model is supplied, and some families are on demand.
- **Coil-field KAM is blocked (Q-2).** The on-demand `CoilKamCert` proves only a vacuous residual bound: about 10⁹, against the roughly 10⁻³⁰ the smallness condition needs. See [06](06-coils-and-design.md).
- **Finite time.** Field lines are confined for 95 transits in the rational field (`rationalStellarator_confined`) and for 52 transits in a concrete polygonal coil field (`coil_stellarator_confined_concrete_N`, existence of the field line assumed). Near-QA passing alphas are confined for 0.19 s, off the axis. These results use covers plus invariant or defect bounds (`fieldLine_confined_of_defect`), not interval ODE integration. No validated ODE integrator is in the library, and no reduced-to-full-orbit error is certified.

## Uncertainty and certificate identity

A design certificate must identify geometry, coefficient serialization, species/profiles, material data version, field conventions, source commit, and checker version. A cryptographic hash can identify bytes but is not itself the theorem linking bytes to semantics; prove/use a well-defined decoder and attach the decoded value to the property.

Define the uncertainty set `U`, including correlations. For boxes, prove a finite box cover and each bound on the full box. An uncertainty parameter may change the equilibrium witness; use a validated branch or a parameter-wise existence theorem.

Monte Carlo confidence intervals require explicit probabilistic/statistical hypotheses and coverage theorems. They are not deterministic enclosures. Physical data intervals remain supplied assumptions unless their derivation is itself formalized.

**Status in PlasmaLean.**

- **Data in the statement.** Certificate data are Lean literals emitted by generators, and the decoded value is part of the theorem statement. For example, the polygonal-coil filaments are a literal list proved equal to their construction (`filsDLB_eq`). There is no hash-based identity layer.
- **Parameter uncertainty by covers.** `alpha_gc_confined_forever_robust` holds for every B₀R₀ ∈ [67.95, 69.99] T·m, with a torus that depends on B₀R₀. Physical constants enter as intervals, for example the alpha mass and the elementary charge.
- **Composition.** Common-witness composition exists as a framework (`Bridge/Contracts`) but is not instantiated for any candidate (audit L-12). The C1–C5 contract on one candidate (G-8) has no composed instance.
- **Probability.** No probabilistic statement is formalized (G-3 proposals only).

## Laptop budget and the workstation pipeline

**Budget.** Every Lean process should stay at or below 6 GB on the development laptop. Since 30 October every module with a recorded peak is within 6 GB. The one exception, `LandremanFamily2MercierStable` at 6.74 GB, was split into three modules with peaks of 1.40, 2.74 and 2.65 GB (`cellCheck_eq_of_pieces`). The individual peaks of the four `NearAxisQAAveraged` parts are not recorded. Audit M-2 corrected an earlier report that claimed the 6 GB target held everywhere before this split.

**Workstation.** Heavy untrusted numerics run on a workstation through `scripts/workstation/run.sh`, as do the first builds of large certificates. Examples of the numerics are KAM tori, Chebyshev families and ballooning oracles. Each run builds every module, measures CPU time and peak memory, checks axioms, and pushes a branch `workstation/<task>-<stamp>` with a laptop verdict:

- default build: peak ≤ 6 GB and at most 60 CPU-min;
- separate on-demand top module: peak ≤ 6 GB and at most 240 CPU-min;
- otherwise not merged.

The rule is that the final Lean must build on the laptop. On the laptop the skill `plasmalean-workstation-update` re-checks passing runs with `--verify-only`, merges them, and records them in [`workstation/REVIEWED.md`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/workstation/REVIEWED.md). Default-build results are always rebuilt in full. On-demand results are spot-checked. Such families are marked "on demand" wherever they are cited, and they are stale after upstream changes until rebuilt.

**Sharing oleans.** [`scripts/workstation/oleans.py`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/scripts/workstation/oleans.py) packs and unpacks compiled PlasmaLean modules between machines, like the Mathlib cache. Before extracting, it checks the Lean version, `lake-manifest.json` and identical sources against a manifest. Trust caveat: unpacked files are not re-checked by the kernel on the receiving machine. Using them means trusting the machine that built them, so they are not a substitute for a laptop rebuild of default-build results.

## Theorem backlog

| ID | Target | Scope |
| --- | --- | --- |
| N1 | Exact rational parser and arithmetic containment | Small trusted certificate core |
| N2 | Grid/Lipschitz and Fourier-tail bounds | Continuous geometric certificates |
| N3 | Matrix factorization and block positivity | Finite algebra and reusable form theory |
| N4 | Generic contraction/radii-polynomial soundness | Banach spaces, explicit hypotheses |
| N5 | A validated scalar/ODE/axisymmetric equilibrium | First continuum examples |
| N6 | MHD equilibrium/operator tail estimates | Substantial analysis/research |
| N7 | All-mode robust energy certificate | N6 plus [03](03-mhd-stability.md) |
| N8 | Invariant-torus and finite-time orbit certificates | Source-specific KAM and validated ODEs |
| N9 | Certificate composition over correlated uncertainty | Common witnesses, norms, and data |

The progress column is generated from `progress/status.json`; the status sections above give the reading of 30 October 2026. In short:

- N4, N5 and the vacuum part of N8 are compiled.
- N1–N3 are partial: there is no text parser and no general LDLᵀ checker.
- N6, N7 and the coil part of N8 (Q-2) are open.
- N9 has the framework only.

Under the contract, the next numerics needs are certified tori and Boozer/ε_QS diagnostics for the Dommaschk QA field (Q-16), and validated bounce integrals for the C2 diagnostics (Q-19).
