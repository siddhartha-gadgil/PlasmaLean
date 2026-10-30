# A quasisymmetric solution with a certified defect bound (Q-16): three routes assessed

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-27` |
| Title | A quasisymmetric solution: exact, validated or family-member routes to Q-16 |
| Kind | source synthesis / research approach / counterexample (exact obstruction for the Landreman families) |
| Addresses | `Q-16`; `G-1`, `G-4`, `G-6`; tracks T7/T8, rung M4–M5 |
| Depends on | N-4 (`near-axis-quasisymmetry.md`), N-12 (`finite-beta-stellarator.md`), N-10/N-13 (KAM route), N-14; Lean: `LandremanFamily2.field_axis`, `LandremanEquilibrium.axis_fieldLine` / `field_axis`, `Kinetic.Boozer.helicalMomentum_hasDerivAt`, `boozerGC_trapped_until`, `Fields.DefectConfinement`, `Certificates.RadiiPolynomial`, `Theory.KAM.Cohomological`, `StripAlgebra`, the `KamTorusA*` pipeline |
| Dependency requirement | Closed forms of the axis field in both families (compiled); the Boozer GC model (compiled, supplied model); KAM-torus and cohomological-equation estimates (compiled) for route (ii). No dependency on any conjecture |
| Produces | Verdict per route; a precise, non-trivial restatement of Q-16 (§2); an exact obstruction (`|B|` is non-constant on the magnetic axis) showing that no member of Landreman families 1–2 with `ε ≠ 0` is weakly quasisymmetric near the axis (§5.1, proof complete, Lean-cheap); numerical Boozer spectra of family 2 (§5.2); a concrete certifiable problem for route (ii) (§4) with size estimates; recommended first deliverables (§6) |
| Difficulty | research (strong form open mathematics); hard but finite for the recommended certified-defect target |
| Status | stated (routes assessed); route (iii) is a **proved barrier** in Lean (§5.4) |
| Lean evidence | `Theory/Fields/WeakQuasisymmetry.lean` (`WeakQS`, `WeakQSDefect`, `qsDefect`, axis lemma `WeakQS.normB_const_of_gradient_eq_zero`, sanity triad) and `Design/LandremanNotQS.lean` (`family1_not_weakQS`, `family2_not_weakQS` and variants), default build, standard axioms (§5.4) |
| Audit evidence | not audited |
| Last updated | 30 October 2026: created; same day: §6.2 item 1 formalized (route (iii) proved barrier) |

Untrusted scripts (numerical observations only): `scripts/quasisymmetry/qs_family.py`
(triple-product QS test), `boozer_line.py` (Boozer spectrum of `|B|` along one field line),
`axis_field.py` (`|B|` on the magnetic axis, against the closed forms). They need `numpy`, `scipy`,
`sympy`.

---

## 0. Verdict

1. **The strong form of Q-16 (an exactly quasisymmetric, non-symmetric vacuum field or MHS equilibrium
   on a volume) is open mathematics.** No existence or non-existence proof is known. Constantin–Drivas–
   Ginsberg write (arXiv:2009.08860, p. 7, after Theorem 1.2): "It is unknown whether or not
   quasisymmetry can be achieved in a volume." Burby–Kallinikos–MacKay (arXiv:1912.06468) frame the
   Garren–Boozer conjecture (only Euclidean isometries can be QS generators of MHS fields with bounded
   surfaces) and state that they have not proved or disproved it. Garren–Boozer (third-order
   overdetermination) and Plunk–Helander (arXiv:1801.02990, no global quasi-axisymmetry for weakly
   non-axisymmetric vacuum fields) are perturbative and *suggest non-existence*. Exact QS on a *single
   surface* is supported only by formal expansions and numerics (Garren–Boozer; Plunk–Helander;
   Sengupta–Paul–Weitzner–Bhattacharjee, arXiv:2011.08149), not by a rigorous theorem. The only rigorous
   weakly-QS non-symmetric fields I found (Sato, Sci. Rep. 12 (2022) 11322, arXiv:2204.09241) have zero
   rotational transform and satisfy no vacuum or isotropic MHS law. **PlasmaLean should not target ε = 0.**
2. **The form of Q-16 that can be achieved is a certified small defect, and it needs a non-triviality
   clause.** Any near-axisymmetric field has a small QS defect. So "quasisymmetric, not exactly
   symmetric" must mean that the defect is small *relative to the non-axisymmetry*. For vacuum fields the
   cleanest clause is `ι ≥ ι_min > 0` on certified invariant tori, because an axisymmetric vacuum field
   has no nested tori with non-zero transform (§2).
3. **Route (i), a rigorous near-axis remainder bound: not recommended as the main route.** The near-axis
   QS system is overdetermined at third order (Garren–Boozer). The vacuum near-axis expansion is
   *ill-posed* and diverges in general (Ruth–Jorge–Bindel, arXiv:2411.04352, Theorem 3.10 in the HTML
   version). It converges only after regularization (their Theorem 3.13 and Corollary 3.15), which
   changes the equation. A truncated expansion plus an elliptic correction (N-4 §6.3) gives *a* vacuum
   field. Its QS defect must still be certified by the machinery of route (ii). Route (i) is therefore a
   source of initial guesses, plus cheap first-order necessary conditions (§3.3).
4. **Route (ii), a validated vacuum field near a QS target: recommended, in the "explicit field"
   variant (§4).**
   - Do **not** solve a boundary-value problem by Newton–Kantorovich. A 3-D Laplace solve on a shaped
     torus needs a validated 3-D spectral inverse that the library lacks. Its Lean check would be far
     beyond the laptop budget.
   - Instead take an *explicit* harmonic field `B = G∇φ + ∇h`, with `h` a finite sum of Dommaschk
     potentials or harmonic polynomials and coefficients fitted (untrusted) to a published QA
     configuration. It satisfies Maxwell's equations exactly, by an algebraic identity.
   - Then certify two things with the existing KAM pipeline: one or more invariant tori, and on each
     torus Boozer angles (one extra cohomological equation) and a bound on the non-QS Fourier part of
     `|B|`.
   - Existence is then not an issue. Nestedness comes from the certified tori. The defect bound is an
     ℓ¹ estimate.
5. **Route (iii), quasisymmetric members of exact families: negative, by an exact argument.**
   - **Neither Landreman family has a weakly quasisymmetric member with ε ≠ 0 near its axis.** A
     weak-QS generator that does not vanish on the magnetic axis forces `|B|` to be constant along the
     axis (§5.1, complete proof). In both families `|B|` on the axis is an explicit non-constant
     function:
     - family 2: `cosh((ε/2) sin 2ζ)/√(2(h + ε cos 2ζ))`, with `h = √(4S² + ε²)`;
     - family 1: `√(1 − ε² + ε² cos² 2ζ)`.
   - Numerically the Boozer defect of family 2 is *first order* in ε. The dominant mode is the mirror
     mode (0, 2), with amplitude ≈ 0.063 ε B₀₀ (§5.2). So the family is "near-QS" only in the trivial
     near-axisymmetric sense. Certifying `|ξB| ≤ C ε` on a band is possible but does not meet Q-16.
6. **Recommended first deliverables (§6).**
   - (a) A cheap Lean unit that records route (iii) as a proved barrier and fixes the definitions:
     `WeakQS` / `WeakQSDefect` (CDG Definition 1, with defects), the axis lemma, and
     `family1_not_weakQS`, `family2_not_weakQS`. About 300–500 lines, laptop.
   - (b) The deliverable that changes the readiness of Q-16: an untrusted numerical candidate for
     route (ii). This is an explicit Dommaschk-sum vacuum field fitted to a QA target, with two
     outputs:
     - measured on its invariant tori: `ι`, twist, Fourier strip width, and the Boozer non-QS amplitude;
     - the basis size needed for `ε_QS ≤ 10⁻³ B₀`.

     Cost: hours to a day on the workstation, nothing heavy on the laptop.

---

## 1. Purpose and scope

Q-16 asks for "an exact or validated field, vacuum or force-balanced, that is quasisymmetric but not
exactly symmetric, with a certified bound on its quasisymmetry defect ξB on a nested region." It feeds:

- **G-6.** The near-QA alpha results (`alpha_trapped_reactorQA`, `alpha_trapped_reactorQA_averaged`,
  `reference_kick_osc`) use a *supplied* second-order near-axis `|B|`. N-4 §5.1 says it is "formal
  asymptotic" only. A solution would replace that supplied field.
- **G-1.** A non-symmetric candidate with confinement *and* a QS structure.
- **G-4.** Finite β. An exactly force-balanced QS equilibrium is out of reach (N-12 §3: small divisors).
  The finite-β link is through the stepped-pressure route Q-14 (§6.4).

Model: vacuum magnetostatics `∇·B = 0`, `∇×B = 0` on an open set of ℝ³ (kernel `VacuumField`), or
isotropic MHS `J×B = ∇p` (kernel `ForceBalance`). Units: normalized (R ≈ 1, B₀ ≈ 1) unless stated.
Outside scope: anisotropic-pressure equilibria (Rodríguez–Bhattacharjee), quasi-isodynamic fields
(they have no continuous symmetry and no Noether invariant), and coil fields (Q-2).

## 2. Definitions and a precise target

**Weak quasisymmetry** (Rodríguez–Helander–Bhattacharjee 2020, arXiv:2004.11431; in the form of CDG,
arXiv:2009.08860, Definition 1, eqs. (1.7)–(1.9)). Let `ξ` be a non-vanishing vector field on a
toroidal domain T, tangent to ∂T. Then B is weakly QS with respect to ξ if, for some ψ : T → ℝ,

    div ξ = 0,     B × ξ = −∇ψ,     ξ·∇|B| = 0     in T.

Strong QS adds `ξ × J = ∇(B·ξ)` (CDG (1.10)). For force-free toroidal fields, CDG state (§1, after (1.10)) that the
two notions coincide; vacuum fields are such fields. In Boozer coordinates of an MHS field, QS with
helicity (M, N) means `B = B(ψ, Mθ − Nφ)`. This is the `ξB = 0` of `BoozerGuidingCentre`.

**Certified defect (proposed Lean structure `WeakQSDefect B ξ ψ T (δ₀, δ₁, δ₂)`).**
`|div ξ| ≤ δ₀`, `|B×ξ + ∇ψ| ≤ δ₁` and `|ξ·∇|B|| ≤ δ₂` pointwise on T, with `|ξ| ≥ ξ_min > 0`.
The three defects play different roles:
- `δ₁ = 0` means that ψ is an exact first integral (exact surfaces);
- `δ₁ > 0` gives finite-time surface confinement, in the pattern of `Fields.DefectConfinement`;
- `δ₂` is the symmetry-breaking forcing of the GC momentum.

Burby–Kallinikos–MacKay, *Approximate symmetries of guiding-centre motion* (J. Phys. A 54 (2021)
125202, arXiv:2010.08968; main result Theorem 6.1), is the source to extract for the GC Noether theorem
with these defects in Cartesian form.

**On a single invariant torus S** (vacuum; the version route (ii) certifies). Let `(θ_B, φ_B)` be
Boozer angles on S. Write `|B| = Σ B_{mn} cos(mθ_B − nφ_B) (+ sin terms)`. The on-surface defect for
helicity (M, N) is `ε_S := Σ_{(m,n) ∦ (M,N)} |B_{mn}|` (an ℓ¹ norm, which dominates the sup norm of the
non-QS part).

**Non-triviality.** Any axisymmetric field has ε = 0, and a near-axisymmetric field has small ε. For QA
helicity every non-axisymmetric Fourier mode of |B| *is* defect. So non-symmetry has to be measured in
the geometry, not in |B|. Two usable clauses:
- **(N-vac)** B is a vacuum field and its certified invariant tori have `ι ≥ ι_min > 0`. *Proved
  informally:* an axisymmetric vacuum field `B = G∇φ + ∇ψ_p × ∇φ` has `Δ*ψ_p = 0`. By the maximum
  principle for the elliptic operator `Δ*` (no zero-order term), ψ_p has no strict interior extremum in
  the poloidal plane. So there is no magnetic axis encircled by nested poloidal-flux tori, and any
  torus of B must have ι = 0. Hence `ι > 0` on an invariant torus certifies that B is not axisymmetric.
  No other continuous Euclidean isometry preserves a bounded torus, apart from rotations about other
  axes; the same argument applies to them.
- **(N-ratio)** Use the ratio `𝔯 := (ε_QS/B₀)/(δ_geo/R₀)`, where δ_geo is a geometric measure of
  non-axisymmetry (for example the non-axisymmetric Fourier part of the surface shape). Rough values:
  - precise QA (Landreman–Paul): 𝔯 ≈ 10⁻⁴;
  - Landreman family 2 at ε = 1/4: 𝔯 ≈ 0.5 (§5.2).

**Proposed restatement of Q-16 (certified-defect form).** An explicit vacuum field B on an open set
U ⊃ T̄, with the following certified properties:
- invariant tori S₁ ⊂ … ⊂ S_n ⊂ U, nested, with Diophantine transforms `ι_j ≥ ι_min > 0`;
- for each j, Boozer angles on S_j and `ε_{S_j} ≤ ε_target B₀` for one fixed helicity (QA: (M, N) = (1, 0));
- optionally, on the solid torus bounded by S_n, explicit (ξ, ψ) with `WeakQSDefect` bounds
  (δ₀, δ₁, δ₂).

The strong form `ε_target = 0` is open (§3.1). A first realistic target is `ε_target = 10⁻³` with
`ι_min ≈ 0.3–0.4`.

## 3. Route (i): the near-axis expansion with a rigorous remainder

### 3.1 What is known (sourced)

| Result | Source and locator | Kind |
| --- | --- | --- |
| QS imposable at O(r) for any axis. Constraints at O(r²). Overdetermined at O(r³) (isotropic MHS, including vacuum) | Garren & Boozer, Phys. Fluids B 3 (1991) 2805 and 2822 (locators from N-4; not re-checked) | formal asymptotic |
| Weakly non-axisymmetric vacuum: QA on one surface possible at every order; global (non-axisymmetric) QA does not exist in the expansion | Plunk & Helander, JPP 84 (2018) 905840205, arXiv:1801.02990 (abstract; conclusions) | formal asymptotic, VMEC check |
| Finite-β version | Plunk, JPP 86 (2020) 905860409 (unverified locator) | formal |
| Anisotropic pressure removes the overdetermination; isotropic QS kept to O(r²) for circular-axis examples | Rodríguez & Bhattacharjee, Phys. Plasmas 28 (2021) 012508 (arXiv:2008.04715) and 012509 (arXiv:2008.12580) | formal asymptotic, numerics |
| Weak QS near-axis to all orders, formally. "We do not prove that the expansion converges (it is likely divergent but asymptotic)" | Rodríguez, Sengupta & Bhattacharjee, Phys. Plasmas 29 (2022) 012507, arXiv:2110.13703 | formal |
| Anisotropic-pressure QA to 6th order (pyAQSC); estimated radius of convergence small | Fu et al., arXiv:2505.20475 (abstract; convergence claim unverified) | numerical |
| **Vacuum near-axis expansion ill-posed**: bounded smooth input perturbations give unbounded off-axis deviations (high poloidal wavenumber). A regularized expansion converges in (σ, H^q)-analytic spaces | Ruth, Jorge & Bindel, JPP 91 (2025) E73, arXiv:2411.04352: Theorem 3.10 (ill-posedness), Theorem 3.13 and Corollary 3.15 (convergence of the regularized problem), Definition 3.5 (spaces). Numbers from the arXiv HTML version; a search snippet cited "Theorem 3.8", so check the version | rigorous (vacuum, no QS) |
| Arbitrary-order NAE written formally, "with no claims regarding the convergence" | Sengupta et al., arXiv:2402.17034 | formal |
| Small-force near-QS equilibria: closed nested surfaces, B×ξ = ∇ψ exact, MHS up to force f, `‖f‖_{C^{k,α}} ≤ c‖δ − g‖_{C^{k+2,α}}`, ξ·∇\|B\| controlled by the Euclidean deformation tensor of ξ (their (1.24)) | Constantin, Drivas & Ginsberg, JPP 87 (2021) 905870111, arXiv:2009.08860, Theorems 1.1–1.2, eq. (1.24), Lemma C.5 | rigorous, perturbative near axisymmetry, non-zero force |
| "It is unknown whether or not quasisymmetry can be achieved in a volume" | CDG, arXiv:2009.08860, p. 7 | statement of open problem |
| QS as an integrability property. Restrictions on generators. A QS generator that is a circle action under mild conditions (Thm VIII.2). Garren–Boozer conjecture neither proved nor disproved | Burby, Kallinikos & MacKay, J. Math. Phys. 61 (2020) 093503, arXiv:1912.06468 | rigorous partial |
| Admissible quasisymmetries characterized (overdetermined 2nd-order PDE system). GB not shown to apply without force balance | Burby, Kallinikos, MacKay, Perrella & Pfefferlé, arXiv:2403.03352 | rigorous partial |
| Weakly QS, smooth, nested surfaces, not isometry-invariant, **zero rotational transform**, anisotropic MHD only | N. Sato, Sci. Rep. 12 (2022) 11322, arXiv:2204.09241 | rigorous, outside our model |
| Exact vacuum QS near one flux surface (surface expansion, a nonlinear parabolic PDE) | Sengupta, Paul, Weitzner & Bhattacharjee, arXiv:2011.08149 (JPP 2021) | formal + numerical |

**Answer to the brief's key question.** A rigorous existence result for an exactly QS, non-symmetric
vacuum field on a volume with nested surfaces is **not known**. Its non-existence is also not proved.
It is **open**, with formal evidence (GB, Plunk–Helander) pointing to non-existence for isotropic MHS
and vacuum. My searches (30 Oct 2026) found no 2025–2026 rigorous or computer-assisted result that
changes this. A later preprint could exist, so the search is not exhaustive. Even exact QS on a single
surface lacks a rigorous existence proof as far as I can verify.

### 3.2 What Lean could prove, and why it does not solve Q-16

- A truncated near-axis potential `Φ̃` with `|ΔΦ̃| ≤ ε_Δ` plus a Dirichlet correction gives an exact
  vacuum field within an explicit C¹ distance of `∇Φ̃` (N-4 §6.3). This needs a Dirichlet-existence
  hypothesis that Mathlib lacks.
- The resulting field has *some* QS defect. Certifying it needs invariant tori and Boozer angles of
  the corrected field: route (ii), with a worse-controlled field. The ill-posedness (Ruth–Jorge–Bindel)
  means high orders do not help. The truncation error is not small at the radii of interest
  (`r_singularity ≈ 0.41` for precise QA, N-4 §3).
- **Verdict:** no independent value for Q-16 beyond supplying an initial guess.

### 3.3 Cheap necessary conditions (proof sketches; first-order Taylor data of an exact smooth field)

The first-order near-axis conditions are Taylor coefficients of an exact smooth field at its axis. So
they are *necessary* for exact QS. No convergence issue arises at this order, but the derivation from
an exact field is not formalized.
- **Constant |B| on the axis** (§5.1, complete proof, coordinate-free).
- **Planar circular axis ⇒ no vacuum QS with ι₀ ≠ 0.** With κ constant, τ = 0 and I₂ = 0, the σ
  equation (N-4 §3) reads `σ' = −ι_N(η̄⁴/κ⁴ + 1 + σ²)`. The bracket is positive and σ is periodic, so
  ι_N = 0, and the axis helicity is 0 for a planar circle. Corollary (proof sketch, conditional on
  the first-order derivation): `RationalStellarator.field (1/4)` has a circular planar axis and
  ι₀ = 1 − √3/2 ≠ 0, so it is not QS even at first order. A route-(ii) target therefore needs a
  non-planar axis, as in precise QA.

## 4. Route (ii): a validated vacuum field near a QS target

### 4.1 The two formulations

**(ii-BVP) Newton–Kantorovich for a boundary-value problem** (the brief's example). The unknown is Φ
with ΔΦ = 0 in a prescribed torus D and `∂_nΦ = 0` on ∂D, plus a prescribed toroidal flux.
- Spectral representation in (s, θ, φ) coordinates of D: Chebyshev × Fourier × Fourier, with
  variable metric coefficients.
- Unknowns for precise-QA shaping: about 12 × 25 × 25 ≈ 7.5 × 10³.
- The approximate inverse A is dense, about 5 × 10⁷ entries.
- The Z₀/Z₁ bounds need `‖I − A·DF‖` in a weighted ℓ¹ operator norm, a 3-D convolution estimate.

Library coverage:
- `RadiiPolynomial` (abstract theorem, all three entry points): **yes**;
- `WeightedEll1`, `ConvAlgebra`, `FourierRegularity`: **1-D only**;
- `WeightedEll1Z2` / `StripAlgebra`: **2-D Fourier only**.

Missing pieces:
- a 3-D Fourier–Chebyshev algebra with a Neumann boundary operator;
- a metric/Jacobian representation of a shaped torus;
- elliptic regularity from coefficients to a classical harmonic function in 3-D (the 3-D analogue of
  `classical_of_coeff`);
- a Lean check of a 5 × 10⁷-entry matrix product. That is far beyond 6 GB and 240 CPU-min.

**Verdict: not feasible on the laptop.** It is also unnecessary, because Q-16 does not prescribe the
boundary.

**(ii-EXP) Explicit harmonic field + certified tori (recommended).** Existence is trivial, so the
certification moves to tori:

1. **Field.** Take `B = B₀R₀∇φ + ∇h`, where h is a finite sum of Dommaschk potentials (W. Dommaschk,
   Comput. Phys. Commun. 40 (1986) 203, from memory). Each potential is a polynomial in (R, z, ln R)
   times cos/sin(mφ), exactly harmonic, with stellarator symmetry and n_fp = 2 available.
   - The coefficients are rationals from an untrusted least-squares fit to the precise-QA field
     (Landreman–Paul, arXiv:2108.03711) or a gentler QA (for example LSP19 §5.1 r1, N-4 §3).
   - Maxwell's equations are identities in ℚ[R, R⁻¹, ln R, z] ⊗ trig(φ). They can be checked by
     polynomial normalization (an `eval_cert` normal-form checker rather than `ring` for ~100 terms),
     following the pattern of `RationalStellarator`.
   - The coils that produce B are not part of the claim. Any harmonic field in U is produced by a
     current sheet on a surface enclosing U, but that is a separate question (Q-2).
2. **Tori.** Use the flow-form a posteriori KAM certificate already used for `field (1/4)` (N-10,
   `KamTorusA*`, `KamFlow*`). Each certified torus K_j(θ, φ) has a Diophantine `ι_j` and a twist
   bound. The all-time confinement inside S_n is already a theorem pattern
   (`rationalStellarator_confined_forever_exists`).
3. **Boozer angles on S_j.** In vacuum, `B·∇φ_B = B²/G`. On the torus write `φ_B = φ + η(θ, φ)` and
   `θ_B = θ + ι_j η` with η periodic. Then η solves
   `(∂_φ + ι_j ∂_θ) η = (|B|²/(G B·∇φ)) ∘ K_j − 1` after the mean is fixed by G.
   - This is *one* more cohomological equation with the same divisor as the KAM step.
   - `Theory/KAM/Cohomological.cohSol_estimate` and `StripAlgebra.Bd.coh` already give
     `‖η‖_{r−δ} ≤ C_R‖rhs‖_r`.
   - G is determined by `∮B·dl` around the torus, a mean that the ball arithmetic computes.
4. **QS defect on S_j.** Compose `|B| ∘ K_j` (ball arithmetic in the strip algebra, `KronBall`) with
   the angle change. Bound the non-QA Fourier part in ℓ¹ (it dominates the sup norm), with tails by
   the strip width (`StripPaleyWiener`).
   - Composition with the angle change can be avoided. QA in Boozer angles means
     `|B| = f(θ_B) = f(θ + ι_j η)`.
   - So it suffices to bound `|B|∘K_j − f(θ + ι_jη)` for an explicit trigonometric polynomial f,
     using the same Taylor/composition estimates (`Theory/KAM/Composition`).
5. **Optional volume statement.** Give explicit (ξ, ψ) on the solid torus inside S_n with
   `WeakQSDefect` bounds, by interval Taylor models on a 3-D box cover (the family-2 ballooning
   checker infrastructure, N-12 §10). This step feeds G-6 through a Cartesian GC Noether theorem with
   defects (BKM 2021) and needs a new note.

### 4.2 Which existing tools cover which parts

| Step | Covered by | Missing |
| --- | --- | --- |
| Exact vacuum field | `Kernel` `VacuumField`; `RationalStellarator` pattern; `eval_cert` | Dommaschk basis (ln R terms) and its harmonicity identities: new but routine |
| Invariance residual of a Fourier torus | `KamFlowField*`, `KronBall*`, `TorusFieldAna` (holomorphic field along a complexified torus) | the field is now (R, z, ln R)-polynomial: new holomorphy/majorant constants for ln R near R ≈ 1 (routine) |
| KAM theorem with explicit constants | `KamSequence`, `Cohomological`, `StripAlgebra`, `KamNewton*`, `KamIteration` (compiled for torus A) | **twist**: precise QA has low shear, so a small twist constant makes the KAM smallness condition harder (barrier B2 below) |
| Boozer angles on the torus | `Cohomological.cohSol_estimate`, `Bd.coh` | the statement "η gives Boozer angles" (a short derivation from `B = ∇Φ`) |
| Non-QS Fourier bound | `KronBall`, `Kronecker2DWeighted`, `StripPaleyWiener` | glue only |
| Nested region | several certified tori (one certificate each) | a volume statement between tori needs (ξ, ψ) defects: 3-D cover |
| Link to G-6 | `BoozerGuidingCentre` needs Boozer coordinates on a *volume* | a Cartesian GC Noether theorem with weak-QS defects (BKM 2021): new theory note |

### 4.3 Size estimate (rough, by analogy with torus A and the family-2 checker)

- **Fit.** About 50–150 Dommaschk coefficients (m ∈ 2ℤ up to about 12, l up to about 8–10). Unknown
  until stage 1 measures it. Workstation: minutes.
- **Torus.**
  - Precise QA is more strongly shaped than torus A (48 θ-modes for the map, about 10³ coefficients for
    torus B, N-10 §4).
  - Estimate 24–32 θ-modes × 12–16 φ-modes × 2 components ≈ 1–2 × 10³ coefficients.
  - Invariance error target 10⁻¹²–10⁻¹⁴ (torus A reached about 3 × 10⁻¹³) means 16–20 digits, dyadic
    2⁻⁶⁰.
- **QS defect.** ε_target = 10⁻³ needs only about 4 digits in the final bound. The cost is dominated by
  the torus.
- **Lean.**
  - One torus certificate is comparable to the `KamTorusA*` family: tens of modules of about 1–2 min
    and ≤ 5.6 GB each. That is laptop-feasible as an on-demand top module (≤ 240 CPU-min) if the
    workstation finds small certificates.
  - The Boozer step adds about one Newton step's worth.
  - The optional 3-D volume cover is workstation-scale: 10⁴–10⁵ boxes, 10–100 CPU-h, borderline for
    laptop re-checking (family-2 experience).
- **Workstation numerics.** Fit plus Boozer diagnostics: hours. KAM Newton refinement to 10⁻¹⁴: about
  1 CPU-day for a strongly shaped torus (Q-2 needed an estimated 4 CPU-days, but for a coil field with
  much worse analyticity).

### 4.4 Barriers

- **B1. Fit quality versus QS quality.** The defect of the explicit field is about
  (QS defect of the target) + O(fit error). Precise QA has about 5 × 10⁻⁵ relative non-QS amplitude
  (N-4 §2), so ε_target = 10⁻³ leaves room. Whether 10⁻⁴ is reachable with ~100 Dommaschk terms is
  unknown.
- **B2. Low shear.** QA configurations have nearly flat ι. The ELP-S twist (Definition 6.1) is then
  small and the KAM constant grows. Mitigation: choose a target with moderate shear or slightly lower
  aspect ratio. Fallback: a finite-time version (one approximate torus with δ₁ > 0) using
  `DefectConfinement`, which needs no KAM.
- **B3. Analyticity strip.** Strongly shaped surfaces have narrow strips (torus D of the rational field
  needed ≥ 200 modes), so stay well inside the plasma (s ≲ 0.5).
- **B4. The coil question** (Q-2) is not addressed. The certified field is a vacuum field in U, not a
  coil field.

## 5. Route (iii): quasisymmetric members of exact families

### 5.1 Exact obstruction: |B| must be constant on the magnetic axis

**Lemma (complete proof).** Hypotheses:
- B is C¹ on an open set containing a closed integral curve Γ of B (a magnetic axis), with B ≠ 0 on Γ;
- ξ and ψ are C¹ with `B × ξ = −∇ψ` and `ξ·∇|B| = 0` on a neighbourhood of Γ;
- ∇ψ = 0 on Γ;
- ξ ≠ 0 on Γ.

Then |B| is constant on Γ.

*Proof.* On Γ, `B × ξ = 0` and `B ≠ 0`, so `ξ = c B` with `c ≠ 0` (because ξ ≠ 0). So
`B·∇|B| = c⁻¹ ξ·∇|B| = 0` on Γ. Since Γ is an integral curve of B, `d/dt |B|(γ(t)) = B·∇|B| = 0`,
so |B| is constant along Γ. ∎ (div ξ = 0 is not used.)

*Remarks on the hypotheses.*
- ∇ψ = 0 on Γ holds when ψ is a C¹ function of a flux label with a non-degenerate minimum on the axis
  (ψ = F(ψ_L), so ∇ψ = F′∇ψ_L = 0). This is the case for both families.
- ξ ≠ 0 on Γ is CDG's Definition 1. It excludes quasi-poloidal generators (∝ ∂_θ, which vanish on the
  axis). Quasi-poloidal symmetry is excluded near the axis anyway: at O(r), |B| has a `cos θ` term
  proportional to the axis curvature, which is non-zero somewhere on a closed curve. That is a proof
  sketch via the first-order expansion.
- In Boozer language: B(ψ, Mθ − Nφ) restricted to ψ = 0 cannot depend on θ, so for M ≠ 0 it is
  constant.

**Application (closed forms from compiled Lean, so a Lean-cheap corollary).**
- **Family 2** (`LandremanFamily2.field_axis`). On the axis `γ(ζ) = (a_c cos ζ, b_c sin ζ, 0)`,
  `B = cosh(ε cos ζ sin ζ)/(2G) · γ′` with `G = |γ′|² = b_c² cos² ζ + a_c² sin² ζ`. So
  `|B|_axis(ζ) = cosh((ε/2) sin 2ζ) / √(2(h + ε cos 2ζ))`, with `h = √(4S² + ε²)`.
  At ζ = 0 and ζ = π/2 the cosh factor is 1 and the values are `1/√(2(h ± ε))`, which differ when
  ε ≠ 0. So `|B|_axis(0) ≠ |B|_axis(π/2)` for every ε ≠ 0, S > 0 and every λ.
- **Family 1** (`LandremanEquilibrium.field_axis`, `axis_fieldLine`). B on the axis equals
  `axisVel = (−ab sin ζ, ab cos ζ, ε cos 2ζ)` with ab = √(1 − ε²). So
  `|B|²_axis = 1 − ε² + ε² cos² 2ζ`, which is non-constant for ε ≠ 0. (At ζ = 0 it is 1; at ζ = π/4
  it is 1 − ε².)
- Numerical check (`axis_field.py`, agreement with the closed forms ≤ 4 × 10⁻¹⁵). Relative variation:
  - family 2, ε = 1/4, S = 4: 3.1 %;
  - family 2, ε = 1/16: 0.78 %;
  - the paper example ε = 2, S = 1: 82 %;
  - family 1, ε = 0.3: 3.5 %.

**Corollary (complete proof given the compiled closed forms).** For ε ≠ 0, no member of Landreman
family 1 or 2 is weakly quasisymmetric, with a generator non-vanishing on the axis, on any
neighbourhood of its magnetic axis. This holds for every helicity with a toroidal component. The
obstruction is at zeroth order in the distance from the axis, so it is the strongest possible
negative statement for these families.

Not checked: the non-stellarator-symmetric extension (Issan–Citrin–Landreman–Tracey, arXiv:2610.07304)
and the Gómez-Serrano–Liehr–Taylor C_N family (arXiv:2609.24739). In the GSLT family B **vanishes** on
the round axis (N-12 §0), so the lemma does not apply there (B ≠ 0 fails). Its QS status is unknown
here.

### 5.2 Numerical Boozer spectra of family 2 (numerical observation)

Method (`qs_family.py`, `boozer_line.py`):
- trace one field line on a surface ψ = k²/2 (ψ conserved to ≤ 2 × 10⁻¹⁰);
- set `φ_B = c∫|B|² dt`, using `B·∇φ_B ∝ B²` along `x′ = B`, with c fixed by the secular toroidal
  winding;
- set `θ_B = ι φ_B + θ₀`;
- fit `|B| = Σ B_{mn} cos((mι − n)φ_B + …)` with m ≤ 4, |n| ≤ 24, n ∈ 2ℤ (two field periods).

For an irrational surface this recovers the Boozer spectrum (fit residual 0.4–2.6 %).

| ε (S = 4, λ = 15) | k | ι | QA part `‖B_{m0}‖/B₀₀` | non-QA part `‖B_{m,n≠0}‖/B₀₀` | dominant defect mode |
| --- | --- | --- | --- | --- | --- |
| 1/16 | 0.4 | 8.31 | 6.1e-2 | 4.0e-3 | (0, 2): 3.9e-3 |
| 1/8 | 0.4 | 8.31 | 6.1e-2 | 8.0e-3 | (0, 2): 7.9e-3 |
| 1/4 | 0.4 | 8.28 | 6.0e-2 | 1.6e-2 | (0, 2): 1.6e-2 |
| 1/4 | 0.7 | 9.28 | 1.6e-1 | 1.8e-2 | (0, 2): 1.6e-2 |

- The defect is **exactly linear in ε**: the (0, 2) amplitude ≈ 0.063 ε B₀₀. It is the mirror term
  generated by the non-constant axis |B| of §5.1.
- The geometric non-axisymmetry is also O(ε): `(b_c − a_c)/a_c ≈ ε/(2S) = 3 %` at ε = 1/4. So
  𝔯 ≈ 0.5, while precise QA has 𝔯 ≈ 10⁻⁴.
- Helicity-free test: the triple-product residual `|g₂ − F g₁|/|g₂|`, with
  `g₁ = B·∇|B|`, `g₂ = (B×∇ψ)·∇|B|` and the best constant F on the surface, is 0.02–0.32 for
  ε = 1/4, S = 4. It is 0.96–0.98 for the paper example. Family 1 gives 0.34–0.57 on single
  (closed) lines.
- Neither QH nor quasi-poloidal fits: the spectrum has large m ≠ 0, n = 0 *and* m = 0, n ≠ 0
  components.
- The rotational transform here (ι ≈ 8–9) comes from the large plasma current. These are
  current-carrying, tokamak-like fields as ε → 0. Their near-QA property at small ε is
  near-axisymmetry, not quasisymmetry.

### 5.3 The weaker target

"A QS field-strength defect bounded by an explicit ε on a band" *can* be certified exactly for
family 2.
- ψ is exact, so take `ξ = B×∇ψ/|B|² + λ_ξ B`. This gives `B×ξ = −∇ψ` exactly (δ₁ = 0).
- The remaining defects are δ₀ (from the choice of λ_ξ) and δ₂.
- The certificate would be pointwise interval bounds with the existing family-2 enclosure machinery
  (`LandremanFamily2Quad`, `ValidatedTrig*`).

But §5.1–5.2 show that `δ₂ ≈ (const)·ε` *is* the whole non-axisymmetry. This would not answer Q-16 in
any non-trivial sense, and **I do not recommend it**. Its only use is as a non-vacuous test fixture
for the `WeakQSDefect` interface.

No exact solution family in the literature that I know of contains QS members other than exactly
symmetric ones (Solov'ev, helical). "None known" is a statement about my search, not a theorem.

### 5.4 Lean status of route (iii): proved barrier (30 October 2026)

Default build, zero warnings, axioms `propext`, `Classical.choice`, `Quot.sound` only.

- `PlasmaLean.Fields.WeakQS B ξ ψ T` (`Theory/Fields/WeakQuasisymmetry.lean`): CDG Definition 1
  pointwise on `T`: `ξ ≠ 0`, `div ξ = 0`, `B × ξ = -∇ψ`, `ξ·∇|B| = 0` (`qsError`), with `|B|`, `ξ`,
  `ψ` differentiable on `T`. Tangency to `∂T`, `[ξ, B] = 0` and strong QS are not included.
  `WeakQSDefect B ξ ψ T δ₀ δ₁ δ₂` (the §2 structure) and `qsDefect B ξ T = sup_T |ξ·∇|B||` in `ℝ≥0∞`;
  `weakQS_iff_defect_zero`, `qsDefect_eq_zero_iff`, `qsDefect_le_ofReal_iff`. Exact symmetry is a special
  case: `qsError_eq_zero_of_invariant`, `qsError_rotGen_eq_zero_of_axisymmetric` (ξ = ∂_φ).
- Sanity triad: `weakQS_uniform` (degenerate), `weakQS_screw` (axisymmetric screw pinch `(-y, x, 1)`,
  ξ = ∂_φ, ψ = (x² + y²)/2), `not_weakQS_mirror` (counterexample).
- Axis lemma: `WeakQS.normB_const_of_gradient_eq_zero` (field line up to any time change, in `T`, with
  `∇ψ = 0` on it ⇒ `|B|` constant on it); `WeakQS.normB_const_of_isLocalExtr`; `not_weakQS_of_normB_ne`.
- `Design/LandremanNotQS.lean`: `family1_axis_normB_sq`, `family2_axis_normB_sq` (the closed forms
  above), `family{1,2}_axis_normB_ne`, and the barrier `family1_not_weakQS` (`|ε| < 1`, `ε ≠ 0`) and
  `family2_not_weakQS` (`S > 0`, `ε ≠ 0`, every `λ`): for every `ξ`, `ψ`, `T` with `T ⊇` axis and
  `∇ψ = 0` on the axis, the field is not `WeakQS` (which includes `ξ ≠ 0` on the axis). Variants
  `*_of_isLocalExtr` and `family{1,2}_not_weakQS_flux` (`ψ = F ∘ ψ_flux`, `F` monotone or antitone,
  using `family{1,2}_psi_isLocalMin`). Not covered: generators vanishing on the axis, and potentials
  with `∇ψ ≠ 0` somewhere on the axis (the topological argument that forces `∇ψ = 0` for a `ψ`
  constant on nested tori is not formalized).

## 6. Recommendation

### 6.1 Route choice

**Route (ii-EXP).** Use an explicit Dommaschk-type vacuum field fitted to a QA target, certified
invariant tori with `ι ≥ ι_min > 0` (the non-triviality clause N-vac), and an on-torus Boozer
non-QS ℓ¹ bound `ε_S ≤ 10⁻³ B₀`. Routes (i) and (iii) are closed as headline routes: (i) reduces to
(ii), and (iii) is obstructed exactly.

### 6.2 Smallest deliverables that change readiness

1. **Lean (cheap, laptop, about 300–500 lines; makes route (iii) a recorded barrier). Done 30 October
   2026 (§5.4), in `Theory/Fields/WeakQuasisymmetry.lean` and `Design/LandremanNotQS.lean` with the
   names listed there.** Originally planned in
   `Theory/Fields/Quasisymmetry.lean`:
   - `WeakQS`, `WeakQSDefect`;
   - `absB_const_on_axis_of_weakQS`, the lemma of §5.1 (`HasDerivAt` along an integral curve; no
     coordinates);
   - sanity: an axisymmetric example (`B = ∇φ`-type with ξ = rotation generator) and the
     `Sanity/QuasisymmetryNotSymmetry` data.

   Then `Design/LandremanQS.lean`: `family2_axis_absB_ne`, `family1_axis_absB_ne`, and
   `family{1,2}_not_weakQS_near_axis`. They use only `field_axis` and closed forms.
2. **Numerics (makes route (ii) ready for certification; workstation, hours to a day).** Build a
   generator `scripts/quasisymmetry/dommaschk_fit.py` that:
   - fits Dommaschk coefficients to a QA target: precise QA through its pyQSC/VMEC boundary, or the
     simpler r1 §5.1 near-axis QA as a warm-up;
   - finds invariant tori by Newton in flow form (reusing `scripts/kam_oracle`);
   - computes Boozer spectra on them.

   Report: basis size against ε_QS, ι, twist, strip width, invariance error, and Fourier sizes.
   Success criterion: one torus with ε_S ≤ 10⁻³, a twist bounded away from 0, and the strip and mode
   counts of torus A or B (N-10 §4).
3. Then the certificate (on-demand top module), reusing the KAM pipeline, plus the Boozer
   cohomological step.

### 6.3 Rough cost

| Item | Cost |
| --- | --- |
| Lean item 1 | about 1 agent-day, laptop |
| Numerics item 2 | 1–3 agent-days, plus workstation hours to a day |
| One certified torus + Boozer bound | comparable to K2–K3 for torus A: weeks of agent time; Lean check on-demand ≤ 240 CPU-min, if the workstation finds a small certificate |
| Volume `WeakQSDefect` (optional) | 3–5k lines of checker plus 10–100 workstation CPU-h |
| Cartesian GC Noether with defects (for G-6) | a new theory note (BKM 2021 extraction) and a moderate Lean file |

### 6.4 Barriers and links

- **Open mathematics.** ε = 0 on a volume (§3.1). Even ε = 0 on one surface has no rigorous proof.
- **B1–B4** of §4.4. Low shear (KAM twist) is the main technical risk.
- **G-6.** The supplied near-axis `|B|` cannot simply be replaced: `BoozerGuidingCentre` needs volume
  Boozer coordinates, which a non-integrable field lacks. The replacement is the Cartesian
  approximate-symmetry theorem (BKM 2021) fed by `WeakQSDefect` on a band. The resulting confinement
  time is again limited by δ₂ (N-4 §5.3: T ∝ 1/ε, or 1/ε² with averaging).
- **G-4 / Q-14.** A certified QA torus of an explicit vacuum field is exactly the interface needed by
  the stepped-pressure construction (ELP-S Lemma 2.1, N-12 §4). Route (ii) and Q-14 share their
  hardest step.

## 7. Claims and evidence

| # | Claim | Status |
| --- | --- | --- |
| 1 | Exact QS on a volume for non-symmetric vacuum/MHS fields is neither proved nor disproved | sourced (CDG p. 7; BKM 2020; RSB 2022 disclaimer); my search not exhaustive |
| 2 | Vacuum near-axis expansion is ill-posed; regularized version converges | sourced theorem (Ruth–Jorge–Bindel Thms 3.10, 3.13; version-dependent numbering) |
| 3 | Weak QS with ξ ≠ 0 on the axis and ∇ψ = 0 there ⇒ \|B\| constant on the axis | compiled: `WeakQS.normB_const_of_gradient_eq_zero` (§5.4) |
| 4 | Landreman families 1, 2 (ε ≠ 0) are not weakly QS near the axis | compiled: `family1_not_weakQS`, `family2_not_weakQS` (hypotheses in §5.4) |
| 5 | Family-2 Boozer defect ≈ 0.063 ε B₀₀, mirror mode (0, 2) | numerical observation (`boozer_line.py`) |
| 6 | Axisymmetric vacuum fields have no nested tori with ι ≠ 0 about a magnetic axis | proof sketch (maximum principle for Δ*) |
| 7 | Planar circular axis ⇒ no vacuum QS at first order with ι₀ ≠ 0; hence `RationalStellarator.field (1/4)` is not QS at first order | proof sketch (σ equation; first-order derivation not formalized) |
| 8 | Route (ii-EXP) is a finite certification problem covered mostly by existing tools | research approach; sizes are estimates |

## 8. Outputs and next dependencies

Suggested registry updates (for the coordinator):
- **Q-16:** status "open (research); strong form open mathematics". Next action: route (ii-EXP)
  stage 1 (numerics) plus the Lean unit of §6.2 item 1. Barrier: low-shear KAM twist.
- **N-27:** this note. Kind: source synthesis plus counterexample. Status: stated; the family
  obstruction is lean-ready.
- Possible new items:
  - `Q-17`: a Cartesian GC Noether theorem with weak-QS defects (BKM 2021), the bridge to G-6;
  - a design note for the Dommaschk fit and the torus certificate (an N-* when stage 1 starts).
- No downstream note becomes ready until stage 1 reports a viable candidate. The Lean unit of §6.2
  item 1 is ready now.

## Decision on the criterion (30 October 2026)

The user adopted the recommended criterion for Q-16 in its vacuum version: certified invariant tori
with ι ≥ ι_min > 0 on a nested region of an explicit or validated vacuum field, and a certified
quasisymmetry defect small relative to ι (report ι and ε_QS/B together; no single absolute
threshold). Rationale: an axisymmetric vacuum field is purely toroidal with ι = 0, so a fixed
ι_min cannot come from a small perturbation of a symmetric vacuum field. Limits recorded: the
criterion does not transfer to force-balanced fields (plasma current gives near-tokamak fields
ι > 0), the ι–defect scaling used to justify the ratio is heuristic, and near-helically-symmetric
large-aspect-ratio fields are not excluded. The finite-β version of Q-16 needs a separate
criterion (zero net toroidal current, or a quantitative non-Killing bound on ξ), still open.

## Addendum (30 October 2026): the colleague's brief (N-32)

In vacuum Boozer coordinates the strong-QS moment satisfies Ψ' = Mι − N. For quasi-axisymmetry (N = 0) the moment is regular exactly where ι ≠ 0, so C1's ι ≥ ι_min is also the nondegeneracy condition of the QA moment; this supports measuring the defect relative to ι. The brief's linear system for the moment and its pointwise jet obstruction are question Q-25 (`holomorphic-qs-brief.md`).
