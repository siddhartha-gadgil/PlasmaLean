# Assessment: "Complex vacuum fields and new stability estimates" (18 November 2026)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-42` |
| Title | Source assessment of the complex-geometry and stability research note (18 November 2026) |
| Kind | source assessment |
| Addresses | `Q-16`, `Q-24`, `Q-3`, `Q-14`, `Q-20`, `Q-28`; `G-1`, `G-2`, `G-4`, `G-6`, `G-10`; new `Q-29`–`Q-32` |
| Depends on | N-1, N-12, N-17, N-29, N-31, N-32, N-33, N-37, N-40, N-41; Lean: `DommaschkKamNested.dommaschk_nested`, `ExactTorusA.adm`, `KamFlowIterationG.AdmBoundsG`, `Subharmonic.laplacian_normSqField`, `GyroNoether.gyroNoether_hasDerivAt`, `WeakQuasisymmetry.WeakQS` |
| Dependency requirement | the compiled Dommaschk tori and admissibility bounds (on-demand modules, workstation policy) as the seed of S-10; the Bochner identity for S-32 |
| Produces | extraction table (35 claims); checks; method notes N-43, N-44; questions Q-29–Q-32; audit item AF-1 |
| Difficulty | routine (assessment) |
| Status | assessment complete: 35 claims, 30 checked and correct, 0 incorrect, 5 unverified |
| Lean evidence | none new (the claims about project code were checked against the declarations above) |
| Audit evidence | not audited; AF-1 recorded |
| Last updated | 20 November 2026: created |

## Provenance

- **Source:** `sources/fusion_complex_geometry_and_stability.pdf`, "Fusion / research note. Complex
  vacuum fields and new stability estimates", dated 18 November 2026, 28 pages, no authors named.
  SHA-256 `4f080749dc96358bfaba878144fd21b5e327efc67f2856d02149163693df7f7e`. Supplied through
  Vamsi Pingali; committed by the user on 19 November 2026 (`9be616f`).
- **Bundle:** `sources/fusion_complex_geometry_reproducibility/` (`433fe74`). Only its LaTeX was
  read, because the PDF renders every formula as an image. Its scripts were not run. Its copies of
  `candidate.json` and `DommaschkQA2RData.lean` are byte-identical to the project files.
- **Pinned project commit:** `6312f1c` (17 November 2026), for the Dommaschk seed tori.
- **Analysis folder:** [`notes/reasoning/2026-11-20-source-fusion-complex-geometry/`](../reasoning/2026-11-20-source-fusion-complex-geometry/README.md).
  It holds the full extraction table (`02_literature_review.md`) and the checks
  (`02_examples.md`); the scripts are in `scripts/fcg_source/`.

## Summary of the source

The note continues the earlier complex-geometry handoff and has four strands.

1. **Exact algebraic vacuum families.** The project's Dommaschk QA potential is `ϑ + F₀`, with
   `F₀` a Laurent polynomial on `(ℂ*)² × ℂ`. A null-conic (minitwistor) construction gives all
   harmonic polynomials. A KAM persistence argument (Theorem 4) keeps two nested invariant tori
   for every small harmonic-polynomial perturbation.
2. **Two static geometric identities.**
   - An Abelian Hermitian–Yang–Mills lift of any vacuum field to `Ω × S¹`.
   - A subharmonic log-determinant of `I + ∇B/λ`.
   - A proof that a nonzero tangent vacuum field cannot have constant `|B|` on `∂Ω`.
3. **A complete ideal-MHD energy for a periodic cylinder.** The cylinder has constant pressure, a
   vacuum gap, a close ideal wall and fixed fluxes. The note gives an explicit all-mode stability
   window with an `H^{1/2}` interface gap uniform in the period, and an explicit unstable branch.
   It also gives a first-order sufficient criterion on a real toroidal interface and a plan for
   transferring the cylinder result to a torus.
4. **Kinetic bounds.**
   - A quadratic-in-velocity corrector that makes the weak-QS full-orbit momentum conserved to
     second order.
   - A finite-time confinement certificate.
   - Hot-core density and temperature bounds for prescribed-field Vlasov with an absorbing wall.
   - The exact extra terms from `E`, `δB`, collisions and sources.
   - A covariant-derivative calculation for future hypocoercivity.

The source states its own limits plainly: the three positive results use **different
configurations**, and none is a self-consistent hot stellarator.

## Extraction table (condensed)

The full table, with model, hypotheses and units, is in `02_literature_review.md`.

| # | Claim | Locator | Kind | Verdict |
| --- | --- | --- | --- | --- |
| S-1 | Laurent form of the Dommaschk potential: 33 coefficients, 121 monomials, harmonic, real, both symmetries, `u⁻⁶` coefficient | §3.1 | computation | **correct** (exact, independent) |
| S-2 | Real algebraic class `G dϑ + dF` | §3.1 | definition or model | correct |
| S-3, S-4 | Null-conic harmonic functions; complete basis; dimension `N(N+2)` | §3.2 | published theorem (classical) | correct |
| S-5 | Laurent basis `E_pq`, `O_pq` | §3.2 | proof sketch | harmonicity correct; completeness unverified |
| S-6 | Harmonic Runge/Walsh density | §3.3 | published theorem | unverified (standard) |
| S-7 | `ι_A`, `ι_C`, `τ_A = 6997/500`, `τ_C = 141623/10000`, `AdmBoundsG.hτ`, nesting | §3.4 | Lean declaration (this project) | **correct** (matches the code) |
| S-8, S-9 | Torsion = return-map shear; embeddedness of the certified tori | §3.4 | proof sketch | plausible |
| S-10 | **Theorem 4:** harmonic perturbations keep two nested tori (`ε_N` unquantified) | §3.5 | proof sketch (de la Llave–González–Jorba–Villanueva 2005) | plausible; KAM persistence |
| S-11 | Symmetric families `h_m`, `k_m` | §3.5 | complete proof | correct |
| S-12 | Positive-pressure weak MHD lift of the family | §3.6 | proof sketch (depends on the unassessed earlier handoff) | unverified |
| S-13 | Anti-self-dual / HYM lift; non-algebraic bundle; YM minimality | §4 | complete proof | correct; consistent with N-37 |
| S-14 | Subharmonic log-determinant | §5 | complete proof | correct (re-derived) |
| S-15 | No tangent vacuum field with constant `|B|` on `∂Ω` | §5 | complete proof | correct (re-derived) |
| S-16, S-17 | Cylinder `δW` and the exact mode coefficient `F_mn` | §6, §6.1 | published theorem (classical surface-current model) | correct (numerical) |
| S-18 | Unstable branch for `B_e ≥ B_i` | §6.2 | complete proof | correct |
| S-19, S-20 | All-mode window `F ≥ s²/8`; gap `(s²/80)(1 + |m| + κ)` | §6.3–6.5 | complete proof | correct (numerical scan); needs the close wall (below) |
| S-21 | Toroidal criterion `ω·d > 0`, `II(Y, g⁻¹d) < 0` | §7 | proof sketch | plausible (first order re-derived) |
| S-22 | Transfer certificate to a torus | §8 | proposal or plan | open |
| S-23–S-25 | Weak QS ⇒ `bᵀSb = 0`; tensorial homological solution; exact identity (Q7) | §9.1 | complete proof | **correct** (symbolic and numeric) |
| S-26, S-27 | Deterministic certificate (Q8)–(Q9); `Λ²` scaling; relativistic version | §9.1 | complete proof | correct |
| S-28, S-29 | Hot-core moment bounds (H3)–(H5) and constants | §9.2 | complete proof | correct (numerical) |
| S-30 | `E`, `δB`, collision and Landau terms | §9.3 | complete proof / sketch | (P1)–(P2) correct; (P5) unverified |
| S-31 | Covariant derivative (C1); gyro-gauge obstruction; OU energy (C8) | §9.4 | complete proof / sketch | (C1) correct; rest unverified |
| S-32 | A vacuum field of constant `|B|` is constant | §9.4 | complete proof | correct; corollary of `laplacian_normSqField` |
| S-33 | Auxiliary-PDE mechanism of an OpenAI wave-equation manuscript | §2 | proposal (secondary reading) | unverified (manuscript not available) |
| S-34 | Parameter illustration (`s ≈ 0.161`, `β ≈ 0.040`) | §10 | numerical observation | correct |
| S-35 | Source-level audit of the pinned closure (227 modules, no holes) | §1, §3.6.1 | provenance audit | consistent with the project's axiom checks |

## Checks

These are untrusted numerics or exact sympy unless stated; details are in `02_examples.md`.

- **Exact** (`check_laurent.py`, from the project's own `candidate.json`): every number in S-1,
  including `u⁻⁶` coefficient `−12674582344287/143360000000000 · i`.
- **Symbolic** (`check_algebra.py`): null conic, basis and dimension, `E_pq`/`O_pq`
  harmonicity, symmetry of `C`, `R_b(vᵀCv) = vᵀ[C,K]v`.
- **Numeric** (`check_q4_numeric.py`): `[C,K] = S` and the (Q7) cancellation, to `10⁻¹⁵`. sympy
  could not simplify the trigonometric form.
- **Against Lean:**
  - `dkIotaA = −((19 + √5)/89)` and `dkIotaC = −((85 + √5)/361)`.
  - `tauC = 6997/500` (A) and `141623/10⁴` (C).
  - `AdmBoundsG.hτ : c.τ ≤ ‖avg (F.Talg u z)‖`, `ExactTorusA.adm`, `dommaschk_nested`.
- **Numeric** (`check_cylinder_hotcore.py`, 30 digits):
  - window ratios `min F/(s²/8)` = 15.9, 166.7, 16.1 and 4.1 for `s` = 0.01, 0.05, 0.161 and
    0.25, all ≥ 1;
  - the gap bound holds;
  - unstable branch: `F = −0.053`;
  - all hot-core constants agree with the source to the stated digits.
- **Stress test** (`check_far_wall.py`): at `s = 0.161`, moving the wall from `b/a = 1.01`
  outward, the window's equilibrium becomes unstable (`m = 1`) by `b/a = 1.1`. With no wall,
  `min F = −0.079`.

## Verdicts by strand

1. **Vacuum families (S-1 to S-12).**
   - The algebra is correct and reproducible from project data.
   - Theorem 4 is a sound application of KAM persistence: plausible, `known_or_near_known` in
     substance. It does not certify any particular perturbed field, because `ε_N` is existential.
     It does show that the certified twist (`hτ`) makes the Dommaschk tori robust, and it gives
     an explicit, complete, symmetric parametrisation of the vacuum search space around the seed.
   - Every member satisfies contract C1 (vacuum). Contract C2 (QS and omnigeneity) is not
     addressed.
   - S-12 depends on an earlier handoff (`sources/complex_geometry_handoff.pdf`) that the
     project has not assessed.
2. **Geometric identities (S-13 to S-15, S-32).**
   - All are correct and static: they are not Lyapunov functionals, as the source says.
   - S-32 is a short corollary of the compiled Bochner identity.
   - S-15 sharpens the min-B discussion of N-1: a tangent vacuum field cannot have constant
     `|B|` on its boundary.
3. **Cylinder benchmark (S-16 to S-22).**
   - The energy and the mode formula are the classical sharp-boundary model. The explicit window
     and the period-uniform gap are correct and new as far as known.
   - **The close wall is essential.** At `s ≈ 0.16` the wall must be within about 5% of the
     minor radius; the source's sufficient condition puts it at 1%. The result is a
     wall-stabilised benchmark, not a reactor configuration.
   - The toroidal criterion (S-21) is a computable design test (Q-31).
   - The transfer to a torus (S-22) is open (Q-30 (b)).
   - Method note **N-44**.
4. **Kinetic bounds (S-23 to S-31).**
   - The corrected flux is correct, and it complements the compiled `GyroNoether`: that module
     handles a Killing generator with a symmetry defect, this one an exact weak QS with a
     non-Killing generator.
   - The certificate and the hot-core bounds are correct.
   - Applicability needs an exact weak-QS field, whose existence as an equilibrium on a toroidal
     volume is open (Q-16, Q-24), and a certified flux buffer. Without exact weak QS a secular
     parallel term remains.
   - Lean-ready (Q-29). Method note **N-43**.

## Effect on the graph

| Source item | Note | Class | Result |
| --- | --- | --- | --- |
| S-23–S-29 | N-29, N-17 | implemented | method note **N-43**; new **Q-29**; pointers |
| S-16–S-22 | N-12 | implemented (partial) | method note **N-44**; new **Q-30**; pointer |
| S-21 on torus A | N-33 | implemented | new **Q-31** (in N-44) |
| S-10, S-11 | N-31, N-33, N-41 | implemented | new **Q-32**; pointers |
| S-28, S-29 | N-40 | not implemented | edited in place (§ "Hot-core moment fixtures") |
| S-14, S-15, S-32 | N-1 | implemented (partial) | pointer; S-32 lean-ready corollary listed in the RG.3 row of N-42 |
| S-13 | N-32 | implemented (partial) | pointer (non-algebraic bundle) |
| S-9 | contract `FieldTorus`, `NestedTori` | — | audit item **AF-1** (low) |
| S-12, S-33 | — | — | no change (unassessed dependencies; recorded as gaps) |

## Gaps and disagreements

- **No incorrect claims.** The only disagreement is one of emphasis: the cylinder window's
  close-wall hypothesis is much more restrictive than "a close wall" suggests (the stress test
  above).
- **Earlier handoff not assessed.** The "previously established equilibrium obstruction" of the
  weak-QS seed and the "positive-pressure weak MHD lift" come from
  `sources/complex_geometry_handoff.pdf`, which has not been assessed. Next:
  `update notes from sources/complex_geometry_handoff.pdf`.
- **Not checked here:** S-12 (needs the earlier handoff), S-33 (the manuscript is not
  available), (P5), (C8), and the completeness half of Prop. 2.
- **Sign convention.** The source writes `B × u = ∇ψ`; `WeakQS` writes `B × ξ = −∇ψ`.

**Pointer (23 November 2026).** N-48 assesses which of these claims fit the differential-form
kernel (N-45) and compiles two of them: the invariance `L_u ω_B = 0` behind S-23, and for S-2
potentials on simply connected regions together with a field (the straight wire) that has none.

**Pointer (23 November 2026, later).** S-13 is partly compiled (`Theory/Fields/FormHYMLift`,
N-48): the lift `ℱ = β − α ∧ dt` is closed iff the field is a vacuum field, and it is
anti-self-dual in components. The bundle, its Chern class and Yang–Mills minimality are not.
