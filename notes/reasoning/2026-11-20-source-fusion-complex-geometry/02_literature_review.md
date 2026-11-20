# Literature review: "Complex vacuum fields and new stability estimates"

Source: `sources/fusion_complex_geometry_and_stability.pdf` (18 November 2026, no authors named,
supplied through Vamsi Pingali). Locators are the PDF's section numbers and its equation tags
(Q1)–(Q9), (H1)–(H5), (P1)–(P5), (C1)–(C8). In this file, claim IDs are `S-n`. The source's tags
(C1)–(C8) are equation tags, not the contract clauses C1–C5. When the contract is meant, it is
written "contract C1".

## Extraction table

The Kind column follows the skill's list. "Check" refers to `02_examples.md`.

| # | Claim | Locator | Kind | Model, hypotheses, units | Relevance | Check |
| --- | --- | --- | --- | --- | --- | --- |
| S-1 | The Dommaschk QA candidate's potential is `ϑ + F₀`, where `F₀ ∈ ℚ(i)[u^±, v^±, z]` (`u = x+iy`, `v = x−iy`) has 121 monomials coming from 33 nonzero coefficients. `F₀` is harmonic for `q = du dv + dz²`, real (`F₀* = F₀`), even under `(u,v) ↦ (−u,−v)` (2 field periods) and odd under `(u,v,z) ↦ (v,u,−z)` (stellarator symmetry). Its `u⁻⁶` coefficient is `−12674582344287/143360000000000 · i`. | §3.1 | computation (exact) | `R₀ = B₀R₀ = 1` normalisation of `candidate.json` | N-31, N-33, Q-16 | **correct** (exact, independent script) |
| S-2 | Real algebraic class of the fields: `α_G = G dϑ + dF` with `Δ_q F = 0`. The field is real iff `G ∈ ℝ` and `F = F*`. Products of harmonic functions are not harmonic. | §3.1 | definition or model | complexification `(ℂ*)² × ℂ` with real structure `ρ(u,v,z) = (v̄, ū, z̄)` | N-32 | correct (elementary) |
| S-3 | `Q_λ = u + 2λz − λ²v` has a null differential, so every holomorphic `f(Q_λ)` is harmonic. The real level sets are lines with direction `n_λ`. | §3.2 | published theorem with proof (classical minitwistor / Whittaker construction; Hitchin 1982) | — | N-32, Q-24 | correct (sympy, `n ≤ 5`; `n_λ` checked) |
| S-4 | Prop. 1: the `2n+1` coefficients `H_{n,k}` of `Q_λⁿ` form a basis of the homogeneous harmonic polynomials of degree `n`. The real dimension for degrees `≤ N`, modulo constants, is `N(N+2)`. | §3.2 | published theorem with proof (classical) | — | Theorem 4 | correct (harmonic, nonzero and `2n+1` of them for `n ≤ 5`; the dimension identity checked for `N ≤ 20`) |
| S-5 | Prop. 2: `E_pq` and `O_pq` (`p, q` not both negative) form a basis of the harmonic Laurent polynomials. | §3.2 | proof sketch | — | S-1 family | harmonicity correct for `|p|, |q| ≤ 4`; completeness argument read, not checked |
| S-6 | Prop. 3: harmonic polynomials approximate harmonic functions on compact sets with connected complement (Walsh 1929), in `Cʳ` on a smooth solid torus. Hence the polynomial family is dense in the fixed-circulation vacuum class. | §3.3 | published theorem with proof (Walsh, Bull. AMS 35 (1929)) and proof sketch | — | Q-16 (search space) | unverified (standard) |
| S-7 | The seed tori have `ι_A = −(19+√5)/89` and `ι_C = −(85+√5)/361`. The admissibility bound `hτ : c.τ ≤ ‖avg (F.Talg u z)‖` holds with `τ_A = 6997/500` and `τ_C = 141623/10000`. `dommaschk_nested` places torus C inside torus A. | §3.4 | Lean declaration (from this project) | on-demand modules | N-33 | **correct**: matches `DommaschkKamDio.dkIotaA`, `DommaschkKamDioC.dkIotaC`, `tauC` in `DommaschkKamAAdmOut` and `DommaschkKamCAdmOut`, `KamFlowIterationG.AdmBoundsG.hτ`, `ExactTorusA.adm`, `DommaschkKamNested.dommaschk_nested` |
| S-8 | The averaged torsion is the shear of the linearized full-turn return map, `(a,b) ↦ (a − 2π⟨T⟩b, b)`, so the seed tori are twist tori. | §3.4 | proof sketch | exact torus, Diophantine `ι` | N-33, Q-31 | plausible; not re-derived in the project's frame conventions |
| S-9 | The certified invariant parametrisations are embedded tori: immersion plus injectivity by a winding-number argument. | §3.4 | proof sketch | `R > 0`, nonsingular normal frame, winding 1 | N-33 | plausible; whether `NestedTori` or `FieldTorus` already implies embeddedness was not checked |
| S-10 | **Theorem 4.** For every `N` there is `ε_N > 0` such that every `B_a = B₀ + ∇Σ a_j P_j` with `|a| < ε_N` (`P_j` harmonic polynomials of degree `≤ N`) has two nested analytic invariant tori with the same `ι_A`, `ι_C`. Field lines stay in the outer solid torus for all time, the toroidal flux is positive, and distinct `a` give distinct outer domains. There is an infinite-dimensional analytic version. | §3.5 | proof sketch (applies the published a-posteriori KAM theorem of de la Llave–González–Jorba–Villanueva 2005, Thm 1) | exact symplectic return maps; twist from S-8; `ε_N` not quantified | G-1, contract C1, Q-16, N-33, N-41 | plausible; see the stress test |
| S-11 | Symmetric families `h_m = Im(x+iy)^{2m}` and `k_m = z Re(x+iy)^{2m}` are harmonic and keep 2 field periods and stellarator symmetry. | §3.5 | complete mathematical proof | — | N-31 | correct (checked by hand: even under `R`, odd under `S`, harmonic) |
| S-12 | The perturbed tori satisfy the boundary-flow hypotheses of a "previously derived positive-pressure weak MHD lift" (Enciso–Luque–Peralta-Salas type), giving positive-pressure weak equilibria with surface currents. | §3.6 | proof sketch, relying on an earlier handoff that the project has not assessed | analytic Diophantine boundary flow | Q-14, Q-20 | unverified (dependency not available here) |
| S-13 | A vacuum field `B` gives `ℱ = β − α∧dt` on `Ω × S¹_ℓ`. `dℱ = 0` iff `B` is vacuum, and `ℱ` is anti-self-dual for every `B` (orientation `dx dy dz dt`). It is the curvature of an Abelian Hermitian–Yang–Mills connection with `c₁` period `−Γℓ/2π`. The bundle is not algebraic, `∫|ℱ|² = 2ℓ∫|B|²`, and the energy is minimal against fixed-boundary variations. | §4 | complete mathematical proof | static, fixed boundary | N-32, N-37, Q-24 | correct; the orientation agrees with patch N-37 (`β + dt∧α` is ASD for `vol₃ ∧ dt`) |
| S-14 | For a vacuum field with `‖∇B‖ ≤ δλ` on `∂Ω` (`0 < δ < 1`), `Q = −log det(I + ∇B/λ)` is positive, subharmonic, and comparable to `|∇B|²/λ²`. | §5 | complete mathematical proof | vacuum, bounded smooth domain | N-1 | correct (re-derived by hand) |
| S-15 | A nonzero vacuum field tangent to `∂Ω` cannot have constant `|B|` on `∂Ω`. | §5 | complete mathematical proof | bounded smooth domain | N-1, Q-16 | correct (re-derived; uses Hopf's lemma and the farthest-point convexity comparison) |
| S-16 | The complete ideal-MHD `2δW` for a constant-pressure periodic cylinder (`B_i e_z`) with a vacuum gap (`B_e e_z + B_θ (a/r) e_θ`), a fixed ideal wall at `r = b`, and fixed fluxes. The interface term is `−B_θ²/(μ₀a)`. | §6 | published theorem with proof (the classical sharp-boundary / surface-current model, e.g. Freidberg, *Ideal MHD*) | ideal MHD, lossless, fixed fluxes | G-4, Q-3, Q-14 | correct (curvature jump re-derived; it matches the classical form) |
| S-17 | Exact mode coefficient `F_mn = κI_m/I_m' + ((kaB_e + mB_θ)/B_i)² n_out − B_θ²/B_i²`, with `F_m0` in closed form via `coth(|m| log(b/a))`. | §6.1 | published theorem with proof (classical) | — | Q-3 | correct (numerical) |
| S-18 | An unstable branch: if `B_e ≥ B_i` and `B_θ ≠ 0`, then `m = 1`, `k = −B_θ/(aB_e)` has `F < 0` whatever the wall distance. | §6.2 | complete mathematical proof | `k` allowed by the period | Q-3 | correct (numerical and by hand) |
| S-19 | **Window.** If `0 < s ≤ 1/4`, `B_θ² = sB_i²`, `B_e² = (1 − 3s/4)B_i²` and `ℓ + sD/β_e² ≤ s/8` (for example `1 < b/a ≤ 1 + s/16`), then `F_mn ≥ s²/8` for `m ≠ 0`, `F_0n ≥ 2 − s`, and `F_00 = 2 − s + γs/4 + β_e²/D + s/ℓ`. | §6.3–6.4 | complete mathematical proof | close ideal wall | G-4, Q-3, Q-30 | correct (numerical scan); `F_00` not checked |
| S-20 | Uniform interface gap: `F_mn ≥ (s²/80)(1 + |m| + a|k|)`, uniform in the period `L`. | §6.5 | complete mathematical proof | as S-19 | Q-30 | correct (numerical scan) |
| S-21 | **Toroidal criterion.** For a vacuum core with interface field `Y` and exterior `X = Y + r g⁻¹d + o(r)` along KAM graphs, the conditions `ω·d > 0` and `II(Y, g⁻¹d) < 0` give `p > 0` and a positive surface term for small `r`. Feasibility is a one-dimensional affine condition in `σ`. | §7 | proof sketch | first order in `r`; relies on the Enciso–Luque–Peralta-Salas construction | Q-14, Q-20, G-4, Q-31 | first-order terms re-derived; `o(r)` uniformity not checked |
| S-22 | Transfer to a torus: a variational reduction (harmonic Neumann field, Jensen), and a sufficient certificate (Hessian change below half the cylinder gap, uniformly in `L`). | §8 | proposal or plan | — | Q-30 | n/a (open) |
| S-23 | Weak QS (`div B = div u = 0`, `B × u = ∇ψ`, `u·∇|B|² = 0`) implies `[B,u] = 0`, `tr S = 0` and `bᵀSb = 0`, where `S = sym ∇u`. | §9.1 (Q1)–(Q2) | published theorem with proof (Burby–Kallinikos–MacKay; Constantin–Drivas–Ginsberg) | `C³` | N-27, N-29 | correct (by hand) |
| S-24 | Explicit tensorial solution `C` of the gyrophase homological equation `[C,K] = S`, with `‖C‖_F ≤ ‖S‖_F`. | (Q3)–(Q4) | complete mathematical proof | `b` unit, `S` traceless with `bᵀSb = 0` | N-29, Q-29 | **correct** (symbolic) |
| S-25 | `J = ψ − εu·v + ε²vᵀDv` (`D = C/|B|`, `ε = m/q`) satisfies exactly `J' = ε² Σ v_iv_jv_k ∂_kD_ij` along prescribed-field Lorentz orbits. | (Q5)–(Q7) | complete mathematical proof | `E = 0`, static `B`, weak QS | N-29, N-17, G-6, Q-29 | **correct** (cancellation checked symbolically) |
| S-26 | Deterministic certificate: `|Δψ| ≤ 2A(V) + |t−s|R(V)`. With a flux buffer `Δ > 2A + TR`, no orbit leaves the region before `T_cert = (Δ − 2A)/R`, and `T_cert/Δ` scales like `Λ²` under `B ↦ ΛB`. | (Q8)–(Q9) | complete mathematical proof | `ψ = ψ_b` on `∂Ω`, `ψ < ψ_b` inside | G-6, G-2, Q-29 | correct (re-derived) |
| S-27 | Exact relativistic version of S-25 and S-26. | §9.1 | complete mathematical proof | `E = 0` | G-6 | correct (time reparametrisation) |
| S-28 | Hot core: for prescribed-field Vlasov with an absorbing wall and initial Maxwellian, `f = M` on the core for `|v| ≤ V` and `t ≤ T`. Hence `n ≥ a(c)n₀` and `Θ/Θ₀ ≥ b(c) − d(c)²/(3a(c)²)` (`c = V/σ`). The constants are `a(2.8) > 0.95056321`, the ratio is `> 0.82577125` at `c = 2.8` and `> 0.88757292` at `c = 3`. | §9.2 (H1)–(H3) | complete mathematical proof | mild solution, Newtonian | G-2, G-6, Q-28 | correct (numerical) |
| S-29 | Perturbed initial data `(1±δ)M` give (H4), and the directional temperature bound (H5); the constants are given. | (H4)–(H5) | complete mathematical proof | — | G-2 | correct (numerical) |
| S-30 | Exact terms for `E` and `δB` (P1)–(P2), for collisions (P3)–(P4), and a weak-form Landau bound (P5). | §9.3 | (P1)–(P4) complete mathematical proof; (P5) proof sketch | prescribed fields or collision generator | G-7, Q-28 | (P1)–(P2) correct by hand; (P5) unverified |
| S-31 | The covariant derivative `𝔇_i = ∂_i + R_{(∂_ib)×b}` removes the field-direction commutator ((C1): only `∂_iΩ_c` remains). The cyclotron-frequency shear cannot be removed by a periodic gyro gauge. There is a global frame on the solid torus (C6)–(C7), and an Ornstein–Uhlenbeck modified energy estimate (C8). | §9.4 | (C1)–(C7) complete mathematical proof; (C8) proof sketch for a model operator | — | G-7, N-19 | (C1) correct (by hand: `a_i × b = −∂_i b`); others unverified |
| S-32 | A vacuum field of constant magnitude is constant. | §9.4 | complete mathematical proof | connected open set | N-1, Q-16 | correct; it follows from the compiled Bochner identity `laplacian_normSqField` |
| S-33 | An auxiliary-PDE (fiberwise quaternionic Monge–Ampère) mechanism from an OpenAI manuscript on wave-equation local smoothing gives an elliptic, not time-monotone, identity. | §2 | proposal or plan (secondary reading of a cited manuscript) | — | N-19 (context) | unverified; the manuscript is not available here |
| S-34 | Parameter illustration: `n = 10²⁰ m⁻³`, `Θ = 12.5 keV` and `B_i = 5 T` give `p ≈ 4.005 × 10⁵ Pa`, `s ≈ 0.16107`, `β ≈ 0.0403`, `B_e ≈ 4.688 T` and `B_θ ≈ 2.007 T`. | §10 | numerical observation | cylinder only | G-4 | correct (numerical) |
| S-35 | A source-level audit of `6312f1c` found 227 modules in the import closure of `DommaschkKamNested`, with no `sorry`, axiom or `native_decide`. The Lean build was not rerun. | §1, §3.6.1 | numerical observation (provenance audit) | — | RG.4 | consistent with the project's own checks (the 4 November axiom check; the on-demand Dommaschk modules are under the workstation policy) |

The source's own caveats, recorded faithfully:
- the three positive results use different configurations;
- `ε_N` is not quantified;
- the cylinder is not an embedded torus;
- the buffer inequality (Q9) is not certified for any device;
- the Lean build was not rerun;
- self-consistent fields, collisions, heating, coils and walls are outside the scope.

## Source study of the substantive results

### Theorem 4 (S-10): harmonic perturbation families keep the certified tori

- **Structure.**
  1. The return maps of `B_a` on annuli around the seed tori are exact symplectic. The flux 2-form
     `ι_B vol` is closed, and `H²(solid torus) = 0`.
  2. The seed tori are twist tori. Nonzero averaged torsion (S-8) comes from the compiled
     `AdmBoundsG.hτ`.
  3. The a-posteriori KAM theorem for exact symplectic maps with fixed Diophantine rotation gives
     invariant circles for `|a| < ε_N`.
  4. Suspension gives the tori, and smallness keeps embedding and nesting.
  5. Invariance of the closed solid torus gives all-time confinement of field lines.
  6. Green's identity gives distinct domains.
- **Hypotheses and what breaks without them.**
  - Without exactness, a perturbation with net flux would drift the circles, and fixed rotation
    could not be kept.
  - Without twist, the KAM theorem does not apply. This is why the compiled `hτ` matters.
  - Without the Diophantine rotation, no persistence.
- **Core idea.** The certified tori are robust KAM tori. Adding any small gradient of a harmonic
  polynomial keeps the field a vacuum field (so contract C1 holds automatically) and keeps two
  nested invariant tori with the same rotational transforms.
- **Assessment.**
  - The argument is the standard persistence of KAM tori, so it is `known_or_near_known` in
    substance. What it adds for the project is the explicit, complete algebraic parametrisation of
    the perturbation space.
  - The radius `ε_N` is existential. No design claim can be made for a given `a` without a new
    certificate, that is, a rerun of the N-33 pipeline.
  - The project's certificate pipeline is a-posteriori: it proves tori for one explicit field.
    Theorem 4 therefore adds a qualitative family, not a certified member.
  - Quasisymmetry and omnigeneity (contract C2) are not preserved in any quantitative sense.
- **Stress test** (`10-conjecture-stress-test` classification): **plausible**, and
  `known_or_near_known` as a persistence statement. Extra hypothesis needed for any use here: a
  quantified `ε_N`, or a direct certificate for the chosen member.

### Cylindrical window (S-16 to S-20)

- **Structure.**
  1. The mode-by-mode energy is the classical sharp-boundary model.
  2. Lower bounds on `κI_m/I_m'` come from the power series.
  3. A lower bound on the vacuum impedance comes from a radially constant trial potential in the
     dual principle.
  4. Cauchy's inequality `t²/A + (1−t)²/B ≥ 1/(A+B)` finishes the argument.
  5. A separate eigenvalue bound gives the `H^{1/2}` gap.
- **Hypotheses and what breaks without them.**
  - **The close wall** (`ℓ + sD/β_e² ≤ s/8`; `b/a ≤ 1.01` at `s = 0.161`). Without it the vacuum
    term no longer compensates the curvature term in the least favourable helicity. Whether the
    window fails for a far wall is checked numerically in `02_examples.md`.
  - **`B_e < B_i`** (the exterior axial field slightly smaller than the interior one). S-18 shows
    the opposite choice is unstable.
  - **Fixed fluxes.** These are needed for the `(0,0)` mode.
- **Core idea.** Let the azimuthal exterior field carry the pressure: a stabilising
  internal-field-line-bending term `κI_m/I_m'`, plus a vacuum term that is large exactly when
  the curvature term matters, so that Cauchy's inequality balances them.
- **Technique.** Bounding by explicit lower bounds on special-function ratios and a dual
  variational (trial-function) estimate; Cauchy–Schwarz splitting; mode-by-mode (Fourier)
  reduction of a quadratic form. These are registry techniques: "energy principle and coercivity",
  "bounding". The dual trial-function bound for a Neumann impedance is worth adding to the
  "energy principle" entry as a worked example.
- **Lean readiness.** Mathlib has no modified Bessel functions. The inequality chain from
  explicit lower bounds (`X ≥ κ²/(m + κ²/(2(m+1)))`, `n ≥ 1/(m²ℓ + κ²D)`) to `F ≥ s²/8` is
  elementary real algebra and lean-ready now: state the Bessel and impedance quantities as
  hypotheses (the supplied-reduction pattern). The Bessel series bounds themselves would need a
  new library. This is Q-30 (a).
- **Stress test:** **plausible / correct** as a theorem in the stated model. For a reactor reading
  it **needs extra hypotheses**: a wall within about 1% of the minor radius, and a periodic
  cylinder rather than a torus.

### Corrected full-orbit flux and the absorbing-core certificate (S-23 to S-28)

- **Structure.** (Q2) gives `bᵀSb = 0`. Then (Q4) solves the homological equation tensorially,
  (Q7) is an exact cancellation, (Q8) integrates, and (Q9) is a first-hit argument.
- **Core idea.** For exact weak QS the canonical-like momentum `ψ − εu·v` has defect
  `−εvᵀ(sym ∇u)v`. That defect is purely gyrophase-oscillating (its gyro-average vanishes because
  `bᵀSb = 0` and `tr S = 0`), so a quadratic-in-velocity corrector removes it exactly, leaving a
  cubic `ε²` remainder.
- **Relation to compiled work.**
  - The project's `gyroNoether_hasDerivAt` / `gyroNoether_band` (`Theory/Kinetic/GyroNoether`)
    corrects a *symmetry defect* `δ = B × K + ∇ψ` for a **Killing** field `K`. There the momentum
    defect is `qv·δ`, and the corrector is linear in `v`.
  - S-25 is the complementary case: an **exact** weak QS with a **non-Killing** `u`. Here the
    defect is `vᵀSv`, and the corrector is quadratic in `v`.
  - Sanity case: a Killing `u` (exact symmetry) has `S = 0`, so `C = D = 0`, `J = ψ − εu·v`, and
    `J' = 0`. This is `canonicalMomentum_conserved` / `noetherMomentum_conserved`, up to the sign
    convention: `WeakQS` uses `B × ξ = −∇ψ` and the source uses `B × u = ∇ψ`.
  - Combining the two correctors (a weak-QS defect plus a non-Killing generator) is a natural
    lemma.
- **Hypotheses and what breaks without them.**
  - Exact weak QS on a whole toroidal domain with a non-Killing `u`. The existence of such
    *equilibria* is open (Q-16, Q-24), and the source admits its seed has an equilibrium
    obstruction. Without exact weak QS, `u·∇|B|² ≠ 0` and `bᵀSb ≠ 0`: the homological equation is
    unsolvable for the `bb` component, and a secular term `ε vᵀ(bbᵀSbbᵀ)v` (a parallel-velocity
    drift) remains. This is the term that must be compared with the project's QS-defect bounds
    (N-29, N-34).
  - `ψ` constant on `∂Ω`.
- **Technique.** Near-identity normal-form correction (a homological equation for the
  fast-rotation operator `R_b`), followed by a first-hit barrier argument. Registry: "invariants"
  and "comparison and barriers"; the Noether/gyro-correction pattern is already used in
  `GyroNoether`.
- **Lean readiness.** (Q4) is finite-dimensional linear algebra. (Q7) is a derivative identity
  along supplied orbits, like `gyroNoether_hasDerivAt`. (Q8) and (Q9) parallel `gyroNoether_band`
  and `gyroNoether_trapped_until`. All are lean-ready now: Q-29.
- **Stress test:** **correct** (complete proof, algebra checked). As a confinement claim for a
  device it **needs extra hypotheses**: an exact weak-QS field, a certified buffer, and constants
  `U₀`, `D₀`, `D₁` for an actual field.

### Toroidal interface criterion (S-21)

- **Core idea.** To first order in the step amplitude `r`, the pressure jump is `r ω·d` and the
  surface term is `−2r II(Y, g⁻¹d)`. Choose the direction `d` of the KAM graph so that both have
  the right sign.
- **Re-derivation.**
  - `|X|² − |Y|² = 2r g(Y, g⁻¹d) + O(r²) = 2rω·d`.
  - `II(X,X) − II(Y,Y) = 2r II(Y, g⁻¹d) + O(r²)`.
  - The signs match the source's conditions.
- **Use.** This is a computable design test on a certified torus of the Dommaschk field (Q-31).
  On a certified torus, `g`, `II` and `ω` are explicit. The test is a pair of sup/inf conditions
  on a one-parameter family, and a failure has a one- or two-point witness, which suits certified
  evaluation. Positivity of the surface term with a vacuum core and a vacuum exterior makes every
  term of `δW` nonnegative. It is not coercive.
- **Stress test:** **plausible**. It needs the Enciso–Luque–Peralta-Salas existence of the KAM
  graphs (an analytic, Diophantine boundary flow) and the `o(r)` uniformity.

### Smaller results

- **S-14, S-15, S-32 (vacuum geometry).**
  - All are correct and elementary.
  - S-32 is a five-line corollary of the compiled Bochner identity (lean-ready).
  - S-15 needs Hopf's lemma, which is not in Mathlib.
  - Relevance: they rule out "constant `|B|`" shortcuts to QS (Q-16) and belong next to N-1.
- **S-13 (ASD/HYM lift).**
  - Correct. It complements N-32 and N-37.
  - The non-algebraicity remark (`Pic((ℂ*)²) = 0`) is a new and correct observation.
  - It is a static identity, not a Lyapunov functional (the source says so).
- **S-30, S-31 (collisions, covariant derivatives).** A research programme for G-7. The key
  barrier is identified: the cyclotron-frequency shear (`∂_iΩ_c`) cannot be gauged away
  periodically.
