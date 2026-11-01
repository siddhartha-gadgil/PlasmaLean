# Certified quasi-axisymmetry defect on the certified Dommaschk torus, and the path to C2

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-34` |
| Title | Design study: a contract-level QA defect on one certified invariant torus of the Dommaschk target, its certificate cost, and an assessment of the path to C2 |
| Kind | definition / research approach / certificate design (with untrusted numerics and a small Lean prototype) |
| Addresses | `Q-16` (vacuum criterion: certified tori, ι ≥ ι_min, certified QA defect small relative to ι), `Q-23` (link Boozer `ξB` to the actual field), `Q-21` (C2 model contract), `G-10`, `G-1` |
| Depends on | N-33 (`dommaschk-kam-certificate.md`, C1 done), N-31 §§24–29, N-30 §2 (vacuum Boozer angles), N-29 (bridge), N-27. Lean: `DommaschkKamC.dommaschk_iotaOnTorus_unconditional`, `dk_exact_of_res`, `ExactTorusC`, `dk_adm`/`dk_hadmC` and the Adm chain (`DommaschkKamCAdm*`), `DommaschkKamIdent` (`Dp_ident`, `nRp_ident`, `nZp_ident`), `Kinetic.Boozer.approxOmnigenousOn_of_defect_le`, `symmetryDefect`, `TwistOn`, `twistOn_qa_of_iota_ge`, `Contract.OmnigeneityContract`, `Fields.qsError`, `WeakQSDefect`, `Theory/KAM/InvSqrtApprox` |
| Dependency requirement | C1 chain: compiled (on demand, standard axioms). Bridge: compiled (default build) **in the supplied Boozer GC model**. Everything numerical here: untrusted |
| Produces | The recommended definition (§2); the untrusted estimator `scripts/dommaschk_kam/qs_defect.py`; the prototype `PlasmaLean/Design/DommaschkQSProto.lean` (on demand, not imported); a cost estimate (§4); a C2 assessment with one audit finding (§5); a module plan (§6) |
| Difficulty | per-torus defect: moderate (routine certificate on existing infrastructure, plus about 1 kLOC of new torus geometry); oracle-normalised spectral bound: moderate (weighted Wirtinger on T²); C2 for the actual field: research (no volume Boozer chart exists for a non-integrable field) |
| Status | proof-ready design for the per-torus defect (go); C2: blocked on a contract decision and on new theory |
| Lean evidence | A1 `Theory/Fields/VacuumBoozerTorus` (`torusQADefect`, `boozerJac_eq_normSq_div`, `exists_qa_of_torusQADefect_eq_zero`, `boozerAngles_bijective`, `symmetryDefect_eq_torusQADefect_vacuum`) and D3 `Design/DommaschkKamCQSPoly` (`qsDefect_eq_real`), default build; earlier: | prototype only: `PlasmaLean.Design.DommaschkQSProto.{boozerX_thetaB, boozerX_phiB, boozerX_apply, boozerX_qa, boozerVec_eq, bijective_of_strictMono_bdd, coeff_sq_le}` (on demand, not imported; standard axioms; 1.5 s, 1.3 GB) |
| Audit evidence | not audited. §5.1 is a candidate audit finding (C2 has no link between `BoozerField` and the physical field) |
| Last updated | 1 November 2026: created |

## Purpose and scope

C1 is proved for the exact Dommaschk QA target on one KAM torus (torus C, ι_C = −(85+√5)/361,
r_eff ≈ 0.02). The QS numbers of the fit are untrusted. Q-16 asks, in vacuum, for certified tori
with ι ≥ ι_min and a certified QA defect small relative to ι; C2 asks for omnigeneity. This note
answers: (1) which per-torus defect to formalise and how it relates to the oracle, to `WeakQS`
and to the Boozer model of the bridge; (2) what its certificate costs; (3) what C2 needs beyond
one torus; (4) a module plan.

**Model and conventions.** Vacuum field `B = ∇Φ`, `Φ = φ + V`, `V` single-valued
(`DommaschkQA2R.field candidate`), cylindrical `(R, φ, z)`, model units (`B ≈ 1.07`, `R ≈ 0.9`),
NFP = 2. The torus is `K(θ, φ) = (R, z)(θ, ψ)` with the strip angle `ψ = 2φ (− π/2 in Lean)`;
lines are `t ↦ (θ + ιt, φ + t)`, `𝓛 = ∂_φ + ι∂_θ`; ι < 0. (In §5 `ψ` also denotes the toroidal
flux of the Boozer model; the meaning is always stated.)

**Out of scope.** ε_eff, collisions, E_r, finite orbit width; a certificate for further tori.

## Dependencies

- **Compiled, on demand:** `dk_exact_of_res`/`ExactTorusC` (exact torus, `Close (9/1400)` to the
  data torus, covering `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z`, μ = 10⁻¹²), `dk_adm` (all admissibility bounds
  for every μ-close torus from the 24 × 28 surrogate chain), `inv_R`/`inv_Z` (`D 𝓛K = n`),
  `Bphi_ne`, `R_pos`, the identifications `Dp_ident` (`D = R⁷B_φ`), `nRp_ident`, `nZp_ident`
  (`n = R⁸B_{R,z}`).
- **Compiled, default build:** the bridge `approxOmnigenousOn_of_defect_le` (Boozer GC model,
  supplied), `qsError`, `WeakQSDefect`, `InvSqrtApprox.invSqrt_approx_bound`.
- **Proved informally (N-30 §2), to be formalised here:** in vacuum `φ_B = Φ`,
  `θ_B = θ_s + ι(φ_B − φ)`, Jacobian `|B|²/B^φ`.
- **Untrusted:** the oracle and every number in §3–§4.

## Sources and prior work

- Boozer, Phys. Fluids 24 (1981) 1999 (Boozer coordinates); Helander, Rep. Prog. Phys. 77 (2014)
  087001, §§3–4 (QS in Boozer angles, `B = G∇φ_B + I∇θ_B + K∇ψ`).
- Rodríguez, Helander, Bhattacharjee, Phys. Plasmas 27 (2020) 062501 (arXiv:2004.11431) and
  Constantin–Drivas–Ginsberg arXiv:2009.08860 (weak QS; generator `e_{φ_B}` up to scaling).
- Nemov et al., Phys. Plasmas 6 (1999) 4622 (ε_eff; not used).
- Repository: N-30 §2 (vacuum Boozer angles, validated numerically), N-29 (bridge), N-33.

## Theory development

### 1. The Boozer angles on one invariant torus (complete argument; partly in the prototype)

Let `K` be an invariant torus with frequency `(ι, 1)`, `ι` irrational, and `v = V ∘ K`
(periodic). Put

    φ_B = φ + v,   θ_B = θ + ι v.

- **Straight field lines.** Along a line, `dθ_B/dφ = ι + ι𝓛v = ι dφ_B/dφ`. So `(θ_B, φ_B)` are
  straight-field-line angles with toroidal angle `Φ|_K`. In vacuum `B = 1·∇Φ` with `I = 0`, so
  these are the Boozer angles (`G = 1`); unique up to constant shifts for irrational ι.
- **No V is needed.** Since `B = ∇Φ` and `∇φ·∂_θK = 0`, `∇φ·∂_φK = 1`:

      a := v_θ = B·∂_θK,      J := 1 + v_φ + ι v_θ = B·𝓛K = |B|²/B^φ.

  The last equality uses invariance `𝓛K = B/B^φ`. `J` is the Jacobian `∂(θ_B, φ_B)/∂(θ, φ)`,
  with mean exactly 1.
- **The Boozer toroidal direction.** The torus vector field
  `X = (−ι v_φ ∂_θ + (1 + ι v_θ) ∂_φ)/J` satisfies `X θ_B = 0`, `X φ_B = 1`. So
  `X = ∂_{φ_B}|_{θ_B}` (`boozerX_thetaB`, `boozerX_phiB`). Pushed forward to space
  (`boozerVec_eq`):

      e_{φ_B} = B/|B|² − ι (∂_θK − (b·∂_θK) b),    b = B/|B|.

  It is tangent to the torus and depends only on `B` and `∂_θK` along the torus.
- **The defect function.** For `f = |B| ∘ K` (`boozerX_apply`):

      g := ∂_{φ_B}|_{θ_B} |B| = (1 + ι a) 𝓛f / J − ι ∂_θ f
         = (b·∇|B|)/|B| − ι (∇_⊥|B|)·∂_θK          (∇_⊥ = component perpendicular to B).

  The first form uses only derivatives along the torus. The second shows `g = qsError B e_{φ_B}`
  at torus points when `|B|` is differentiable there. Numerically the two terms partly cancel
  (sup 0.0118 and 0.0064; total 0.0090), so `g` must be certified as one series.
- **Global invertibility (the diffeomorphism question).** In the coordinates `(α, φ)`,
  `α = θ − ιφ` (the field-line label), the angle map is `(α, φ) ↦ (α, φ_B)`. Here
  `∂φ_B/∂φ|_α = 1 + 𝓛v = J`, and `φ_B − φ = v` is bounded. If `J > 0` on the torus, each fibre
  map is a strictly increasing bijection of ℝ (`bijective_of_strictMono_bdd`). So
  `(θ, φ) ↦ (θ_B, φ_B)` is a bijection of ℝ², equivariant under `(2π, 0)` and `(0, π)`, hence a
  bijection of the torus. Smoothness of the inverse follows from the inverse function theorem
  (`J ≠ 0`).
  - `J > 0` holds iff `B_φ > 0` on the torus, because `J = |B|²R/B_φ`. The C1 chain proves
    `B_φ ≠ 0` (`Bphi_ne`). The sign follows by connectedness and one positive value, or from
    `D ≥ D_min > 0`. On torus C, `J ∈ [0.921, 1.052]`.
- **QA characterisation without the full inverse.** `∂_θ θ_B = 1 + ιa ∈ [0.9986, 1.0011]` on
  torus C. So the mixed chart `(θ, φ) ↦ (θ_B, φ)` is also a bijection (1-D monotone in `θ`). In
  it, `∂_φ|_{θ_B} = (J/(1 + ιa)) X`. Hence `g ≡ 0` ⇔ `f` is constant in `φ` at fixed `θ_B` ⇔
  `f = F(θ_B)`. The direction ⇐ is `boozerX_qa`.

### 2. Recommended contract-level definition

**Definition (torus QA defect).** For a vacuum field `B` and an invariant torus `K` with
frequency `(ι, 1)`:

    torusQADefect B ι K (θ, φ) := [(1 + ι B·∂_θK) 𝓛(|B|∘K) − ι (B·𝓛K) ∂_θ(|B|∘K)] / (B·𝓛K),
    TorusQADefectLe B ι K δ  :⇔  ∀ θ φ, |torusQADefect B ι K (θ, φ)| ≤ δ.

The certified Q-16 numbers are then: ι; `δ_∞` (sup); `B_min`; and optionally `δ_2`, the
`L²(J dθ dφ)` norm of the same function.

**Why this one.**
- It is exactly the hypothesis `hξ` of the bridge, restricted to one surface. In the Boozer model,
  QA is helicity `(N, M) = (0, 1)` and `symmetryDefect F 0 1 = F.Bφ = ∂_{φ_B}B`.
- It needs no flux label, no volume chart and no inverse map, so it is honest on one torus.
- It is a polynomial expression in the certified torus data (§4).

**Relations.**
1. **(c) Boozer GC model.** If a `BoozerField F` comes from a Boozer chart in which the surface
   `ψ = ψ_j` is the torus `K_j` (§5), then
   `F.Bφ(ψ_j, θ_B(θ, φ), φ_B(θ, φ)) = torusQADefect B ι_j K_j (θ, φ)`. This is the chain rule plus
   `X = ∂_{φ_B}`.
2. **(b) `WeakQS`.** `torusQADefect = qsError B ξ` with `ξ = e_{φ_B}` on the torus.
   - `B × e_{φ_B} = ∇ψ` holds in Boozer coordinates. Its derivation is not formalised; it would
     need a volume chart.
   - `div e_{φ_B} = −2 ∂_{φ_B}|B|/|B|`. So in `WeakQSDefect` form `δ₂ = δ_∞`, `δ₀ = 2δ_∞/B_min`,
     and `δ₁` is 0 (the cross condition) only once a volume chart exists.
   - The torus defect is therefore the surface trace of the `δ₂` component. The other two
     components need a volume.
3. **(a) Oracle Boozer spectrum.** The oracle defines `c_mn = ⟨f J e^{−i(mθ_B − nNφ_B)}⟩` over the
   KAM grid (`fieldeval.boozer_coeffs`), `A_mn = 2|c_mn|`, `B00 = c_00`, and
   `defect = sqrt(Σ_{n≠0} A_mn²)/B00` (half lattice). Then

       defect · B00 = sqrt(2 Σ_{n≠0, full} |c_mn|²) ≤ (√2/N) ‖g‖_{L²(J)} ≤ δ_∞/√2      (N = 2).

   **Proof.**
   - The `e_mn ∘ (θ_B, φ_B)` are orthonormal in `L²(J dθ dφ)`, because
     `e_pq J = [∂_θ(e_pq ∂_φθ_B) − ∂_φ(e_pq ∂_θθ_B)]/(iqN)` for `q ≠ 0` (and similarly with
     `φ_B` for `q = 0`, `p ≠ 0`), and the integral of a periodic divergence is 0.
   - `X` preserves `J dθ dφ`: `∂_θ(−ιv_φ) + ∂_φ(1 + ιv_θ) = 0`. So `c_mn(g) = inN c_mn(f)`.
   - Bessel's inequality gives the first bound (`coeff_sq_le` is the scalar step). The second is
     `‖g‖_{L²(J)} ≤ sup|g|` with `⟨J⟩ = 1`.
   - `B00 = ⟨fJ⟩ ≥ B_min` gives `defect ≤ δ_∞/(√2 B_min)`.
   - This bounds the **full** off-QA spectrum, not the oracle's truncation `m, |n| ≤ 8`.
   - The proof needs only the KAM-chart formula for `c_mn`, not the inverse map. That formula
     is the oracle's own definition, so no change of variables is needed.
4. **Q-16 ratio and the bridge constant.** The dimensionless ratio of the bridge is
   `κ = 2δ_∞/(B_min |ι|)`, and N-29 calls the bound useful for `κ < 1`. Report `κ` and the
   oracle-normalised `defect/|ι|`, which is bounded via (3).

### 3. Untrusted numerics on torus C (`scripts/dommaschk_kam/qs_defect.py`)

The script uses the 96 × 80 oracle torus (`results/20261101T015838Z/torus_C_N96_M80.json`,
candidate sha checked) on a 256 × 256 grid, with the exact field polynomials, central
differences for `∇|B|`, and the exact `V` for the spectrum cross-check.

```
python scripts/dommaschk_kam/qs_defect.py [--n 256] [--trunc 24,28]     # 0.3 s; needs numpy
```

Consistency checks:
- invariance error `6.5e-15`;
- `|J − |B|²/B^φ| = 1.4e-15` and `|J − (1 + 𝓛v)| = 9e-15`;
- `|a − v_θ| = 2e-16` and `⟨J⟩ = 1.000000`;
- the coordinate-free formula agrees to `4e-15`;
- the Boozer reconstruction error is `3e-7` with `m, |n| ≤ 16`.

| quantity (torus C, ι = −0.24165) | value |
| --- | --- |
| `|B|` range; `B00` | [1.04886, 1.10124]; 1.07319 |
| `J` range; `1 + ιa` range | [0.9212, 1.0519]; [0.99864, 1.00112] |
| oracle-form defect `sqrt(Σ_{n≠0}A²)/B00` (m, \|n\| ≤ 8 / ≤ 16) | 4.50e-4 / 4.57e-4, i.e. **defect/\|ι\| = 0.00186** (oracle at r = 0.024: 0.00182) |
| `δ_∞ = sup|g|` (256² / 512² grid) | 9.00e-3 / 9.02e-3 |
| `ℓ¹(ĝ)` at ρ = 0 / ρ = 0.045 | 0.01981 / 0.02839 |
| `ℓ¹` of `∂_{φ_B}|B|²` / (2 B_min) | 0.02051 |
| `δ_2 = ‖g‖_{L²(J)}` | 2.115e-3 |
| bound (3) via `δ_2` / via sup / via ℓ¹ (÷ \|ι\|) | 0.0058 / 0.0245 / 0.054 |
| `κ` via sup / via ℓ¹ | 0.071 / 0.156 |
| largest Fourier coefficient of `g` | `|ĝ_{0,±6}| = 5.4e-4` (so sup|g| ≥ 8.5e-4: torus C is certifiably not exactly QA) |
| surrogate truncation | 24 × 28 and 16 × 20 change `δ_∞, δ_2, ℓ¹` by < 1e-8; 12 × 12 by 3e-6 |

**Findings.**
1. **The oracle's Lean-form δ is too small by a factor of 1.8.** `diagnostics.py` reports
   `lean_qa_delta = sup|∂_{φ_B}B|` from Boozer modes `m, |n| ≤ 8` only. Recomputed this way on
   the exact torus it gives 0.0051, against the true 0.0090 (with 16 modes it converges). The
   modes with `8 < m ≤ 16` carry little amplitude but large `nN` weight. So the oracle's κ column
   (N-31 §§21–24) is optimistic by about 2×. The spectral defect itself is unaffected.
2. **The norm decides the tier.**
   - The ℓ¹ norm, which a ball chain certifies directly, loses 2.2× against the sup. Through (3)
     it gives `defect/|ι| ≤ 0.054`, just above the moderate tier (0.05).
   - The `L²(J)` route gives 0.0058, the strong tier (≤ 0.01), about 3× above the true 0.00186.
   - A sharper certified sup (sampling with a Bernstein bound) would need about 10⁶ exact point
     evaluations, so it is not recommended.
3. **κ < 1 comfortably** (certified value ≈ 0.17), so the bridge would give a non-trivial (but
   worst-case, N-29) per-bounce bound.
4. **Low resolution suffices.** The defect needs about 1e-4 relative accuracy, against the
   1e-27 of the residual. The 24 × 28 surrogate of the admissibility chain (`dk_adm`) is enough,
   and so is a 16 × 20 one.

### 4. Certification cost (question 2)

**Polynomial form** (flow-form data, `u = R − R₀`, `D = R⁷B_φ`, `n_{R,z} = R⁸B_{R,z}`):
- `|B|² = Q/R¹⁶` with `Q = n_R² + R²D² + n_z²`, and `J = Q/(R⁸D)`.
- On the exact torus invariance gives `D𝓛Q = Q_u n_R + Q_z n_z + D Q_φ =: P_L`.
- With `M_L = R P_L − 16 Q n_R`:

      ∂_{φ_B}|B|² = N_g / (Q R¹⁷),   N_g = R⁸M_L + ι[(n_R M_L − Q(RQ_u − 16Q)) u_θ + (n_z M_L − RQ Q_z) z_θ].

  Here `Q_u, Q_z, Q_φ` are polynomial in `(u, z, cos 2φ, sin 2φ)`. So `N_g` is a polynomial in
  `(u, z, c, s)` that is **linear in `(u_θ, z_θ)`**. No `𝓛` of a ball and no Cauchy estimate is
  needed.
- `g = ∂_{φ_B}|B|²/(2|B|)`. Either:
  - bound by `ℓ¹(∂_{φ_B}|B|²)/(2B_min)` (+3.5 %); or
  - use `InvSqrtApprox` for `|B|⁻¹ = R⁸Q^{−1/2}` (sharp).
- `δ_2² = ⟨(∂_{φ_B}|B|²)² R⁸/(4D)⟩`. This is one strip-algebra average (the `(0, 0)` coefficient)
  and needs `q_D ≈ 1/D`, which the Adm chain already has (`‖q_D D − 1‖ ≤ 4.7e-9`).
- `B_min² ≥ c − ‖Q R⁻¹⁶ − c‖₀`. On torus C this gives `B_min ≥ 1.0426` (true 1.0489).

**Chain** (extension of the Adm chain: same 24 × 28 surrogate, same environment, monomials
`RᵃZᵇ`, `D, n_R, n_z` and their `∂_u, ∂_z` already certified). New nodes:

| group | nodes |
| --- | --- |
| `∂_φ D, ∂_φ n_R, ∂_φ n_z` (exact polynomial derivative; `polyT` chunks of ≤ 4 monomials, no products) | ≈ 50 |
| `Q, Q_u, Q_z, Q_φ` (reusing `RD`) | ≈ 17 products |
| `P_L, M_L, P0, P1, P2, N_g` | ≈ 14 |
| `q_Q ≈ 1/Q` (centre data), norm node, `q_R^{16}, q_R^{17}` by squaring, `∂_{φ_B}|B|²` | ≈ 10 |
| `|B|²` and its `ℓ¹` deviation node, `D_min` node (sign of `J`) | ≈ 3 |
| `δ_2²` average (3 products and a `(0,0)` read) | ≈ 4 |
| **total** | **≈ 95 nodes, images ≤ 5 Mbit** |

- **Weights.** Unit weights (ρ = 0) for the new nodes give the sup bound directly (ℓ¹ 0.0198
  against 0.0284 at ρ = 0.045). Adm balls at ρ = 0.045 are reused through `Bd` monotonicity.
- **Magnification.** `R^{−17} ≤ 29` and `Q ≈ 0.04–0.85` magnify truncation radii by ≤ 10³. With
  `2^{-64}` rounding and intermediate boxes of about 32 × 36 the radii stay ≤ 1e-6, against
  `δ ≈ 2e-2`.
- **Transfer to the exact torus.** The inputs `(u, z, u_θ, z_θ)` of the exact torus are within
  `μ + tail ≈ 1e-11` of the surrogate at ρ = 0. This uses `Close (9/1400)`, `Bd` monotonicity,
  the tail lemmas `Bd_tg_U/Z` and the existing `∂_θ` tails 7.2e-12. A crude per-node Lipschitz
  propagation (product rule with certified node norms, constants ≤ 10⁶) adds ≤ 1e-5. Two
  options:
  - a generic "perturbed chain" lemma (about 300 lines, reusable for further tori);
  - majorant Lipschitz constants as in `admO_near`.

**Cost** (scaled from the measured Adm chain: 182 nodes in about 19 min, ≤ 2.9 GB):

| component | modules | CPU | peak |
| --- | --- | --- | --- |
| `∂_φ` polynomials and `Q`-structure identities (DkPoly checks) | 1–2 | 1–2 min | ≤ 2.5 GB |
| centre data (about 95 centres at 24 × 28, `2^{-64}`; about 2 MB source) | 2–3 | 10 s | ≤ 1 GB |
| env, trees, rel, chain, out | 5 | 1 min | ≤ 2 GB |
| check modules (`kron2_proof`, 8–10 modules) | 8–10 | 10–14 min | ≤ 3 GB |
| transfer, identification with `torusQADefect`, final | 3 | 1–2 min | ≤ 2.5 GB |
| **total (on-demand top module)** | **≈ 20** | **≈ 15–20 CPU-min** | **≤ 3 GB** |

This is laptop-buildable, with no workstation run needed and no new oracle run.

**Expected certified values:**
- `δ_∞ ≤ 0.021`; with `InvSqrtApprox`, ≤ 0.020;
- `B_min ≥ 1.042` and `κ ≤ 0.17`;
- `δ_2 ≤ 2.13e-3`, hence (with §6 module A2) oracle-normalised **`defect/|ι| ≤ 0.0060`**, the
  strong tier, against the untrusted 0.0019;
- without A2: `defect/|ι| ≤ 0.059` (not a tier) from `δ_∞`;
- lower-bound fixture: `δ_∞ ≥ 8e-4` (torus C is not exactly QA).

### 5. Beyond one torus: the path to C2 (question 3)

#### 5.1 Contract gap (candidate audit finding, high when a Dommaschk C2 claim is made)

`Contract.OmnigeneityContract F c κ` is a statement about an arbitrary `F : BoozerField`. Nothing
ties `F` to the physical field.
- `constField_omnigeneityContract` shows that it is satisfiable for any candidate by an
  unrelated `F`.
- The normative spec (`00-model-contracts.md`, C2: "a chart (Boozer or other straight-field-line
  angles) whose existence is proved") requires this link. The open audit item "C1/C2 common
  witness" (AR-L) is the same gap.
- **Fix to decide.** C2 for a candidate should read `∃ F, BoozerModelOf B Ω F ∧
  OmnigeneityContract F c κ`. Here `BoozerModelOf B Ω F` asks for:
  - a C¹ map `x : (0, c] × T² → Ω`, a diffeomorphism onto the region;
  - `Φ ∘ x = φ_B` (vacuum), with `F.G = 1`;
  - each `x(ψ, ·, ·)` an invariant torus of `B`, with transform `F.ι(ψ)` and toroidal flux `ψ`;
  - `F.B = |B| ∘ x`.
- The sanity triad still holds: axisymmetric fields have such charts.

#### 5.2 Why a volume chart for the actual field is the crux

- **The bridge needs a region.** It needs `|∂_φB| ≤ δ` on all of `0 < ψ ≤ c`, because trapped
  orbits drift across surfaces.
- **The field is not integrable.** A KAM family exists only on a Cantor set of ι. Between tori
  there are island chains, so `BoozerModelOf` is **unsatisfiable** for this field on any open
  region that contains a resonant surface.
- **Inside torus C** (ι from −0.2417 to about −0.2452 on the axis) every resonance has
  period-map order `q ≥ 33` (the lowest is ι = −8/33). So the islands are exponentially small
  (Fourier decay `0.62^33 ≈ 1e-7`), but not absent.
- **Between C and A** lies ι = −6/25 (order 25), with islands of uncertain width.
- So an exact chart exists only for integrable fields. For this field C2 needs an
  **approximate** chart and a guiding-centre theorem that tolerates its defect.

#### 5.3 Options, shortest first

| route | what is proved | new work | audit value |
| --- | --- | --- | --- |
| **R0 (this note)** per-torus Q-16 | certified `ι`, `δ_∞`, `B_min`, `κ`, oracle-normalised defect on torus C | §6 A1–A7 | full (no model) |
| **R1** Boozer surrogate | `OmnigeneityContract F_s c κ` for an explicit integrable `F_s` built from certified tori (e.g. axis + torus C, or tori C and A, interpolated in ψ); exact agreement `F_s.B = |B|∘K_j` on the certified surfaces | Boozer representation `F_j = |B|∘K_j∘(θ_B, φ_B)⁻¹` (global inverse, §1); certified toroidal flux `ψ_j = ∮ α` along the poloidal loop (the flux primitive `P_a, P_b, P_c` exists in `FlowFieldG`, so this is one chain average); `F_s = (1 − t)F_C + tF_A` gives `|∂_φF_s| ≤ max δ_j` by convexity; the negative-ι twist lemma (open AR-M1: ι < 0 here) or a mirror reflection | low–medium: the surrogate is the actual field only on the certified surfaces. Comparable to `reactorQA` (truncated near-axis field without remainder). Must be labelled a model, not C2 for the field |
| **R2** approximate Boozer chart | per-bounce drift bound in the Boozer model with a field-line tangency defect `ε_∥ = sup|b·∇ψ̃|` | a polynomial chart `x(ψ, θ_B, φ_B)` from a family of approximate tori (ParamInterp-style interpolation in ψ); 3-D cell certificates of `ε_∥` and `∂_φ|B|`; a **new GC theorem**: ψ̇ gains the streaming term `v_∥ b·∇ψ̃`, so per bounce `|Δψ| ≤ (2H/(|q|B_min ι_min)) δ τ + v τ ε_∥`, useful only if `ε_∥ ≲ ρ*·δ` (about 1e-5) | high, but it needs the Boozer GC model's derivation in non-flux coordinates (not in Lean) |
| **R3** physical GC model | approximate helical-momentum conservation in the Littlejohn model (`Kinetic/GuidingCentreLittlejohn`) from `WeakQSDefect (δ₀, δ₁, δ₂)` on a volume (Burby–Kallinikos–MacKay) | new theory (Q-23 open item "link `ξB` to `WeakQS`"), plus the volume certificate of R2 | highest; research |

**Assessment.**
- **R0 is ready now.**
- **R1 is the shortest C2-type statement:** about 2 agent-weeks after R0, given one more torus
  (or the magnetic axis). The magnetic axis is a periodic orbit, a cheap Newton–Kantorovich
  certificate, and its `|B|`-variation is itself a QA defect. R1 adds little beyond the per-torus
  numbers, because the model is free between the surfaces.
- **R2/R3 are research,** with unknown feasibility of `ε_∥ ≲ 1e-5` across a region containing
  any order-≤ 30 resonance. A realistic target is the core inside torus C, where all resonances
  have `q ≥ 33`.
- **The region is small.** Torus C has `r_eff ≈ 0.02` (aspect ratio about 45); the fit's nested
  region ends at `r_eff ≈ 0.053`. Even a full C2 proof would cover a thin core. Tori further out
  (B-type, near 3/13, θ-decay 0.47) are much harder to certify (N-31 §25).

**"Certified tori on a nested region"** (the Q-16 wording) needs at least two nested certified
tori.
- **Candidates:**
  - A (ι = −(19+√5)/89, r ≈ 0.037, needs about 104 × 84, N-33 §3.4);
  - an inner torus D with ω = [0; 8, 4, 1̄] (ι ≈ −0.2434, r ≈ 0.018: smaller `W₀`, so a larger κ,
    but faster decay).
- **Cost per torus:** about the C1 chain (residual about 12 min wall, ≤ 5.4 GB; admissibility
  about 26 CPU-min; defect about 15 min), plus a workstation oracle run.
- **Nesting certificate.** Both tori must be radial graphs over a common reference curve, with
  ordered radii. This extends `radial_ge_of_close`.

### 6. Module plan (question 4)

All modules are new. "A" modules are theory in the default build; "D" modules are on demand,
not imported by `PlasmaLean.lean`.

| # | Module | Content | Where / cost |
| --- | --- | --- | --- |
| A1 | `Theory/Fields/VacuumBoozerTorus` (default) | `boozerPhiVec`, `torusQADefect`, `TorusQADefectLe` (torus-intrinsic form); vacuum Boozer angles `φ_B = Φ∘K`, `θ_B = θ + ι(φ_B − φ)`; `X θ_B = 0`, `X φ_B = 1`; `J = B·𝓛K = |B|²/B^φ`; `torusQADefect = qsError B e_{φ_B}` when `‖B‖` is differentiable; QA ⇔ `|B|∘K = F∘θ_B` (mixed chart, needs `1 + ι a > 0`); bijectivity of the angle map from `J > 0` (from the prototype); sanity triad: degenerate `B = ∇φ`, circle torus, defect 0; exact QA ⇒ 0; rejected: a non-QA instance with `g ≠ 0` | laptop, light; about 700 lines |
| A2 | `Theory/Fields/BoozerWirtinger` (default) | KAM-chart Boozer coefficients `c_mn = ⟨f J e_mn⟩`; orthonormality by the divergence identity; `X`-invariance of `J dθ dφ`; Bessel ⇒ `Σ_{n≠0}|c_mn|² ≤ ‖g‖²_{L²(J)}/N²`; the oracle-normalised corollary `defect ≤ (√2/N) δ_2/B00 ≤ δ_∞/(√2 B_min)` | laptop, moderate; 800–1200 lines (intervalIntegral, Fubini on a box, `Orthonormal.sum_inner_products_le`) |
| D3 | `Design/DommaschkKamCQSPoly` | `∂_φ` of `Dp, nRp, nZp`; `Qp`, `Qp_u`, `Qp_z`, `Qp_φ`, `N_g` structure as DkPoly identities; emitter `scripts/dommaschk_kam/emit_qs.py` (exact checks first) | laptop ≤ 2.5 GB |
| D4 | `Design/DommaschkKamCQSData1–3`, `…QSEnv`, `…QSTrees`, `…QSCheck1–10`, `…QSRel`, `…QSChain`, `…QSOut` | the chain of §4 on the Adm surrogate, unit weights; certified `ℓ¹(∂_{φ_B}|B|²)`, `B_min`, `D_min`, `δ_2²` | laptop, about 15 CPU-min, ≤ 3 GB (WS rebuild task optional) |
| D5 | `Design/DommaschkKamCQSTransfer` | surrogate ⇒ every μ-close torus (perturbed-chain lemma or majorants), `Bd 0 ⇒` pointwise bounds | laptop, light |
| D6 | `Design/DommaschkKamCQSIdent` | on `ExactTorusC`: `|B|∘K = √(Q(K))/R⁸` (from `Dp/nRp/nZp_ident`), derivatives along the torus through `eval` of `dTh`/`Lt` and the chain rule, `B_φ > 0`, hence `torusQADefect (field candidate) ι_C K = eval(N_g/(2Q^{3/2}R⁹))` | laptop, moderate (about 500 lines; the main new Lean analysis of D3–D7) |
| D7 | `Design/DommaschkKamCQS` (top) | **`dommaschk_qaDefect_unconditional`**: `∃ R z`, `IotaOnTorus (field candidate) R z ι_C` ∧ `TorusQADefectLe … (21/1000)` ∧ `B ≥ 1.042` on the torus ∧ `κ ≤ 0.17`; with A2, `dommaschk_boozerDefect_le`: oracle-normalised defect ≤ `0.0060 |ι_C|`; fixture `δ_∞ ≥ 8e-4` | laptop |

**Order.** A1 → (D3 ∥ A2) → D4 → D5 → D6 → D7. A1, D3–D7 need no workstation. The R1 surrogate
(§5.3) comes after D7 and one more torus. **Shared files (coordinator):** `PlasmaLean.lean` (A1,
A2), `scripts/check_axioms.lean` (A1, A2), `scripts/check_axioms_heavy.lean` (D7).

### 7. Open mathematical gaps

1. **Contract (§5.1).** There is no `BoozerModelOf` link in C2. This is a decision for the
   coordinator and the audit lane, before any C2 claim for a candidate.
2. **The Wirtinger bound with weight `J` (A2).** The mathematics is complete (§2(3)); it needs
   formalisation.
3. **The sign of `J`.** It needs `B_φ > 0`, not only `≠ 0`. This is a connectedness argument or a
   `D_min` node.
4. **Negative ι in the bridge.** `twistOn_qa_of_iota_ge` assumes `ι ≥ ι_min > 0`; here ι < 0.
   Use AR-M1 or a reflection `φ ↦ −φ` (only relevant for R1+).
5. **Volume chart and GC theory for near-integrable fields (R2/R3).** This is open research. A
   new question is proposed: "approximate Boozer chart with certified non-integrability defect
   and a drift theorem tolerating it".
6. **Resonance widths between certified tori.** An untrusted island-width scan at ι = 6/25 and
   inside torus C is the cheap next numeric that would inform R2.

## Claims and evidence

1. **Complete mathematical argument** (§1), with its algebraic core **compiled in the prototype**
   (`boozerX_thetaB`, `boozerX_phiB`, `boozerX_apply`, `boozerX_qa`, `boozerVec_eq`):
   - in vacuum, on an invariant torus, `e_{φ_B} = B/|B|² − ι(∂_θK)_⊥` and
     `∂_{φ_B}|B| = (1 + ιa)𝓛|B|/J − ι∂_θ|B|`, with `J = B·𝓛K = |B|²/B^φ`;
   - the angle map is a bijection when `J > 0` (`bijective_of_strictMono_bdd` for the 1-D step;
     the inverse function theorem for smoothness is not done).
2. **Complete mathematical argument** (§2(3)). The oracle Boozer defect obeys
   `defect · B00 ≤ (√2/N)‖g‖_{L²(J)} ≤ δ_∞/√2`, for the full spectrum. Only the scalar step
   (`coeff_sq_le`) is compiled.
3. **Numerical observations** (untrusted, `qs_defect.py`), on torus C:
   - `δ_∞ = 0.0090`, `ℓ¹ = 0.0198`, `δ_2 = 0.00212`;
   - oracle-form `defect/|ι| = 0.00186`;
   - `κ = 0.071` (sup) and 0.156 (ℓ¹);
   - the oracle's truncated Lean-form δ underestimates the true value by 1.8×.
4. **Cost estimate** (extrapolated from the measured Adm chain): about 95 nodes, 15–20 CPU-min,
   ≤ 3 GB, laptop.
5. **Contract observation** (§5.1). `OmnigeneityContract` is not linked to the physical field.
   This is a candidate audit finding.

## Difficulty, barriers and readiness

- **Lean-ready now:** A1 (definitions and the torus geometry), D3–D5 (the chain is a routine
  extension of `DommaschkKamCAdm*`), A2 (independent).
- **D6** is the only part with new analysis: derivatives of `|B|∘K` along the exact torus and
  `B_φ > 0`.
- **Barriers:**
  - for R0: none beyond engineering;
  - for C2: the contract link, and the non-integrability of the field (§5.2).

**Smallest next step:** A1 together with the emitter `emit_qs.py`. The emitter reuses
`emit_adm.py`/`adm_ball.py` and reproduces the §3 numbers from the surrogate in exact ball
arithmetic before any Lean is written.

## Outputs and next dependencies

**Files:**
- this note;
- `scripts/dommaschk_kam/qs_defect.py` (untrusted estimator);
- `PlasmaLean/Design/DommaschkQSProto.lean` (prototype, on demand, not imported; standard
  axioms).

**Suggested registry updates (coordinator):**
- **N-34 row:** depends on N-33, N-30, N-29; status "proof-ready design (go) for the per-torus
  defect".
- **Q-16:** "per-torus certified QA defect designed (N-34): expected `κ ≤ 0.17`,
  oracle-normalised `defect/|ι| ≤ 0.006` with A2. A nested region needs a second certified
  torus".
- **Q-23:** "torus-level identification of `ξB` with `qsError B e_{φ_B}` designed (N-34 §2)".
- **New audit item:** C2 lacks a `BoozerModelOf` link (§5.1).
- **N-31 §§21–24 κ column:** optimistic by about 2× (§3, finding 1).
- **Proposed new question:** an approximate Boozer chart and a drift theorem with a
  non-integrability defect (§5.3, R2/R3).
- **Edges:** N-33 → N-34 → Q-16, Q-23.

**Go/no-go.**
- **GO** for R0: A1, D3–D7, and A2 for the strong-tier, oracle-normalised claim.
- **NO-GO for a C2 claim about the actual field** until §5.1 is decided. R1 (the surrogate)
  only with explicit model labelling. R2/R3 as research.

**Risks.**
1. Without A2 the certified Q-16 ratio is only 0.059 (ℓ¹), which misses the moderate tier.
2. Node radii: magnification by `R^{−17}/Q` (≤ 10³) is estimated, not measured. Fallback:
   centre the polynomials in `u` and use `q_R` products early.
3. D6 effort, especially derivatives along the exact torus.
4. Over-reading: a per-torus defect and `κ < 1` are not omnigeneity. The bridge is a worst-case
   per-bounce bound in a supplied model (N-29). Even a full chain would cover only
   `r_eff ≲ 0.02–0.05`.

## Update (1 November 2026): A1, A2, D3 formalised

A1 `Theory/Fields/VacuumBoozerTorus`, A2 `Theory/Fields/BoozerWirtinger` (`torus_oracleDefect_le`, full spectrum, sharp constant √2/N; sign correction c_mn(g) = −inN c_mn(f)) and D3 `Design/DommaschkKamCQSPoly` are in the default build. Remaining: D4/D5 (ball chain, in progress), D6 (identification on `ExactTorusC`, including B^φ > 0 and 2π/N periodicity for `BoozerChartHyp.of_torus`), D7.

## Update (2 November 2026): D4–D7 done (sup route)

`dommaschk_C1_qaDefect`, `dommaschk_C1_oracleDefect` (on-demand `Design/DommaschkKamCQS`): certified
δ_∞ = 0.020642, B_min = 1.04259, κ ≤ 0.165, oracle defect ≤ 0.0141 (≈ 0.058 |ι|). The certified
δ₂ = 0.00224 (L² route, ≈ 0.0063 |ι|, strong tier) awaits two identities: 4g²J = F/((q_G Q R¹⁷)²(q_D D))
pointwise, and the torus average as the strip `avg`. Remaining risk statement unchanged: one thin
torus; no C2 (AC-1).

## Update (2 November 2026): D7 L² route done

`dommaschk_C1_oracleDefect_L2` (on-demand `Design/DommaschkKamCQSL2`): defect ≤ (√2/2)δ₂/B_min < 0.0016 ≈ 0.0063 |ι| (strong tier). Scope unchanged: one thin torus, no C2 (AC-1).

