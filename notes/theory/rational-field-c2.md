# C2 diagnostics for the rational stellarator vacuum field (Q-19)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-30` |
| Title | Omnigeneity (C2) diagnostics for `RationalStellarator.field (1/4)`: Boozer spectrum, quasisymmetry defect, ε_eff, and a first-order obstruction |
| Kind | computation / counterexample (obstruction) |
| Addresses | `Q-19`; clause C2 of the stellarator contract; `G-10`, `G-1`, `Q-16` (Dommaschk route) |
| Depends on | N-9 (`first-stellarator-rung.md`), N-10 (`kam-route.md`), N-29 (`omnigeneity-bridge.md`). Lean: `RationalStellarator.field`, `field_vacuum`, `axis_fieldLine`, `rationalStellarator_confined_forever` (ι_A = (75 + √5)/562); `Kinetic.Boozer.approxOmnigenousOn_of_defect_le` (for the κ column) |
| Dependency requirement | Field definition and vacuum property: compiled. KAM torus A: compiled. Everything computed here: **untrusted numerics**. The Boozer facts of §2 are **proved informally** |
| Produces | Numbers (ι profile, Boozer spectra, QS defects, ε_eff); the closed-form first-order QA defect `sqrt(ι₀/N)` (proved informally); verdict on C2; recommendation for Q-16 |
| Difficulty | moderate (numerics routine; the obstruction is a short near-axis computation) |
| Status | exploratory (numerics) / proof-ready (first-order obstruction) |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 30 October 2026: created |

## Purpose and scope

C1 + C4 hold for the rational vacuum field in the vacuum model: the field is current-free, it has
ι ≈ 0.137 on a KAM-certified torus, and field lines inside that torus are confined forever. C2 asks
whether trapped thermal particles have zero, or small, bounce-averaged radial drift. This note
measures that numerically, as an untrusted oracle. It also explains the result by a near-axis
obstruction.

- **Model.** The field is `B = ∇Φ`, `Φ = φ + ε h`, with `ε = 1/4` and h as in N-9 §0. Units are
  R₀ = B₀ = 1, and |B| = 1 exactly on the circular axis.
- **Particle model.** Collisionless guiding centres, through the standard ε_eff (1/ν) functional.
- **Out of scope.** Finite β, finite orbit width, and alphas (Q-1, Q-4).

## Dependencies

- `field_vacuum` and `axis_fieldLine` are compiled.
- Torus A is compiled (`rationalStellarator_confined_forever`). The other tori are numerical
  observations from N-9 and N-10, reproduced here.
- The Boozer guiding-centre model of N-29 is a supplied model. Its `ξB` is a Boozer-chart defect;
  linking it to this field's Boozer chart is not formalized.
- The Nemov ε_eff formula is a sourced definition. It is not in Lean (Q-21 / N-29 "next
  dependencies").

## Sources and prior work

- **ε_eff.** V. V. Nemov, S. V. Kasilov, W. Kernbichler, M. F. Heyn, *Phys. Plasmas* 6 (1999) 4622,
  Eqs. (29)–(31). The formula was recalled from memory, then checked (§3.3) against the
  classical-stellarator limit ε_eff = ε_h, the normalization property of that definition.
- **First-order near-axis quasisymmetry.**
  - D. A. Garren, A. H. Boozer, *Phys. Fluids B* 3 (1991) 2805, 2822.
  - M. Landreman, W. Sengupta, *J. Plasma Phys.* 84 (2018) 905840616. Their σ equation is
    `σ′ + (ι₀ − N)(η̄⁴/κ⁴ + 1 + σ²) − 2(η̄²/κ²)(I₂/B₀ − τ)G₀/B₀ = 0`.
- **Omnigeneity near the axis.** G. G. Plunk, M. Landreman, P. Helander, *J. Plasma Phys.* 85
  (2019) 905850602. **Lead:** with constant on-axis |B|, first-order omnigeneity reduces to
  first-order quasisymmetry. This is recalled, not re-checked.
- **Typical ε_eff values (order of magnitude, from memory, to be checked against primary sources
  before citing).**
  - W7-X standard configuration: ε_eff ≲ 1 % over most of the radius (Beidler et al.,
    *Nature* 596 (2021) 221).
  - LHD: about 1–2 % (inward-shifted, R_ax = 3.6 m) to several % (R_ax = 3.75 m).
  - HSX (QHS): about 0.5 % or less.
  - NCSX: about 1 %.
  - Landreman–Paul precise QA/QH (*Phys. Rev. Lett.* 128 (2022) 035001): ε_eff ≲ 10⁻³.
  - Axisymmetric tokamak: 0.
  - Classical l = 2 stellarators (W7-A era): ε_eff ≈ ε_h, several %.

## Theory development

### 1. Method (scripts in `scripts/c2_diagnostics/`, untrusted)

- `field.py`: the field in cylindrical coordinates, from sympy, with a polynomial fast path.
  - Self-checks: the axis is a field line with |B| = 1; ∇·B = 0 symbolically; the polynomial and
    sympy right-hand sides agree to 4×10⁻¹⁷.
- `tori.py`: tori and ι.
  - Integration: RK4 in φ, 200 steps per field period (π), vectorized over lines.
  - ι comes from a weighted Birkhoff average (Das–Saiki–Sander–Yorke) of the poloidal angle about the
    exact axis, using 2000 section points.
  - Halving the step changes ι by ≤ 3×10⁻⁹.
  - The section conjugacy K(θ_s) is a 40-mode Fourier fit with θ_s(k) = kπι.
- `boozer.py`: the Boozer spectrum, using exact Boozer angles (§2). There are 128 lines from
  uniform θ_s, each followed over one period with 128 samples.
  - The coefficients are `c_mn = (2π²)⁻¹ ∬ |B| (|B|²/B^φ) e^{−i(mθ_B − n N φ_B)} dα dφ`, with
    N = 2 field periods.
  - Checks: the mean Boozer Jacobian is 1 to 10⁻¹⁰. The reconstruction error of |B| from
    m, |n| ≤ 16 is 3×10⁻¹¹ (r = 0.05) to 10⁻⁵ (r = 0.40).
- `nemov.py` and `eps_eff.py`: ε_eff, using 8 lines per surface, 150 toroidal transits each, and
  300 values of b′.
  - Exact inputs: `∇ψ = r_α × B` and `|∇ψ| k_G = (B × ∇|B|)·∇ψ / B²` (vacuum). The tangent
    vector r_α is carried by the variational equation from K′(α).
  - Convergence: the half-length and full-length values agree to 0.2 %, and 20 transits already
    give the same values to 2 %. The maximum of |∇ψ| is the same after 20 and 150 transits, so r_α
    shows no secular drift.
- Cost: under 5 CPU-minutes in total, one process at a time.

### 2. Exact Boozer angles for this field (proved informally)

The field is vacuum and B = ∇Φ, where Φ − φ = εh is single-valued and the torus encloses no toroidal
current. Hence the covariant Boozer representation is `B = G∇φ_B` with G = 1 and **φ_B = Φ = φ + εh**.

Straight-field-line coordinates with a prescribed toroidal angle are unique up to a shift when ι is
irrational. Hence **θ_B = θ_s + ι ε h**, where θ_s is the straight-field-line angle for the
cylindrical φ.

Along a field line, `dφ_B/dφ = |B|²/B^φ`. So the Jacobian is
`∂(θ_B, φ_B)/∂(θ_s, φ) = 1 + ε (dh/dφ)_line = |B|²/B^φ`. No Boozer transform code is needed.
Both checks in §1 confirm this.

### 3. Results (numerical observation)

#### 3.1 ι and the tori

| launch r (φ = 0, outboard) | r_eff | ι |
| --- | --- | --- |
| axis | 0 | 0.1339746 (exact 1 − √3/2) |
| 0.05 | 0.053 | 0.1344898 |
| 0.10 | 0.104 | 0.1360051 |
| **0.13073** (torus A) | 0.135 | **0.1374307 = (75 + √5)/562** |
| 0.20 | 0.201 | 0.1420838 |
| 0.287 (≈ torus B) | 0.279 | 0.1510525 |
| 0.36 | 0.340 | 0.1617253 |
| 0.40 | 0.370 | 0.1690106 |

The KAM-certified ι_A is reached at launch radius 0.130734, by bisection on the Birkhoff ι. N-10
quotes r = 0.131.

#### 3.2 Boozer spectrum and quasisymmetry defect

Modes are written (m, n) with |B| ∋ cos(mθ_B − nNφ_B), N = 2. The QS defect for helicity (M, Nh) is
`sqrt(Σ_{mNh − nM ≠ 0} A_mn²)`. It is reported in two ways: divided by B₀₀, and as a fraction of
the whole non-constant spectrum.

| r | A₁₀/B₀₀ | A₁₁/B₀₀ | A₂₀/B₀₀ | best helicity | defect/B₀₀ | fraction | next best | Lean QA δ = sup\|∂_{φ_B}B\| | κ = 2δ/(B_min ι) | ε_eff |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0.05 | 0.0549 | 0.0147 | 8e-4 | (1, 0) QA | 0.0147 | 0.259 | (1, 1): 0.966 | 0.030 | 0.48 | 0.0097 |
| 0.10 | 0.108 | 0.0288 | 3e-3 | QA | 0.0289 | 0.258 | 0.966 | 0.062 | 1.04 | 0.020 |
| 0.1307 (A) | 0.140 | 0.0372 | 5e-3 | QA | **0.0373** | **0.258** | 0.966 | 0.082 | 1.44 | **0.027** |
| 0.20 | 0.208 | 0.0552 | 0.013 | QA | 0.0556 | 0.258 | 0.967 | 0.136 | 2.5 | 0.045 |
| 0.287 | 0.287 | 0.0764 | 0.028 | QA | 0.0778 | 0.260 | 0.967 | 0.221 | 4.4 | 0.071 |
| 0.36 | 0.347 | 0.0940 | 0.047 | QA | 0.0971 | 0.267 | 0.966 | 0.312 | 6.6 | 0.099 |
| 0.40 | 0.376 | 0.104 | 0.062 | QA | 0.109 | 0.274 | 0.965 | 0.417 | 9.0 | – |

All other helicities tested ((0, 1), (1, −1), (1, ±2), (2, ±1), (1, ±3)) have fraction ≥ 0.999.

- The spectrum is that of a tokamak-like (1, 0) modulation, i.e. toroidal 1/R, plus one helical
  sideband (1, 1).
- The sideband ratio is constant to 3 digits.
- The best helicity is QA. Its defect is about 26 % of the |B| variation at every radius, so it
  does not decrease towards the axis.
- At torus A, defect/ι ≈ 0.27.
- The worst-case Boozer-model factor κ of N-29 exceeds 1 already at r ≈ 0.1. So the per-bounce
  theorem `approxOmnigenousOn_of_defect_le` gives no useful bound here.

#### 3.3 ε_eff (validation and values)

- **Validation.** The same code was run on the classical model
  `b = 1 − ε_t cos θ − ε_h cos Nφ`, with |∇ψ|k_G = r sin θ/R₀.
  - Analytically, ε_eff^{3/2} → (9/2) A ε_h^{3/2}, where `A = ∫₀¹ [E(k) − (1−k²)K(k)] k dk = 2/9`
    (numerically 0.222222). Hence **ε_eff = ε_h**, the known normalization.
  - The code gives ε_eff/ε_h = 1.026 (ε_h = 0.02, ε_t = 0.002) and 1.013 (ε_h = 0.01). The
    remainder is the finite-ε_t correction.
- **Values.** ε_eff is in the table above (R₀ = B₀ = 1; 150 transits; half-length values within 0.2 %).
  - It is about 2.7 % at torus A (aspect ratio ≈ 7.4).
  - It is about 7 % at r_eff ≈ 0.28 and about 10 % at r_eff ≈ 0.34.
  - **ε_eff ≈ 0.2 r_eff**, linear in r, which is the signature of an O(r) defect.
  - This is classical-stellarator level, 3–10× the W7-X value at comparable radius, and much larger
    than optimized QA/QH (10⁻³).

### 4. The obstruction: a planar circular axis forces an O(r) QA defect (proved informally)

**Claim.** Consider the rotating-ellipse family of N-9 §1.3, with N field periods, the exact circular
axis R = 1, z = 0, and on-axis transform ι₀ = N/2 − κ_N, where κ_N = sqrt(N²/4 − 4ε²). At first
order in the distance r from the axis, |B| in Boozer angles is

`|B| = 1 − r [ |Q| cos(θ_B + q) + |P| cos(Nφ_B − θ_B + p) ] + O(r²)`, with `|P|² = N ι₀`, `|Q|² = N (N − ι₀)`.

So the non-QA fraction of the first-order |B| variation is exactly **sqrt(ι₀/N)**. For N = 2 and
ε = 1/4 this is sqrt(0.13397/2) = **0.2588**, and the sideband ratio is
sqrt(ι₀/(2 − ι₀)) = 0.2680. The numerics give 0.259 and 0.2676 at r = 0.05.

**Proof sketch.**
1. |B| = 1/R + O(r²), because εh = O(r²). Also θ_B = θ_s + O(r²) and φ_B = φ + O(r²).
2. The linearized flow is `v = Rot(Nφ/2) w`, `w′ = M w`, with `M = [[2ε, N/2], [−N/2, −2ε]]`.
3. M has eigenvector `a = (N/2, iκ_N − 2ε)` for the eigenvalue iκ_N.
4. Writing `V = x + iz`, the invariant tori are
   `V = e^{iNφ/2}(P e^{iϑ} + Q e^{−iϑ})·r`, with `ϑ = θ₀ + κ_N φ`,
   `P = (N/2 − κ_N − 2iε)/2` and `Q = (N/2 + κ_N − 2iε)/2` (up to normalization).
5. The straight-field-line angle is `θ_s = (N/2 − κ_N)φ − θ₀`. Then `e^{i(Nφ/2 − ϑ)} = e^{iθ_s}` and
   `e^{i(Nφ/2 + ϑ)} = e^{i(Nφ − θ_s)}`.
6. Finally `|P|² = (N/2 − κ_N)² + 4ε² = Nι₀` and `|Q|² = N(N − ι₀)`, using `4ε² = N²/4 − κ_N²`.

**Interpretation.** This is the Garren–Boozer statement specialized to this family. With a planar
axis (τ = 0) in vacuum (I₂ = 0), the σ equation for QA reads `σ′ = −ι₀(1 + σ² + η̄⁴/κ⁴) < 0`, which
has no periodic solution unless ι₀ = 0. QH is unavailable because the normal of a planar convex
curve does not rotate.

So, at first order:
- **no** vacuum field whose magnetic axis is a planar circle can be quasisymmetric with ι₀ ≠ 0;
- in this family the defect is pinned at sqrt(ι₀/N), so the ratio defect/ι = 1/sqrt(N ι₀) grows as
  ι₀ → 0. The Q-16 criterion (defect small relative to ι) fails **structurally** for every member.

On the circle |B| = 1/R = 1 is constant along the axis. If the Plunk–Landreman–Helander lead holds,
first-order omnigeneity then reduces to first-order QS, and the obstruction extends from QS to
omnigeneity (lead, not checked).

### 5. Can more harmonics help?

- **Higher-order terms in h that keep the circular axis** (the l = 3, 4 content, more Laurent
  completions): no at O(r). The first-order |B| depends only on (N, ε), i.e. on the linearized
  rotating ellipse. Adding such terms can only change the O(r²) part. The constant 26 % in §3.2 is
  the O(r) term.
- **Larger N at fixed ι.** This lowers the fraction only as 1/sqrt(N), e.g. 0.16 for N = 5 at
  ι₀ = 0.134. That is still far from QS.
- **What is needed.** A **non-planar magnetic axis** (torsion), or a non-constant on-axis |B|
  for the quasi-isodynamic route. In practice this means giving up the exact circular axis. The
  Dommaschk route of Q-16 should fit a QA target whose axis is the non-planar near-axis axis
  (Landreman–Sengupta / Landreman–Paul style, N = 2 or 3, ι ≈ 0.4). It should not perturb this
  field.

## Claims and evidence

1. **Numerical observation.** ι on the seven surfaces of §3.1. The KAM torus A is at launch radius
   0.130734 with ι = (75 + √5)/562.
2. **Proved informally.** The exact Boozer angles φ_B = φ + εh and θ_B = θ_s + ιεh, with Jacobian
   |B|²/B^φ (§2).
3. **Numerical observation.** The best helicity is QA (1, 0) on every surface. The QA defect is
   about 0.26 of the |B| variation (0.037 B₀₀ at torus A, so defect/ι ≈ 0.27). All other tested
   helicities have defect fraction ≥ 0.96.
4. **Numerical observation.** ε_eff ≈ 0.2 r_eff: 2.7 % at torus A, 4.5 % at r = 0.2, 7.1 % at
   r = 0.287 and 9.9 % at r = 0.36. The ε_eff code is validated on the classical-stellarator limit.
5. **Proved informally.** First-order QA defect fraction = sqrt(ι₀/N), exact for the family (§4).
6. **Lead.** The obstruction extends to first-order omnigeneity (Plunk–Landreman–Helander).

## Difficulty, barriers and readiness

- **Verdict on C2.** The field is **not near omnigenous**.
  - Its ε_eff is that of a classical, unoptimized stellarator (a few % in the core, about 10 % near
    the edge).
  - Its QS defect is O(r) with a fixed fraction, not small relative to ι.
  - The worst-case Boozer-model bound of N-29 is vacuous here (κ > 1 for r ≳ 0.1).
  - Under the contract this candidate satisfies C1 + C4 in vacuum, but fails C2 at any reasonable
    ε_max (e.g. 1 %), except within r_eff ≲ 0.05.
- **Is a certificate worth attempting?**
  - **Positive C2 certificate: no.** No useful bound can be certified, and the quantity (ε_eff) is
    not yet a Lean definition.
  - **Obstruction (§4): yes, a short Lean target.** Its algebraic core is lean-ready: the
    eigenvector, |P|² = Nι₀, |Q|² = N(N − ι₀), and the reduction |B| = 1/R + O(r²). The suggested
    declaration name is `rotatingEllipse_firstOrder_QA_defect`.
  - **Missing for the full statement.** A Lean Boozer chart for this field. §2 makes it elementary:
    φ_B = Φ. Also a link from the chart to N-29's `ξB`.
- **Not done.**
  - Direct guiding-centre Δψ per bounce. ε_eff, with its Ĥ_j bounce integrals, is the standard
    proxy.
  - Electron versus ion distinction. ε_eff is species-independent in the 1/ν regime.
  - Finite β.

## Outputs and next dependencies

- **Q-19.** Answered in the negative, as untrusted numerics plus an informal first-order proof.
  Suggested registry status: "answered (numerics): not omnigenous; ε_eff ≈ 0.2 r_eff;
  obstruction sqrt(ι₀/N)".
- **Q-16 (Dommaschk route).**
  - The exact-circular-axis construction cannot be the base of a QA candidate. The target axis must
    be non-planar.
  - The Boozer machinery of §2 (φ_B = Φ, Jacobian |B|²/B^φ) carries over verbatim to any vacuum
    field B = ∇Φ, and so does the validated Nemov code. Both are ready for a Dommaschk fit.
- **N-29.** The worst-case κ shows that a sharp, oscillation-based bound is needed before any
  nontrivial C2 field can use the bridge.
- **Suggested registry entries** (not edited here): Q-19 status; N-30 row in the research graph;
  this note indexed in `notes/theory/README.md`.
