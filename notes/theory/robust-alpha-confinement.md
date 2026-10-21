# Making the alpha guiding-centre result robust: intervals of ρ, v∥ < 0, μ > 0

Lane-A discovery note, written after progress report 9 (`alpha_gc_confined_forever`). **Nothing here is a compiled
Lean theorem.** Tags: **[Lean]** compiled and sorry-free; **[num]** untrusted double-precision numerics;
**[plan]** proposal.

- Numerics: venv `/tmp/k2venv`, scripts in `/tmp/laneA9`, all importing `scripts/gc_kam/`:
  - `common.py`: grid, strip norm and `maj E`;
  - `scan.py`: ι_A continuation in ρ;
  - `optA.py`: option (a);
  - `cheb.py`, `chebB.py`, `chebres.py`: Chebyshev-in-ρ tori and their residuals;
  - `iscan.py`, `iotaB.py`: ι continuation and the ι_B family;
  - `gcc.py`: KAM constants (a copy of `gc_constants.py` with the torus, ρ and ι taken as arguments);
  - `bmod.py`: |B| on the tori.
- Notation:
  - ρ is the gyroradius parameter `m v∥/(q B₀R₀)`, the argument of `gcField ρ`;
  - `r` is the analyticity strip, with `r_A = 0.1257` and `δ₀ = r_A/7`;
  - `ι_A = (75+√5)/562 = [0;7,3,1̄]`.
- Weighted ℓ¹ norms are taken on `r_A` with weight `e^{r(|k|+|m|)}`, as `Bd`.
- The truncation N = 32, M = 22 used here floors the residual at about 3×10⁻⁹. Decay rates are read off above that
  floor.

## 0. Verdict and ranking

| Rank | Target | Route | Main numbers | Cost |
| --- | --- | --- | --- | --- |
| **1** | **v∥ < 0 at ρ = −1/256** | Same pipeline with a **different rotational transform** ι_B = (161−√5)/1178 = [0;7,2,2,1̄]. This gives a smaller torus, so the node is valid. | `maj E = 0.38`, `e_max = 2.9×10⁻²¹` (the current pipeline reaches 3.7×10⁻²³); γ_B = 0.0674 | ≈ one rerun of the current pipeline: ~35 min of build, ≤ 6 GB, plus a Diophantine proof and a star certificate |
| **2** | **Interval of ρ at fixed ι** (option 1b) | Parametric KAM is **not needed**: apply the existing KAM theorem pointwise in ρ. Use an approximate torus that is a polynomial in ρ, `K(ρ) = Σ_j K_j T_j((ρ−ρ_c)/h)` (Chebyshev). Certify it by ball arithmetic with ρ as a third angle `ρ = ρ_c + h cos ϑ`. | Chebyshev degree d ≈ 8 for the cell `ρ ∈ 1/256·[63/64, 65/64]` (B₀R₀ ∈ [67.9, 70.1] T·m); d ≈ 14 and 16 for `[0, 1/512]` and `[1/512, 1/256]` (all E ≤ 3.5 MeV) | ≈ (2d+1) × 0.6 × the current high-resolution cost per cell: about 5 h of CPU for d = 8 and 9 h for d = 16 |
| 3 | **μ > 0, passing** | Energy-Littlejohn identity: `B*∥ Ẋ = v∥ ∇×(A + ρ_{E,μ}(X) b)`. Then KAM for `B + ∇×(ρ_{E,μ} b)`, a field with a second node. | Passing iff `λ := μB₀/E < 1/max|B| ≈ 0.85` on the torus | Identity: cheap, pure Lean. One (E, μ) instance ≈ 1.5 × the current pipeline. A positive-measure (E, μ) cell ≈ 300 × the current cost. |
| 4 | v∥ < 0 on an interval | ι_B on `[−1/256, −1/512]` (d ≈ 17); `[−1/512, 0]` (d ≈ 19) | see §2 | like rank 2 |
| 5 | Option 1a (frozen K₀) | residual `e₀ + C|ρ−ρ₀|` with C = 1.58 | admissible interval `|ρ − 1/256| ≤ 3.4×10⁻²⁰` (relative 8.6×10⁻¹⁸) | worthless as robustness |

Option 1c (nested tori, complex-ρ KAM) collapses into 1b; see §1.4.

## 1. Robustness in ρ (energy or B₀R₀), μ = 0, v∥ > 0

Physics map. ρ = √(2mE)/(q B₀R₀), and `ρ = 1/256` at E = 3.5 MeV, B₀R₀ = 68.95 T·m. At fixed B₀R₀ ≈ 69 T·m,
`E = 3.5 MeV·(256ρ)²`. So:
- `ρ ∈ [0, 1/256]` is **every** μ = 0 forward alpha with E ≤ 3.5 MeV, including slowing-down alphas;
- the same interval also covers 3.5 MeV alphas at any B₀R₀ ≥ 69 T·m, because only ρ enters.

### 1.1 The structural fact: fixed ι works on an interval [num, theory]

The KAM theorem used (`FlowFieldS.KamH.kam_flow_torus`) is the twist (translated-torus) version for exact
volume-preserving field flows:
- the twist `τ = ⟨T₀⟩` absorbs the average normal correction;
- the flux identity `eta2_flux` removes the counterterm.

So **no frequency parameter or counterterm is needed**. For each field `gcField ρ` that satisfies the hypotheses,
the torus with the same Diophantine ι exists, and the torus moves radially to where ι is attained. The Cantor-set
obstruction arises only for a *fixed* field and varying ι. Here the field varies and ι is fixed, so the family is
analytic in ρ until it degenerates.

Numerically (ι_A family, N = 32, M = 22, `scan.log`):

| ρ | −0.0142 | −1/256 | −1/512 | 0 (torus A) | 1/512 | 1/256 | 0.0078 | ≈ 0.0084 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ‖u‖, ‖z‖ | 0.79, 0.53 | 0.33, 0.29 | 0.28, 0.26 | 0.23, 0.22 | 0.21, 0.19 | 0.19, 0.16 | 0.12, 0.06 | collapses onto the axis |
| `maj E` | 1092 | 1.39 | 0.86 | 0.52 | 0.38 | 0.29 | 0.05 | 0 |

Readings:
- The ι_A torus exists for **ρ ∈ (−0.0145, 0.0084)**. On the right it shrinks onto the GC magnetic axis, where
  `ι_axis(ρ) = ι_A` (a square-root branch point). On the left it breaks up.
- The node is valid (`maj E < 1`) for **ρ ∈ (−0.0026, 0.0084)**. The whole interval `[0, 1/256]` is inside, with
  `maj E ≤ 0.52`.

### 1.2 Option (a): one frozen approximate torus [num] — rank 5

`gcField ρ` is affine in ρ, and so are D̃, ñ in the flow form. So, exactly,
`res(K₀, ρ) = res(K₀, ρ₀) + (ρ−ρ₀)·½W³(κ_D·L(u,z) − (κ_R, κ_Z))`.

At the certified `K₀` (ρ₀ = 1/256):
- `C_R = 0.169`, `C_Z = 1.577` (weighted ℓ¹ on r_A; `optA.py`; affinity checked to 10⁻⁷);
- the KAM smallness allows `e ≤ e_max = δ₀⁴/(32κ) = 5.31×10⁻²⁰` (the margin over `e₀ = 3.7×10⁻²³` is ≈ 1470).

Hence the admissible interval is **|ρ − 1/256| ≤ (5.31×10⁻²⁰ − 3.7×10⁻²³)/1.577 = 3.37×10⁻²⁰**:
- relative 8.6×10⁻¹⁸;
- ΔB₀R₀ ≈ 6×10⁻¹⁶ T·m, ΔE ≈ 6×10⁻¹¹ eV.

The cap is structural: even with `e₀ = 0`, `|Δρ| ≤ e_max/C`, and `e_max ∝ δ₀⁴/κ` is at most about 10⁻¹⁸ even
with a sharp C₂ (§1.5). Covering `[0, 1/256]` with frozen cells would need ~10¹⁷ cells. With first-order cells
`K_c + (ρ−ρ_c)K'_c` the width is about √(e_max/C'') ~ 10⁻¹⁰, so ~10⁸ cells.

Use only as a generic lemma (cheap, §4 M5), not as a result.

### 1.3 Option (b): a Chebyshev-in-ρ approximate torus, certified with ρ as a third angle [num, plan] — rank 2

**Mathematics.** Write `ρ = ρ_c + h cos ϑ` and `K(ϑ) = Σ_{j ≤ d} K_j cos(jϑ)`; the K_j are trigonometric
polynomials in (θ, ψ). The ℓ¹ algebra of functions of (θ, ψ, ϑ), with weight e^{r(|k|+|m|)} in (θ, ψ) and weight 1
in ϑ, has two key properties:
- it is a Banach algebra;
- evaluation at any real ϑ is a contractive ring homomorphism onto the 2-D strip algebra `FA`.

So one ball computation in 3 variables gives `‖res(K(ρ), ρ)‖_{r_A} ≤ e` and all `AdmBounds` **for every ρ in the
cell at once**. The existing KAM theorem is then applied pointwise: `gc_kam_torus` for each ρ, with constants that
are uniform over the cell. The KAM theorem itself is not reproved.

**Chebyshev decay** (weighted norm of `K_j`; `cheb.py`; decay ratio per degree):

| cell | ρ range | E at B₀R₀ = 69 T·m | ratio | Bernstein prediction | `e_max` over the cell (worst end) | degree d for tail ≤ e_max/3 |
| --- | --- | --- | --- | --- | --- | --- |
| single | [0, 1/256] | 0–3.5 MeV | **7** | 6.6 (singularity at 0.0084) | 5.3×10⁻²⁰ | **21** |
| P1 | [0, 1/512] | 0–0.875 MeV | 17 | 15 | 9.4×10⁻²⁰ | **14** |
| P2 | [1/512, 1/256] | 0.875–3.5 MeV | 12.3 | 11 | 5.3×10⁻²⁰ | **16** |
| S (small) | width 2⁻¹³ at 1/256 | [3.29, 3.5] MeV, or B₀R₀ ∈ [69, 71.2] at 3.5 MeV | ≈ 200 | ≈ 150 | 5.3×10⁻²⁰ | **8** |

Notes on the table:
- The residual of the truncated torus is about **0.2–0.3 × the coefficient tail** (`chebres.py`, d = 4, 6), so the
  coefficient tail is a safe proxy.
- The symmetric small cell `ρ ∈ 1/256·[63/64, 65/64]`, i.e. **B₀R₀ ∈ [67.9, 70.1] T·m**, a ±1.6% B₀ tolerance, has
  the same width, so d ≈ 8 as well.

**`e_max` varies along the family** (`gcc.py`; κ ≈ C₂ throughout):

| ρ | `e_max` |
| --- | --- |
| 0 | 4.2×10⁻¹⁸ |
| 1/512 | 9.4×10⁻²⁰ |
| 1/256 | 5.3×10⁻²⁰ |

The certificate for each cell must use the worst constants over the cell, which here are at its largest |ρ|.
Constants at 1/512 are `cK = 3.8×10³`, `cL = 1.65×10⁴`, `τ = 0.42`, `sW = 85`.

**Implementation choice.** The existing pipeline (`KronBall`, `KronBallGrid`) packs ℤ[u][v].

1. *Kronecker in a third variable* (ℤ[u][v][w], with cos ϑ as a symmetric Laurent polynomial in w). Simplest
   mathematically, but each product's integers become `(4d+1)` times longer: about 33× for d = 8. The per-module
   peak of 5.5 GB becomes infeasible.
2. **Evaluation and interpolation (recommended).** Represent each node in the Chebyshev basis. Evaluate at `2d+1`
   rational nodes `x_k ∈ [−1, 1]` (a linear map with rational `T_j(x_k)`). Multiply pointwise with the existing 2-D
   kernel products, interpolate back (exact rational `V⁻¹`), and truncate to degree d, adding the Chebyshev tail to
   the radius.
   - Correctness is polynomial interpolation uniqueness: a degree ≤ 2d polynomial in x with values in `FA` is
     determined by `2d+1` values.
   - Time ≈ `(2d+1)×` the 2-D cost; memory ≈ the 2-D cost per module (split modules by evaluation point).
3. *Monomial (Taylor) basis in t = (ρ−ρ_c)/h* is acceptable only for small cells. The Taylor ratio is the
   singularity distance over h: ≈ 75 for cell S, but 3.3 for the single cell, which would need d ≈ 41.

**Cost estimate (rough).**
- The current high-resolution pipeline is ≈ 16 check modules, 25–30 min in total, ≤ 5.5 GB.
- The target `e ≈ 2×10⁻²⁰` is ≈ 500× weaker than the 3.7×10⁻²³ reached now. This allows a scale of about 2⁻⁷⁵
  instead of 2⁻¹⁰¹ and somewhat smaller N, M; estimate a factor 0.6.

| cell | CPU time | stored data |
| --- | --- | --- |
| S (d = 8, 17 points) | ≈ 5 h | ≈ 4–5× today's ≈ 5 MB (high Chebyshev coefficients need fewer bits, about 3.6 bits less per degree) |
| P1 + P2 (d = 14, 16) | ≈ 17 h | ≈ 8× per cell (~40 MB) |

- The low-resolution admissibility pipeline needs only about 10⁻³ relative accuracy: d_L ≈ 4 (9 points), ≈ 1 h.
- Modules parallelize across evaluation points, at ≤ 6 GB each.

**What else changes for a cell** (all ρ-generic or cheap):
- `gcField_contDiffOn ρ`, `norm_field_ge` and `BstarPar_field` (`B*∥ = |B|` for every ρ) are already
  ρ-generic **[Lean]**.
- The star-shapedness and winding certificate (`gc_radial_ge`, `gc_winding_ge`) must hold for every K(ρ). Run the
  same Kronecker check on the 3-D ball, or certify it at the cell centre with a margin larger than
  `sup_ρ ‖K(ρ) − K(ρ_c)‖`. The cell-S torus moves by ≈ 3×10⁻³ (the first Chebyshev coefficient); the radial margin is 0.035 and the winding margin
  0.0064, so this is fine for S. For P1/P2 the motion is ≈ 0.05: certify with the 3-D ball.
- The torus profile bounds become uniform: `r_in ≤ r_ρ ≤ r_out`. Torus A is larger (R 0.831–1.188), so check
  `r_out ≤ 0.3` (the tube of `norm_field_ge`). This is not measured here: the R and z ranges (R ≤ 1.19, |z| ≤ 0.18) suggest it holds, but it must be certified.

### 1.4 Option (c) and the task's alternatives

- *Different Diophantine ι per cell* is not needed on `ρ ≥ 0`, since ι_A works on all of `(−0.0145, 0.0084)`. It
  *is* the right tool where node validity fails (ρ < −0.0026, §2). That is cell-wise ι, and each cell needs its own
  Diophantine certificate.
- *Two tori bounding an annulus*: trapping between two tori gives no extra robustness, because each torus is still
  per-ρ. It would only matter for confinement away from the axis.
- *KAM with ρ in a complex neighbourhood*: the ϑ-construction of 1.3 is exactly this. The Chebyshev ℓ¹ norm
  dominates the sup over ρ in the cell, and decay is governed by the Bernstein ellipse reaching the branch point
  0.0084.
  - Lifting the KAM theorem itself to the 3-variable algebra would also give *analytic dependence* of the exact
    torus on ρ (nested family). That would mean reproving `KamFlow*S` over a new algebra.
  - Not needed for confinement; not recommended.

### 1.5 Cheap multiplier: a sharper C₂

In all runs κ ≈ C₂, and C₂ is the crude `PolyExprS` second-derivative majorant. It contains
`g³, g⁵ = (1−maj E)^{−3/2, −5/2}` and `maj W³`, and is 10–100× above sharp values. For example:
- C₂ = 7.8×10⁸ at ρ = 0, but 6.1×10¹⁰ at ρ = 1/256;
- C₂ = 3.1×10¹⁴ for ι_A at ρ = −1/512, where `maj E = 0.86`.

Bounding the second derivatives by ball arithmetic (`PolyExprSMajQ` applied to a re-centred tree, or the 3-D ball
itself) would raise `e_max` 10–100×. That saves 1–2 Chebyshev degrees per cell and would make ι_A usable on
`[−1/512, 0]`.

## 2. v∥ < 0 (ρ < 0) — rank 1 (instance), rank 4 (interval)

**Diagnosis [num].** At ρ = −1/256 the ι_A torus is large (‖u‖ = 0.33, ‖z‖ = 0.29, R 0.83–1.28), and
`maj E = Σ|coeff|·‖u‖^i‖z‖^j e^{r(k+l)}` of the 275-term `E = qP² − 1` is 1.39. Along the ι_A family `maj E`
crosses 1 at ρ ≈ −0.0026.

Fixes considered:
1. **Change ι (recommended).** In the GC field at ρ < 0 the transform rises outward from the axis, so a smaller ι
   gives a smaller torus (`iscan.py` at ρ = −1/256: ι = 0.9775·ι_A gives `maj E = 0.27`). Choose the noble
   number `ι_B = [0;7,2,2,1̄] = (161 − √5)/1178 = 0.134774` (`iotaB.py`). Then:

   | quantity | ι_B torus at ρ = −1/256 |
   | --- | --- |
   | ‖u‖, ‖z‖ | 0.217, 0.179 |
   | `maj E` | **0.38** |
   | R range, z range | 0.905–1.187, ±0.141 |
   | `sW`, `tT`, `τ` | 208, 43.2, 0.327 |
   | `cK`, `cL` | 1.35×10⁴, 5.5×10⁴ |
   | C₂ | 1.14×10¹² |
   | **`e_max`** | **2.85×10⁻²¹** |

   The current pipeline achieved 3.7×10⁻²³ at +1/256, a 77× margin with the same N = 40, M = 30.
   - Diophantine constant of `ι_B/2`: **γ_B = 0.06739** (attained at k = 1; checked for k < 2×10⁵), against 0.0687
     for ι_A.
   - The proof is `torusA_rotation_diophantine` verbatim with conjugate `(161+√5)/1178`
     (`diophantine_one_of_conj`).
   - The ι_B family is node-valid for ρ ∈ (−0.0074, 0.0024) and collapses onto the axis at ρ ≈ +0.0025.
2. *Re-centre `R = R_c + u`* (interface change of `xB`, `Ri`). This reduces only the u-part of the majorant; z and
   the helical ripple terms remain (`maj E` is mostly `‖z‖`- and `e^{r}`-driven). Not pursued.
3. *A better P*. Any polynomial `P ≈ q^{−1/2}` works with no interface change: `W = P(1+E)^{−1/2}` with
   `E = qP² − 1` gives `W²q = 1` for every P, and only `RationalStellaratorGCPoly`/`Flow` need regenerating.
   But Newton-improving P does not lower a majorant that is already above 1 (`maj E₁ ≲ ¾m² + ¼m³`). It is useful
   only as a refinement after fix 1.
4. *A smaller strip*: ‖u‖ falls only from 0.331 to 0.314 at r = 0.08, while `δ₀⁴` loses 6×. No.

**Interval** (ι_B, `chebB.py`):

| cell | Chebyshev ratio | `e_max` | degree d |
| --- | --- | --- | --- |
| `[−1/256, −1/512]` | 13 | 2.9×10⁻²¹ | **17** |
| `[−1/512, 0]` | 8 (the ι_B axis collapse at +0.0025 is close) | 3.3×10⁻¹⁹ | **19** (or split) |

ι_A on `[−1/512, 0]` is node-valid but has `maj E = 0.86` and `e_max = 1.0×10⁻²³`; it is usable only after §1.5.
Together with P1 and P2, four cells give **all μ = 0 alphas with 0 < |E| ≤ 3.5 MeV, either direction, at any
B₀R₀ ≥ 69 T·m**. ρ = 0 itself is a particle at rest.

## 3. μ > 0 — rank 3

**Identity (pure Lean, cheap) [plan, proof complete on paper].** Let `B` be C², `B ≠ 0`, and `(X, v)` a
`LittlejohnOrbit m q μ B X v`. Energy conservation (`energy_const`) gives `½ m v² + μ|B(X)| = E`. If `v(t) ≠ 0` for
all t, then by continuity `v = σ·v∥(X)` with `v∥(x) = √(2(E − μ|B(x)|)/m)`, σ = ±1 constant. Put
`ρ_{E,μ}(x) := σ (m/q) v∥(x)`. Then:
- `∇ρ = −σ(μ/(q v∥))∇|B|`;
- the **curl product rule** `∇×(f b) = f ∇×b + ∇f × b` gives
  `v ∇×(ρ b) = v ρ ∇×b + (μ/q) b×∇|B|`;
- hence `B*∥ Ẋ = v B* + (μ/q) b×∇|B| = v·B̃_{E,μ}(X)`, with `B̃_{E,μ} := B + ∇×(ρ_{E,μ} b)`, which is
  divergence-free.

So passing orbits are reparametrized field lines of `B̃_{E,μ}`, with rate `v/B*∥`. That rate has constant sign σ
and modulus at least `√(2(E−μ max|B|)/m)/max|B*∥| > 0` on a compact region. For our curl-free field,
`B*∥ = |B| + ρ b·∇×b = |B|`; this is `BstarPar_field`, whose proof does not use ρ constant. So
`isFieldLine_of_rate_ge` and the trapping layer apply unchanged.

**Parametrization.** `ρ_{E,μ} = ρ_E √(1 − λ|B|)`, with `ρ_E = √(2mE)/(qB₀R₀)` and pitch parameter
`λ = μB₀/E = sin²χ` at |B| = 1.
- On the GC tori, |B| ∈ [0.912, 1.176] at ρ = 1/256 and [0.83, 1.19] for torus A (`bmod.py`). So the passing
  condition on the torus is **λ < 0.85**.
- The isotropic passing fraction at |B| = 1 is `1 − √(1−λ_max)`: 0.61 for λ_max = 0.85 and 0.29 for λ ≤ 1/2.

**Flow form.**
- `P̃ = P − ρ_E S R W(n_R, R n_z, R D)`, with a **second, nested node** `S = (1−λ|B|)·isqrt(1, −λ|B|)` and
  `|B| = qW·R⁻⁴`. `PolyExprS.isqrt c d` allows a node inside d **[Lean]**.
- D̃ and ñ gain `∇S × b` terms. Regenerate `GCFlow` (divFree, flux identities) with the split certificates as
  before.

**Feasibility.**
- *One (E, μ) instance*, for example ρ_E = 1/256 and λ = 1/4: one more node, ≈ 1.5 × the current pipeline. This
  is still a measure-zero set in velocity space, but it is the first μ > 0 orbit class.
- *Positive measure in phase space* needs an open (ρ_E, λ) cell: a 2-variable Chebyshev family.
  - λ enters like a ρ-shift of about ρλ/2 plus a ripple term. The singularities are the branch at λ = 1/max|B| ≈
    0.85 and the axis collapse.
  - For λ ∈ [0, 0.05] at cell S, estimate d_λ ≈ 9 and d_ρ ≈ 8, i.e. `(17)(19) ≈ 320` evaluation points ≈ 300× the
    current cost. For λ ∈ [0, 1/4], d_λ ≈ 15.
  - Research-scale, but it is the only route here to a **positive-measure set of alphas confined forever** in the
    model.

**Trapped particles (v∥ changes sign).** At bounce points `|B| = E/μ`:
- `ρ_{E,μ}` has a square-root branch and `∇ρ` blows up;
- the orbit follows `B̃_{+}` and then `B̃_{−}`, which are different fields;
- near the bounce, the motion is the finite drift `(μ/q) b×∇|B|/B*∥`.

So **no fixed field has trapped orbits as field lines**. What is provable now:
1. `|B(X(t))| ≤ E/μ` for all t (energy). This is not spatial confinement here, since |B| decreases outward on the
   outboard side.
2. Finite-time confinement from a drift-speed bound. In model units, `|Ẋ_⊥| ≤ ρ_E·sup(|∇|B||/|B|)·(...)` gives
   escape times of order `0.1·256` transit times, about 10⁻⁵ s. True but physically empty.
3. The honest route is KAM on the 3-D energy surface of the 2-degree-of-freedom GC Hamiltonian, with
   bounce/precession tori. Its frequencies are disparate (ratio ~ ρ_E), so the KAM constants are very poor.
   Research only; not proposed.

## 4. Recommended Lean modules (in order)

**M1. `Theory/KAM/DiophantineB`**: `iotaB := (161 − √5)/1178`, `iotaB_period_diophantine :
Diophantine (iotaB/2) (673/10000) 1`. Copy `torusA_rotation_diophantine`. Small.

**M2. `Design/RationalStellaratorGCNeg*`** (pipeline rerun: data, environment, checks, relations, `Maj`, `AdmL`,
`Adm`, `Exact`, `Real`, star):
- `gc_exact_torus_neg`: an exact real analytic invariant torus of `gcFlow (−1/256)` with ι = iotaB,
  `10⁻¹²`-close to K_B;
- `rationalStellarator_gc_field_confined_forever_neg`, and
  `alpha_gc_confined_forever_pm`, the current statement with `v 0 = ±√(2·3.5 MeV/m)`, using
  `littlejohn_mu0_isFieldLine_neg` **[Lean, exists]**.

**M3. `Theory/Kinetic/GuidingCentreEnergy`** (no numerics):
- `curl_fderiv_smul (hf : DifferentiableAt ℝ f x) (hb : DifferentiableAt ℝ b x) :
  curl (fderiv ℝ (fun y => f y • b y) x) = f x • curl (fderiv ℝ b x) + cross (gradient f x) (b x)`.
  It follows from `curl_add`, `curl_smul`, `curl_innerSL_smulRight`.
- `modFieldFn (ρ : Space → ℝ) B x := B x + curl (fderiv ℝ (fun y => ρ y • bhat B y) x)`.
- `littlejohn_passing_isFieldLine`: for `h : LittlejohnOrbit m q μ B X v`, with `∀ t, v t ≠ 0`, `σ = sign (v 0)`,
  `E = hamiltonian m μ B (X 0) (v 0)` and C² regularity,
  `∀ t, HasDerivAt X ((v t / BstarPar m q B (v t) (X t)) • modFieldFn (rhoE m q μ E σ B) B (X t)) t`.
- `littlejohn_passing_confined`, the analogue of `littlejohn_mu0_confined`.

**M4. `Certificates/KronBallCheb` + `Design/RationalStellaratorGCFamily*`** (option 1b, cell S first):
- `evCheb : FA₃ →+* FA` with `Bd_evCheb` (contraction);
- the interpolation step `mul_interp`;
- `gc_family_torus : ∀ ρ ∈ Set.Icc (63/16384) (65/16384), ∃ u z, exact torus of gcFlow ρ at ι_A, μ-close to
  K(ρ)`;
- then `alpha_gc_confined_forever_robust`: ∀ B₀R₀ ∈ [67.9, 70.1] T·m, E = 3.5 MeV. Equivalently, every (E, B₀R₀)
  with √E/(B₀R₀) in the cell, with a uniform region `r_in ≤ r_ρ ≤ r_out`.
- Then cells P1 and P2 (all E ≤ 3.5 MeV), and the ι_B cells.

**M5 (optional). `kamH_of_rho_near`**: `KamH` at ρ₀ with slack `s` gives `KamH` at ρ for `C|ρ−ρ₀| ≤ s`, by
affinity in ρ. Generic and cheap, but the interval is 3×10⁻²⁰; use it only to absorb rounding.

**M6 (later).** Generate `gcFlowE ρ_E λ` (second node), a single instance, then the (ρ_E, λ) cell.

**Literature to check before docstrings** *(memory, not verified this session)*:
- parametric KAM and torus continuation with validated numerics: Figueras–Haro–Luque (FoCM 2017), Haro et al.,
  *The parameterization method for invariant manifolds* (2016), ch. 4;
- the guiding-centre energy form `Ẋ ∥ ∇×(A + (m v∥/q) b)`: Littlejohn 1983, Cary–Brizard 2009 §IV.
