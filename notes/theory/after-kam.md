# After the KAM theorem: coil-produced confinement, stepped pressure, guiding centres

Lane-A discovery note (input for Phase 11). Status tags follow `README.md`. **Nothing here is a compiled Lean
theorem.**
- Numerics (untrusted, double precision): numpy/scipy in `/tmp/k2venv`, scripts in `/tmp/laneA8`:
  - `coil.py`: the cubic coil set `filsC`, parsed from `PolygonCoilCubicData.lean` (192 segments);
  - `torus.py`: torus A (`/tmp/k2work/torusA_P90_N32_M22.npz`);
  - `resid.py`: flow-form residuals and weighted ℓ¹ norms;
  - `gcf.py`, `gcscan.py`: the guiding-centre field B̃ and its ι scans;
  - `coilscan.py`: the coil-field ι_A torus.
- No web search was run this session. Literature locators marked *(memory)* need checking before they go into
  docstrings.

Starting point (Phase 10 plus addendum): `rationalStellarator_confined_forever_exists`. The field
`field (1/4) = ∇φ + ¼∇h` has an exact analytic invariant torus with ι = (75+√5)/562, within 10⁻¹⁰ of torus A
(0.077 ≤ ρ ≤ 0.19). Every field line starting inside it exists for all time and stays inside. The KAM constants
(`KamTorusAExact`) are:
- γ = 0.0687, r_A = 0.1257, δ₀ = r_A/7 = 0.01796;
- e₀ = 5.83×10⁻²², κ ≈ 5.7×10⁹;
- smallness 32κe₀/δ₀⁴ ≈ 1.0–1.1×10⁻³;
- displacement budget μ = 10⁻¹⁰.

## 0. Verdict and ranking

| Rank | Target | Route | Cost (agent-weeks) | Physics value |
| --- | --- | --- | --- | --- |
| **1** | **3. Guiding centres** | passing guiding-centre orbits are field lines of B̃ = B + ρ_s∇×b; rerun KAM for B̃ | **3–4** | first all-time *particle* (GC-model) confinement in a non-axisymmetric field |
| **2** | **1. Coil field** | option (a): rerun KAM for the coil field with a *refitted* torus, using analytic (non-polynomial) composition | **5–7** | the exact model field is replaced by an explicit coil set |
| 3 | 2. Stepped pressure | ELP-S: Hamilton–Jacobi on the torus + Cauchy–Kovalevskaya + gluing | ≥ 8 for existence; stability is open and probably negative | first exact finite-β 3-D equilibrium on our field |

Key findings, each detailed below:

1. **Option 1(b), robustness, is ruled out by about 14 orders of magnitude (numerical observation, §2.1).**
   - The verified KAM theorem tolerates initial error e ≤ δ₀⁴/(32κ) ≈ **5.7×10⁻¹⁹** (weighted ℓ¹ on r = 0.1257).
   - The cubic coil set gives torus A a residual of **8.4×10⁻⁵** in that norm, so C = e/η ≈ 6.5. The required field
     error is therefore **η ≲ 9×10⁻²⁰** (analytic sup on the complexified torus).
   - The best certified coil error is 4.9×10⁻⁶ (frontier of the a = 0.104 tube). On torus A itself the sampled
     error is 1.3×10⁻⁵. The TF closure alone contributes 2.5×10⁻⁶.
   - Even an idealized KAM with κ = 1 would need η ≲ 5×10⁻¹⁰.
   - **Conclusion:** the torus must be *refitted* to the coil field, and that requires the KAM theorem for a
     non-polynomial field (option (a)).
2. **The coil field has a regular ι_A torus about 5×10⁻⁵ from torus A (numerical observation).**
   - Coil field = ideal ∇φ + `filsC`. The ι_A torus launches at r* = 0.18824 on φ = π/4 (model: 0.18819). Its
     weighted-Birkhoff ι agrees to 1.3×10⁻¹¹ between 300 and 600 periods.
   - The coil-field composition along torus A is analytic on the (θ, ψ)-strip (0.8, 0.5). The singularity is
     near (1.0, 0.6).
   - Fourier decay is e^{−1.3k} in θ and e^{−0.8m} in ψ. A refitted torus therefore needs about N = 40, M = 64
     (≈ 10⁴ coefficients; torus A had 2925).
3. **Passing guiding-centre orbits are field lines of a divergence-free field (proved informally, classical).**
   - With v_∥(X) = σ√(2(E − μ|B|)/m) and B̃ := ∇×(A + (m v_∥(X)/q) b), the Littlejohn GC velocity satisfies
     B*_∥ Ẋ = v_∥ B̃ (§1.1).
   - For μ = 0, B̃ = B + ρ_s∇×b exactly, with ρ_s = σ m v/(qB₀R₀) in model units.
   - So the Phase-10 pipeline applies after adding **one algebraic variable** w = |B|⁻¹. The residual stays
     exactly certifiable by Kronecker arithmetic.
4. **GC tori with ι = ι_A exist for |ρ_s| ≤ 5.4×10⁻³, both signs (numerical observation).**
   - Weighted-Birkhoff ι agrees to ≤ 4×10⁻¹² between 500 and 1000 periods.
   - For 3.5 MeV alphas, ρ_s = 0.2695 T·m/(B₀R₀), so the condition is **B₀R₀ ≥ 50 T·m**:
     - HELIAS 5-B (121 T·m): ρ_s = 2.2×10⁻³;
     - Stellaris (114 T·m): ρ_s = 2.4×10⁻³;
     - ARIES-CS (44 T·m): ρ_s = 6.1×10⁻³, just outside the scan, so another Diophantine ι is needed.
   - At |ρ_s| = 10⁻² the ι profile no longer crosses ι_A for r ≤ 0.28, so another ι is needed there too.
5. **The time-bound route for particles is useless (§1.6).**
   - The drift bound ρ_L s t/L_B reaches the 0.077 R₀ barrier distance in ~10⁻⁶ s at R₀ = 10 m, against a
     slowing-down time of 0.1–1 s.
   - An invariant torus alone gives only an *exponential* Grönwall bound for drifting orbits.
6. **Stepped pressure: existence is KAM-class work; stability is probably negative (§3.4).**
   - Mercier and ballooning do not apply (p′ = 0 a.e.). The relevant criterion is the ideal-interface energy
     principle, with surface term ½∮|ξ_n|²[[n·∇(B²/2)]].
   - For vacuum fields on both sides, n·∇(B²/2) = B²κ_n. On torus A, κ_n ∈ [−0.97, 1.26] and is negative (bad) on
     **48 %** of the surface.
   - The leading O(Δp) surface term 2Δp κ_n is therefore sign-indefinite, and the pointwise sufficient criterion
     fails. This is consistent with the toroidal min-B obstruction (`toroidal-min-b-obstruction.md`).
   - A stability margin would have to come from the field-direction jump across the sheet, which is O(Δp). An
     interface-interchange instability witness is the more likely formal outcome.

**Recommended order.**
- Phase 11a: an abstract `FlowField` interface for the KAM step (serves 3 and 1).
- Phase 11b: the guiding-centre KAM (target 3).
- Phase 11c: analytic composition and the coil KAM (target 1).
- Target 2 only after 11c, and only if a stability statement is wanted or an instability witness is acceptable.

---

## 1. Target 3 (rank 1): all-time guiding-centre confinement in the exact field

### 1.1 Reduction: passing guiding-centre orbits are field lines of B̃ (proved informally)

The model is the Littlejohn guiding centre in a static field, E = 0 (Cary–Brizard, RMP 81 (2009) 693 *(memory)*):
- B* = B + (m v_∥/q)∇×b and B*_∥ = b·B*;
- Ẋ = (v_∥B* + (μ/q) b×∇|B|)/B*_∥;
- m v̇_∥ = −μ B*·∇|B|/B*_∥.

Energy E = m v_∥²/2 + μ|B| and μ are conserved.

**Lemma GC-1.** On an orbit with v_∥ ≠ 0, put v_∥(X) = σ√(2(E − μ|B(X)|)/m) and
B̃ := B + (m/q)∇×(v_∥(X) b). Then B*_∥ Ẋ = v_∥ B̃(X), and ∇·B̃ = 0.

*Proof.* ∇×(v_∥b) = v_∥∇×b + ∇v_∥×b, and ∇v_∥ = −μ∇|B|/(m v_∥). Hence
(m/q)∇v_∥×b = (μ/(q v_∥)) b×∇|B|, and multiplying by v_∥ gives the claim. Divergence-free because B̃ is
B plus a curl. ∎

So each passing guiding centre (fixed E, μ, σ) moves along a field line of B̃, reparametrized by v_∥/B*_∥ ≠ 0.
**An invariant torus of B̃ is an all-time barrier for those guiding centres.** The torus-trapping and
ODE-global theorems apply to the vector field V = (v_∥/B*_∥)B̃, which is C¹ and nonvanishing where
E > μ|B| and B*_∥ > 0.

- For **μ = 0**, B̃ = B + (σ m v/q)∇×b. In model units (B₀ = R₀ = 1), **B̃ = B + ρ_s∇×b with ρ_s = σρ_L(B₀)/R₀**.
- For a vacuum B, ∇×b = ∇(1/|B|)×B = (w³/2)·B×∇Q, where Q = |B|² and w = Q^{−1/2}.
- So **B̃ is polynomial in (R, z, cos2φ, sin2φ, w) after clearing R**, with the single algebraic relation
  w²Q = 1.

Novelty: none. Drift surfaces as flux surfaces of B + ∇×(ρ_∥B) are standard (White, *Theory of toroidally confined
plasmas*; Boozer; Cary–Littlejohn *(memory)*). What is new for the library is the route: the verified field-line KAM
gives a verified GC KAM.

### 1.2 Numbers (numerical observation, `gcscan.py`)

ι(r) is scanned on φ = π/4 from the GC magnetic axis (period-map Newton). Columns: ρ_s; GC axis R; launch radius
r* of the ι_A torus; minor-radius range of that torus; |ι(1000) − ι(500)| (weighted Birkhoff).

| ρ_s | axis R | r* | ρ range | Birkhoff diff |
| --- | --- | --- | --- | --- |
| 0 | 1.00000 | 0.18819 | 0.102–0.188 | 1.2e-12 |
| +2.7e-3 | 0.97362 | 0.15028 | 0.083–0.150 | 2.5e-12 |
| −2.7e-3 | 1.02763 | 0.22300 | 0.117–0.223 | 3.2e-12 |
| +5.4e-3 | 0.94845 | 0.10381 | 0.059–0.104 | 2.3e-12 |
| −5.4e-3 | 1.05657 | 0.25804 | 0.132–0.258 | 3.8e-12 |
| ±1e-2, ±2e-2 | — | no ι_A crossing for r ≤ 0.28 | — | — |

- The axis shift is ≈ −9.7ρ_s, the familiar passing-orbit shift ~ρ_L/ι.
- Alpha: E = 3.5 MeV, v = 1.299×10⁷ m/s, ρ_L(5 T) = 5.39 cm. So ρ_s = 0.2695 T·m/(B₀R₀).
- With ι_A fixed, |ρ_s| ≤ 5.4×10⁻³ means B₀R₀ ≥ 50 T·m. Beyond that, choose another Diophantine ι in the
  shifted profile, e.g. ι ∈ (0.139, 0.150) for ρ_s = +10⁻².
- **Recommended first instance: ρ₀ = 1/256 (3.9×10⁻³), both signs σ = ±1.** That is B₀R₀ = 69 T·m, e.g.
  R₀ = 12.5 m at 5.5 T. ι_A is reused, so the Diophantine certificate is unchanged.

### 1.3 Statements (proposed)

```lean
namespace PlasmaLean.Kinetic.GCLittlejohn          -- Theory/Kinetic/GuidingCentreLittlejohn.lean
def bhat (B : Space → Space) (x : Space) : Space := ‖B x‖⁻¹ • B x
def Bstar (m q : ℝ) (B) (x : Space) (v : ℝ) : Space := B x + (m * v / q) • curl (bhat B) x
def BstarPar (m q B x v) : ℝ := ⟪bhat B x, Bstar m q B x v⟫
structure IsGCOrbit (m q μ : ℝ) (B : Space → Space) (X : ℝ → Space) (v : ℝ → ℝ) : Prop where
  hX : ∀ t, HasDerivAt X ((BstarPar m q B (X t) (v t))⁻¹ •
          (v t • Bstar m q B (X t) (v t) + (μ / q) • cross (bhat B (X t)) (gradient (‖B ·‖) (X t)))) t
  hv : ∀ t, HasDerivAt v (-(μ / m) * (BstarPar m q B (X t) (v t))⁻¹ *
          ⟪Bstar m q B (X t) (v t), gradient (‖B ·‖) (X t)⟫) t
theorem energy_const (h : IsGCOrbit m q μ B X v) : ∀ t, m * v t ^ 2 / 2 + μ * ‖B (X t)‖ = m * v 0 ^ 2 / 2 + μ * ‖B (X 0)‖
def modField (m q μ E σ : ℝ) (B) (x : Space) : Space :=
  B x + (m / q) • curl (fun y => (σ * Real.sqrt (2 * (E - μ * ‖B y‖) / m)) • bhat B y) x
theorem velocity_eq_modField (h : IsGCOrbit m q μ B X v) (hE : energy = E) (hv : v t ≠ 0) (hσ : sign) :
    deriv X t = (v t / BstarPar m q B (X t) (v t)) • modField m q μ E σ B (X t)
theorem modField_divFree : divergence (modField m q μ E σ B) x = 0          -- B̃ = B + curl
```

```lean
namespace PlasmaLean.Design.RationalStellaratorGC     -- Design/RationalStellaratorGC*.lean
def gcField (ρ : ℝ) (x : Space) : Space := field (1/4) x + ρ • curl (bhat (field (1/4))) x
theorem gcField_eq (hx : x ∈ domain) :                    -- the algebraic form used by the KAM residual
    gcField ρ x = field (1/4) x + (ρ / 2 * Q x ^ (-(3:ℝ)/2)) • cross (field (1/4) x) (gradient Q x)
theorem gc_exact_torus (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :   -- ρ₀ = σ/256
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ resR_gc (σ/256) iota u z = 0 ∧
      resZ_gc (σ/256) iota u z = 0 ∧ Close ρ∞ iota u z u_gc z_gc μ
theorem rationalStellarator_gc_confined_forever (hσ) : ∃ (c : ℝ × ℝ) (prof : ℝ → ℝ → ℝ), bounds ∧
    ∀ X₀ ∈ gcRegion c prof, ∃! X : ℝ → Space, IsFieldLine (gcField (σ/256)) X ∧ X 0 = X₀ ∧ ∀ t, X t ∈ gcRegion c prof
theorem alpha_gc_confined_forever (R₀ B₀) (hscale : 0.2695 / (B₀ * R₀) = 1/256) :   -- SI instance, μ = 0
    ∀ (X v), IsGCOrbit mα qα 0 (Bphys R₀ B₀) X v → X 0 ∈ region → ∀ t, X t ∈ region
```

### 1.4 What must be built (dependency order, with costs)

1. **`FlowField` interface (shared with target 1, §2.4 step 1): 1–1.5 weeks.**
   - Refactor `KamNewtonField/Frame/Step` and `KamIteration` so that `kam_step`/`kam_flow_torus` take an abstract
     field record. The record holds:
     - `D, n_R, n_Z : FA → FA → FA` with `eval` compatibility;
     - first-derivative maps and majorant bounds (the role of `bD, bDu, bnR, …`);
     - the Taylor constant (`C2`);
     - the identities `divFree`, `flux_a/b/c` and `torsion_poly` as hypotheses.
   - Show the polynomial `field (1/4)` is an instance. Regression check: `torusA_exact` still builds.
2. **`PolyExpr` plus one inverse-square-root node: 4–6 days.**
   - In ℓ¹_ρ(ℤ²), for ‖x − c‖ < c with c > 0, define y = c^{−1/2} Σ binom(−½, n)((x − c)/c)ⁿ. Prove y²x = 1,
     `eval y = (eval x)^{−1/2}` (positive branch, real points) and d y = −½ y³ dx.
   - Majorants: maj(invSqrt e) = (c − maj(e − c))^{−1/2}, together with `majD`/`majD2`.
   - Pattern: the Neumann inverses already in `StripAlgebra`.
3. **Littlejohn GC module (§1.3): 3–4 days.** Lemma GC-1 is an algebraic identity plus the chain rule.
4. **The B̃ polynomial forms: 3 days.**
   - Write `D̃ = R³B̃^φ`, `ñ_R`, `ñ_Z` in (u, z, c, s, w).
   - Prove the identities `divFree` and flux (the primitive comes from Ã = A + ρ_s b) with `linear_combination`
     modulo w²Q = 1.
5. **Oracle and certificate: 1 week.**
   - Galerkin–Newton for the GC torus. Continue in ρ_s from torus A: the torus moves by about 0.05 at
     ρ_s = 3.9×10⁻³, so take 4–8 continuation steps.
   - Certify w₀ ≈ (Q∘K₀)^{−1/2} with a radii-polynomial: ‖w₀²·Q∘K₀ − 1‖ is computed exactly (Kronecker), so
     ‖w − w₀‖ ≲ 10⁻²³.
   - Certify the residual exactly with the extended Kronecker forms, then the frame/twist surrogates as in
     `KamTorusASurrogate*`.
   - Expect constants like torus A's (similar shear and twist; dι/dr ≈ 0.03 at the GC tori).
6. **Trapping transfer and SI instance: 3 days.** Reuse `RationalStellaratorForever*`, `ODEGlobal` and the
   reparametrization by v_∥/B*_∥.

### 1.5 Scope and honesty

- This is the **guiding-centre model**, not full Lorentz orbits. A full-orbit all-time result is not available:
  3 DOF means 3-tori are not barriers in the 5-D energy shell. Nekhoroshev/adiabatic-invariance gives times
  ~exp(c/ρ*) (Benettin–Sempio *(memory)*), which is out of scope.
- The first rung is **μ = 0 (exactly parallel) particles at one energy**, a measure-zero class.
- μ > 0 passing particles at fixed (E, μ) only add the second algebraic variable v_∥(X).
- A theorem for *all* (E, λ = μB₀/E) in a box needs a **parametrized a posteriori KAM**:
  - K₀(·; λ, ρ_s) piecewise polynomial in the parameters;
  - the residual certified as a 3- or 4-variable Kronecker polynomial, with constants uniform in the parameters;
  - the KAM applied pointwise.
  - Cost: +2–3 weeks.
- **Trapped particles are not covered.** v_∥ = 0 is a branch point of B̃. In this non-omnigenous field they are
  expected to be lost promptly; the second-adiabatic-invariant (bounce-averaged) theory is separate.
- Collisions and slowing-down are not modelled. "All time" means collisionless.

### 1.6 Why not the time bound (negative)

- `GuidingCentre.guidingCentre_reduction_bound` gives |X − X₀ − ∫v_∥b| ≤ ρ_L(G/B_min)s t. For a 3.5 MeV alpha at
  5 T with L_B = 1 m that is 7×10⁵ m/s.
- Distance to the torus is ≥ 0.077 R₀ (0.77 m at R₀ = 10 m), which gives ≲ 1.1×10⁻⁶ s, under one toroidal transit
  (4.8×10⁻⁶ s).
- Turning this into a barrier statement also needs a *first integral*. The torus alone gives only
  |G(t)| ≤ (|G₀| + |∇G|u_d t)e^{L s t}.
- So it is cheap but physically empty. Do not pursue it except as a sanity corollary.

---

## 2. Target 1 (rank 2): coil-produced all-time confinement

Setting: the coil field is B_c = `tfField` + `polyCoilFieldC` (8 polygonal filaments, 192 segments; TF rectangle
closed at Λ = 10⁶).
- Coils lie at minor radius ≥ 0.46 about R = 1. They are ≥ 0.297 from torus A (sampled).
- Certified: ‖polyCoilFieldC − hel‖ ≤ 4.874×10⁻⁶ on the frontier of the a = 0.104 tube (46-transit theorem),
  and ζ = 2.5×10⁻⁶ for TF.
- Torus A reaches ρ = 0.19, outside that tube. There the sampled coil error is up to **1.3×10⁻⁵**.

### 2.1 Option (b), robustness: quantified and rejected

- If B_c is used with the *unchanged* approximate torus A, the initial error becomes e = e₀ + ‖D₀(X₀ − X_c)∘K₀‖_r.
- The verified theorem needs 32κe/δ₀⁴ ≤ 1, i.e. e ≤ δ₀⁴/(32κ) = 1.04×10⁻⁷/(1.82×10¹¹) ≈ **5.7×10⁻¹⁹**. The
  displacement budget 2c_K e/δ₀² ≤ 10⁻¹⁰ gives 1.5×10⁻¹⁸, which is weaker.

| quantity | value |
| --- | --- |
| ℓ¹_{0.1257} residual of torus A in B_c (`resid.py`, 128×192 grid) | 8.4×10⁻⁵ (R and z components; 3.0×10⁻⁵ at r = 0) |
| sup of real \|B_c − hel\| on torus A | 1.3×10⁻⁵, so C = e/η ≈ 6.5 |
| **required η** (sup on the complexified torus) | **≲ 9×10⁻²⁰** |
| required η if κ were 1 (any scheme of this structure) | ≲ 5×10⁻¹⁰ |
| best coil errors (certified / continuum current potential) | 4.9×10⁻⁶ / 2.3×10⁻⁶ |

**Certifying an analytic-neighbourhood error, if ever needed (proved informally).**
- Suppose u is harmonic near the closed real ball B̄(x₀, R) with |u| ≤ η there. Each Cartesian component of
  B_c − B₀ qualifies.
- Complexifying the Poisson integral gives, for |y| < R,

  |u(x₀ + iy)| ≤ η · R(R² + |y|²)/(R² − |y|²)^{3/2},

  because |(iy − ζ)·(iy − ζ)| ≥ R² − |y|² on |ζ| = R. The factor is 1.93 at |y| = R/2.
- On the strip r = 0.1257, the complexified torus A has |Im x| ≤ 0.073 (`resid.py`). So real balls of radius
  0.146 suffice, and they avoid the coils (≥ 0.297).
- Real bounds therefore transfer to the complex neighbourhood at a factor of about 2, via the existing
  maximum-principle covers enlarged to the 0.146-neighbourhood of torus A.
- This does not rescue (b): the gap is 10¹³–10¹⁴.

**Why no coil set can close (b).** Any finite coil set misses ∇φ + ¼∇h by more than 10⁻⁶–10⁻⁸. The TF closure is
O(1/Λ), and helical fits stagnate near 10⁻⁶. The KAM tolerance at this strip and γ is far below that. Widening
the strip (δ₀⁴ grows) gains about 10², not 10¹³.

### 2.2 Option (a): KAM for the coil field with a refitted torus (recommended)

**Feasibility evidence (numerical observation):**
- B_c (with ideal ∇φ) has a regular ι_A torus: r* = 0.18824 against 0.18819, axis shift 1.2×10⁻⁷, Birkhoff diff
  1.3×10⁻¹¹. So the same ι and the same Diophantine certificate can be reused, and the frame and twist constants
  will be essentially those of torus A.
- The composition (θ, ψ) ↦ residual of torus A in B_c is analytic on the strip (0.8, 0.5):

  | (θ, ψ) strip | sup \|residual of torus A in B_c\| |
  | --- | --- |
  | (0.1257, 0.1257) | 1.75×10⁻⁵ |
  | (0.3, 0.3) | 4.5×10⁻⁵ |
  | (0.5, 0.4) | 1.7×10⁻⁴ |
  | (0.8, 0.5) | 3.5×10⁻³ |
  | (1.0, 0.6) | blows up: Re(a·a) → 0 at a coil |

- Fourier decay of the coil part is e^{−1.3k} in θ and e^{−0.8m} in ψ.
- For ℓ¹_{0.1257} residual ≈ 10⁻²¹ the refitted torus needs **N ≈ 40, M ≈ 64**: about 10⁴ coefficients at
  ~100-bit dyadic precision. The oracle needs double-double or mpmath Newton.

**Residual certificate (the main cost).** B_c is not polynomial: there are 2 square roots per segment, i.e. 196
vertex distances. So there is no exact Kronecker residual. Use sampling plus aliasing:
- Evaluate E = D·𝓛K₀ − n at real grid points with dyadic interval arithmetic. Use the closed-form `segClosed` and
  the `Bseg` checker machinery with square-root brackets at 2⁻¹⁰⁰.
- Bound sup|E| ≤ M″ ≈ 10 on the complex strip r″ = (0.8, 0.5) with the complex Biot–Savart majorant (§2.3).
- Then ‖E‖_r ≤ Σ_grid |Ê^{disc}| e^{r(|k|+|m|)} + (alias + tail), with alias + tail ≲ 2M″Σ e^{−(r″−r)N/2}.
- For alias + tail ≤ 10⁻²³ take N_ψ ≈ 300 and N_θ ≈ 170, i.e. 5×10⁴ points, 2.5×10⁴ after σ-symmetry. That is
  **≈ 5×10⁶ exact segment evaluations**. This is of the order of the existing frontier certificates (an estimate;
  calibrate with a pilot on one grid line).

**Smallness.**
- Do not count on κ improving: κ ≈ 5.7×10⁹ is dominated by c_K·c_L ≈ 1.4×10⁹ (twist and torsion), not by
  polynomial majorant slack.
- So the coil run needs e₀ ≲ 5×10⁻¹⁹ again. Target e₀ ≈ 10⁻²¹ for a margin of about 500.

### 2.3 Statements (proposed)

```lean
namespace PlasmaLean.Theory.KAM.StripPaleyWiener          -- holomorphic on a strip ⇒ ℓ¹ bounds
theorem coeff_le_of_holo {f : ℂ → ℂ} (hper : ∀ w, f (w + 2 * π) = f w)
    (hd : DifferentiableOn ℂ f {w | |w.im| < ρ'}) (hb : ∀ w, |w.im| < ρ' → ‖f w‖ ≤ M) (hρ : ρ'' < ρ') :
    ∀ k : ℤ, ‖fourierCoeffC f k‖ ≤ M * Real.exp (-ρ'' * |k|)     -- contour shift; Mathlib rectangle Cauchy
theorem wnorm_le_of_holo₂ … : wnorm ρ (coeff₂ f) ≤ M * (Real.coth ((ρ'' - ρ) / 2)) ^ 2
theorem dft_alias (N₁ N₂ : ℕ) : dft₂ f N₁ N₂ km = ∑' j : ℤ × ℤ, coeff₂ f (km + (j.1 * N₁, j.2 * N₂))
theorem wnorm_le_of_samples … : wnorm ρ (coeff₂ f) ≤ ∑ km ∈ box, ‖dft₂ f N₁ N₂ km‖ * weight ρ km + aliasTail M ρ'' ρ N₁ N₂

namespace PlasmaLean.Fields.BiotSavartComplex
def segFieldC (κ : ℝ) (p q : Space) (y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  κ • ∫ t in (0:ℝ)..1, (dotC (w p q y t) (w p q y t)) ^ (-(3:ℂ)/2) • crossC (q - p) (w p q y t)
theorem segFieldC_ofReal : segFieldC κ p q (ofRealV y) = ofRealV (segClosed κ p q y)   -- off the segment
theorem segFieldC_bound (hη : ‖imV y‖ < d) (hd : ∀ t ∈ Icc 0 1, d ≤ ‖reV y - seg p q t‖) :
    ‖segFieldC κ p q y‖ ≤ |κ| * ‖q - p‖ * √(Dmax ^ 2 + ‖imV y‖ ^ 2) / (d ^ 2 - ‖imV y‖ ^ 2) ^ (3/2 : ℝ)
theorem segFieldC_analyticOn : AnalyticOnNhd ℂ (segFieldC κ p q) {y | ‖imV y‖ < infDist (reV y) (segment p q)}

namespace PlasmaLean.Theory.KAM.AnalyticComposition       -- X(K₀ + h) = Σ c_α h^α in FA
structure AnaFieldAt (ρ d C : ℝ) (K₀ : FA × FA) where
  c : ℕ × ℕ → FA                       -- c_α = Fourier coefficients of ∂^αX(K₀(θ,ψ),ψ)/α!
  bound : ∀ α, wnorm ρ (c α) ≤ C / d ^ (α.1 + α.2)
  eval_eq : ∀ θ ψ α, eval (c α) θ ψ = iteratedPartial X α (K₀ θ ψ) / α!
def comp (F : AnaFieldAt ρ d C K₀) (h : FA × FA) : FA := ∑' α, F.c α * h.1 ^ α.1 * h.2 ^ α.2
theorem comp_eval (hh : ‖h‖ρ < d) : eval (comp F h) θ ψ = X (K₀ θ ψ + eval h θ ψ, ψ)
theorem comp_taylor (hh : ‖h‖ρ + ‖k‖ρ ≤ d/2) :
    ‖comp F (h + k) - comp F h - dcomp F h k‖ρ ≤ (8 * C / d ^ 2) * ‖k‖ρ ^ 2

namespace PlasmaLean.Design.PolygonCoilKam
theorem coilTorus_exact : ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ resCoil iota u z = 0 ∧
    Close ρ∞ iota u z u_c z_c (1/10^10)
theorem coilStellarator_confined_forever : ∃ prof, (0.07 ≤ prof ∧ prof ≤ 0.2) ∧ ∀ x₀ ∈ region prof,
    ∃! γ : ℝ → Space, IsFieldLine (fun x => tfField x + polyCoilFieldC x) γ ∧ γ 0 = x₀ ∧ ∀ s, γ s ∈ region prof
```

### 2.4 Build order and cost

1. **`FlowField` interface**: §1.4 step 1, shared.
2. **`StripPaleyWiener`: 1 week.**
   - 1-D contour shift for periodic holomorphic functions, using Mathlib's
     `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`; the vertical sides cancel by periodicity.
   - Then the 2-D version by iteration, and the sampling/aliasing identity.
3. **`AnalyticComposition`: 1–1.5 weeks.**
   - Power series in the Banach algebra ℓ¹_ρ (geometric majorants, as `PolyExpr.maj` but infinite).
   - The identities `divFree` and flux hold at real points: div B_c = 0, and the closed-form segment vector
     potential A = κ v̂ ln((|b| + b·v̂)/(|a| + a·v̂)) gives the primitive. They transport by `ext_eval`.
4. **`BiotSavartComplex`: 1 week.** This covers holomorphy of a parametric integral, the majorant, and the
   Cauchy estimate in space for the c_α bounds.
5. **Oracle and certificates: 1.5–2 weeks.**
   - High-precision refit.
   - The sampling residual certificate (≈ 5×10⁶ segment evaluations; pilot first).
   - Frame/twist surrogates.
   - A certified coil distance ≥ 0.25 on a 0.15-neighbourhood of the torus.
6. **Trapping transfer: 3–4 days**, via `ODEGlobal` (C¹ off the coil).

Total: **5–7 agent-weeks**, of which 2–2.5 weeks are shared with target 3.

**Cheaper variants considered and rejected:**
- A polynomial (harmonic) approximation of B_c about the axis. The complex polydisc reaching ρ ≈ 0.25 hits the
  coils, and convergence ~(0.625)ⁿ needs degree ~100.
- Treating the Taylor remainder as an error term. This breaks exact convergence: KAM needs the exact field.
- Straight infinite wires (rational fields). Exactness is lost at the return legs.

---

## 3. Target 2 (rank 3): stepped pressure across the exact torus

### 3.1 What must be proved (ELP-S, JEMS 27 (2025) 2251; Bruno–Laurence, CPAM 49 (1996) 717)

Let S = the exact torus of Phase 10, Ω₁ its solid interior, B₁ = `field (1/4)`, p₁ = Δp, p₂ = 0. Find:

1. **Outer field.** A collar U ⊃ S and B₂ = ∇Φ₂ on U \ Ω₁ (vacuum), tangent to S.
2. **Jump.** |B₂|² = |B₁|² + 2Δp on S (total pressure continuous; μ₀ = 1, outer field stronger).
3. **Hamilton–Jacobi on S.**
   - In torus coordinates, write Φ₂|_S = f = aθ + bφ + ζ(θ, φ), with ζ periodic. Then (1)–(2) become
     |∇_S f|²_g = |B₁|²_S + 2Δp, and ∂_nΦ₂ = 0.
   - Linearizing at Δp = 0 (where f₀ = Φ|_S) gives B₁·∇_S ζ = Δp, i.e. λ𝓛ζ = Δp with
     𝓛 = ∂_φ + ι∂_θ and λ = B^φ-weight.
   - It is solvable iff aι + b = ⟨Δp/λ⟩. The periodic part comes from the existing Diophantine solver
     (`cohSol_estimate_one`, γ = 0.0687).
   - The nonlinear problem needs a Newton scheme in which the transport field V = ∇_S f changes at every step. Its
     rotation number must stay Diophantine (fixed by (a, b)): a Kolmogorov/Herman conjugacy on T² (ELP-S Thm 5.1).
     This is **a second KAM-class theorem**, without twist but with conjugacy.
4. **Collar (Cauchy–Kovalevskaya).** Φ₂ is harmonic near S with analytic Cauchy data (f, 0). In normal coordinates
   the Laplacian has analytic coefficients from K_∞.
   - Take a majorant series Φ₂ = Σ nʲΦ_j with nested ℓ¹ strips (Ovsyannikov).
   - The collar thickness is ~ρ_∞·|∂K| ~ 10⁻³ R₀. It is thin but explicit.
5. **Gluing (ELP-S Lemma 2.1).** (B, p) is a weak MHS equilibrium on Ω₁ ∪ U.
   - Pointwise form: each side satisfies curl B = 0 and p = const; there is tangency; total pressure is continuous.
   - The weak form needs a divergence theorem on a curved domain, which Mathlib lacks. State the interface form.

**Pressure size.** With small-parameter perturbation theory at fixed strip, the Newton smallness would allow only
β_step = 2Δp/B² ≈ γ²δ⁴/C, i.e. 10⁻¹²–10⁻¹⁵. That is negligible. To reach β ~ 1 % one needs an *a posteriori* run:
- solve HJ + CK numerically at β = 1 %;
- certify the residual;
- Newton-validate.

As for torus A, the smallness then constrains the residual, not Δp.

### 3.2 Statements (proposed)

```lean
structure SteppedEquilibrium (Ω₁ U : Set Space) (B₁ B₂ : Space → Space) (Δp : ℝ) : Prop where
  inner_vac : VacuumField (interior Ω₁) B₁
  outer_vac : VacuumField (U \ closure Ω₁) B₂
  tangent₁ : ∀ x ∈ frontier Ω₁, ⟪B₁ x, normalS x⟫ = 0
  tangent₂ : ∀ x ∈ frontier Ω₁, ⟪B₂ x, normalS x⟫ = 0
  jump : ∀ x ∈ frontier Ω₁, Δp + ‖B₁ x‖ ^ 2 / 2 = ‖B₂ x‖ ^ 2 / 2
theorem hj_torus_exists (hD : Diophantine (ι/2) γ 1) (hres : ‖HJres f₀ a b‖ρ ≤ e) (hsmall : …) :
    ∃ ζ a' b', HJres (f₀ + ζ) a' b' = 0 ∧ ‖ζ‖ρ∞ ≤ C e
theorem ck_laplace_collar (hdata : Ana f) : ∃ τ > 0, ∃ Φ₂, Harmonic on collar S τ ∧ Φ₂|_S = f ∧ ∂ₙΦ₂|_S = 0
theorem rationalStellarator_stepped (Δp := Δp₀) : ∃ U B₂, SteppedEquilibrium (Ω₁ exactTorus) U (field (1/4)) B₂ Δp₀
```

### 3.3 Cost

- Gluing and structure: 3 days.
- HJ Newton with conjugacy: 3–4 weeks. It reuses `StripAlgebra`, `Cohomological` and `KamSequence`.
- CK collar: 2 weeks.
- Oracle and certificate at β ≈ 1 %: 2 weeks.

Total **≥ 8 agent-weeks**, after the `FlowField` refactor.

### 3.4 Stability: what could follow (assessment)

- **Mercier and ballooning do not apply.** p′ = 0 a.e. with a δ-function at S.
- **The relevant theory is the ideal plasma–vacuum interface energy principle.** It covers surface currents
  (Bernstein–Frieman–Kruskal–Kulsrud 1958 *(memory)*) and the MRxMHD stability of Hole–Hudson–Dewar
  (NF 47 (2007) 746) and Mills–Hole–Dewar (JPP 75 (2009) 637) *(memory)*. In it,
  δW = ½∫_{V₁}|∇χ₁|² + ½∫_{V₂}|∇χ₂|² + ½∮_S |ξ_n|² [[n·∇(p + B²/2)]].
- For tangent curl-free fields, n·∇(B²/2) = B²κ_n = −B² II(b, b) (the field lines' normal curvature on S). At
  O(Δp), [[n·∇B²/2]] ≈ 2Δp κ_n plus a term from the field-direction jump α = O(Δp/B²).
- **Numerics (`/tmp/laneA8`, torus A):** κ_n ∈ [−0.965, 1.260], area-mean +0.032, negative on 48 % of S. So the
  pointwise sufficient criterion [[·]] ≥ 0 **fails**. On a torus it must fail somewhere, by the toroidal min-B
  obstruction.
- **Heuristic outcome.** For high-|k|, near-field-aligned interface modes on the outboard side:
  - the inner-side bending energy is ~B²(k·b₁)²/|k| ≥ B²γ²/|k|³ (Diophantine), which tends to 0;
  - the outer side contributes ~B²|k|α²;
  - so δW/|ξ|² ≈ B²|k|α² − 2Δp|κ_n| + O(|k|⁻³). For small Δp this is negative at |k| ~ 1/Δp.
- So **an interface-interchange instability witness is the likely formal outcome** for the single-step rung in
  this non-optimized field. It would mirror the Phase-9 Mercier-instability result.
- A *stable* finite-β rung probably needs magnetic-well design (a positive surface-averaged good curvature), not
  this field.
- **Do not promise stability.** The formal target would be the interface δW formula plus a trial-function witness
  (cost about 2 weeks after existence), or a conditional margin.

---

## 4. Counterexample and honesty checks

- All numbers in §§0–3 are double-precision floating-point observations.
  - The ℓ¹ norms at r = 0.1257 include round-off amplified by weights e^{20}, at about 10⁻¹⁰ (the model-field
    run shows 6×10⁻⁸ noise). The coil residual 8.4×10⁻⁵ is far above that.
  - Birkhoff agreement at 10⁻¹² is evidence of a regular torus, not a proof.
- The coil set in the computations uses ideal ∇φ, not the TF rectangle. Its return legs add ~2/Λ ≈ 2×10⁻⁶ of
  nearly uniform field. That changes the refit but not the conclusions.
- Lemma GC-1 was proved by hand and checked numerically at one point of `field (1/4)` (E = 2, μ = 0.7,
  m = q = 1). There v_∥B̃ = v_∥B* + μ b×∇|B| holds to 3×10⁻¹¹ with central differences. Re-check it in sympy
  before formalizing.
- κ for the coil and GC runs is assumed similar to torus A (same ι, nearby tori). If the twist at the GC tori is
  smaller, the margin shrinks. Compute the twist before committing to ρ₀.
- Novelty: none claimed. GC drift surfaces as field lines of a modified field are classical. ELP-S is published.
  The contributions here are the quantitative rejection of 1(b), the coil and GC torus evidence, the cost routing
  and the Lean statements.
