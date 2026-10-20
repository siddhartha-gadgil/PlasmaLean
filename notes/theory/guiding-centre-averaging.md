# Guiding-centre averaging and exact-symmetry alpha confinement (M4, T8)

Track: M4/T8 (implementation plan §4–§6, Cycle 3). Lane A (discovery), 20 Oct 2026. **Nothing in this note is a
compiled Lean theorem.** Status tags follow `README.md`: **published** (with locator), **proved informally**
(sympy-checked where stated), **numerical observation**, **conjectured**, **lead**.

Scripts are in `/tmp/laneA4/scripts/`: `solovev_band.py`, `instance.py`, `birthfrac.py`, `gyro_noether.py`,
`qa_gc.py`, `qa_growth.py`, `qa_avg_consts.py`, `qa_kfold.py`. They use the pyQSC/sympy virtualenv `/tmp/laneA3/venv`.

Starting point: `PlasmaLean/Theory/Kinetic/GuidingCentre.lean`. Its bound
`|X(t) − X(0) − ∫v_∥b| ≤ ρ_L (G/B_min) s t` (constant 1) and its linear μ-drift bound are honest. The time scale for a
3.5 MeV alpha is ≈ 10⁻⁷ s.

---

## 0. Summary

1. **You cannot "upgrade" the reduction bound for X itself into a confinement time.** The secular term
   `ρ_L s t/L_B` is the actual ∇B/curvature drift, which is physical and not an error. Confinement has to come from a
   (near-)invariant flux-like observable: p_φ, the Noether momentum p_K, or the Boozer momentum P. The averaging has to
   be applied to that observable's drift, not to X. §2 gives two rigorous lemmas with explicit constants that do this
   (**proved informally**, Lean-cheap):
   - **Lemma A (oscillatory integration by parts, k-fold).** For `P′ = a sinΦ + b cosΦ + e` with `Φ′ = Ω ≥ Ω₀ > 0`:
     `|ΔP| ≤ 2 sup(|a|+|b|)/Ω₀ + (sup|(a/Ω)′| + sup|(b/Ω)′| + sup|e|) t`. Iterating it k times gives the secular rate
     `sup|a_k|`, where `a_{j+1} = (a_j/Ω)′`.
   - **Theorem B (gyro-integrated Noether identity, full orbit, exact).** Let `δ = B×K + ∇ψ` be the symmetry defect and
     `U = B×δ/|B|²`. Then `d/dt[p_K + m⟨U(x), v⟩] = q v_∥ δ_∥ + m⟨DU(x)v, v⟩` exactly (sympy-checked). The defect
     forcing rate drops from `|q| s |δ|` (current `noether_approx_band`) to `|q| s |δ_∥| + |m| s² ‖DU‖`. The
     perpendicular part therefore gains a factor of about ρ_L/L_δ.
2. **Exactly symmetric fields resolve the 14 Oct obstruction with no averaging** (§3). Energy plus p_φ give the Störmer
   band `|p_φ − qΨ(x)| ≤ m s R(x)`. This is sharp for those two invariants. In minor radius it is a band of width
   ≈ 2ρ_pol = 2m s/(qB_pol). It differs from the true banana width only by a factor of about 1/√ε ≈ 2, and closing
   that gap needs μ. The library's crude band already has this form. What failed before was the parameter choice:
   `iter_like` has L = 6 m and A = 1.4 T, so a ≈ 1.55 m and B_pol ≈ 0.7 T, which makes 2ρ_pol ≈ 0.77 m ≈ a/2.
   **Rescaled Solov'ev instance:** L = 10 m, A = 7/4 T, F = 50 T·m. That gives B_axis = 5 T exactly, R₀ ≈ 9.66 m,
   a ≈ 2.59 m, κ ≈ 1.41, β_axis = 147/3200 ≈ 4.6% (exact), ⟨β⟩ ≈ 2.2%, I_p ≈ 11.9 MA, q₀ ≈ 2.02 (exact formula),
   q_edge ≈ 2.65 (numerical). In this instance the **existing** theorem `Solovev.orbit_confined` applies verbatim to
   3.5 MeV alphas: rigidity 0.26940 T·m ≤ AL/64 = 0.27344 T·m. So every 3.5 MeV alpha (full orbit, any pitch) born
   with ψ̃ ≤ ψ̃_edge/4 stays in ψ̃ ≤ (11/12)ψ̃_edge for **all t ∈ ℝ**. This birth region carries ≈ 57% of the fusion
   power for a p² birth profile (numerical observation). A sharp Störmer version (§3.3) widens it to ψ̃ ≤ 0.415ψ̃_edge
   (≈ 80% of fusion power).
3. **Nearly symmetric fields** (§4). In the truncated precise-QA Boozer GC model, the worst-case bound gives ≈ 0.3–1 ms.
   - Lemma A with k = 1, 2, 3 reduces the secular rate by factors of 5×10⁻², 1.2×10⁻² and 2.6×10⁻³ for passing alphas
     (numerical observation of `sup|a_k|/sup|a_0|` along orbits). With k = 3 this reaches about 0.1–0.4 s, the
     slowing-down scale. A rigorous version needs a-priori bounds on a_k over the phase-space region. These are
     explicit rational functions, so interval arithmetic can supply them.
   - Direct integration shows that P stays bounded, with no visible secular growth over 20 ms (≈ 3500 transits). That
     is consistent with KAM: with μ fixed, the GC model has 2 DOF.
   - Trapped particles are not covered (Φ′ changes sign). In rippled tokamaks they have genuine stochastic losses
     (Goldston–White–Boozer), so no uniform averaging theorem can exist for them.
4. **Recommended Lean order** (§6): (i) `Design/SolovevAlpha.lean`, about 1 day, near-certain; (ii) Theorem B in
   `Theory/Kinetic/GyroNoether.lean`, 1–2 days; (iii) Lemma A in `Theory/Kinetic/OscillatoryAveraging.lean`, 1 day.

---

## 1. Literature: rigorous averaging for charged particles (with locators)

| Source | Setting and hypotheses | Conclusion | Explicit constants? | Status |
| --- | --- | --- | --- | --- |
| E. Hairer & C. Lubich, *Long-term analysis of a variational integrator for charged-particle dynamics in a strong magnetic field*, Numer. Math. **144** (2020) 699–728, **Theorem 2.1** (preprint CRC 1173 2018-6, §2.1, eq. (1.1)–(1.4)) | `ẍ = ε⁻¹ ẋ×B(x) + E(x)`, `B = ∇×A`, `E = −∇U` smooth, `\|B\| ≥ 1`, `x(0), ẋ(0) = O(1)`, solution stays in a compact K | `\|I(t) − I(0)\| ≤ C_N ε` for `t ≤ ε^{−N}`, every N, with `I = \|ẋ×B\|²/(2\|B\|³)` | No: C_N depends on N, on the first N+1 derivatives of B and E on K, and on the data bounds | **published** (read in preprint) |
| E. Hairer, C. Lubich & Y. Shi, *Large-stepsize integrators for charged-particle dynamics over multiple time scales*, Numer. Math. **151** (2022) 659–691, **Theorem 4.1** (modulated Fourier expansion `x = Σ z_k e^{ikt/ε} + R_N`, `R_N = O(t²ε^N)` on `[0,T]`) and **Theorem 6.1** | Maximal ordering `B = B₀/ε + B₁(x)`, `\|B₀\| = 1`. Thm 6.1 also assumes `B₁(x) = B₁(x_⊥) + εB₂(x)` (weak x_∥ dependence) and an orbit in compact K for `t ≤ c/ε` | Thm 6.1: `\|x_⊥(t) − y_⊥(t)\| ≤ Cε` for `0 ≤ t ≤ c/ε`, with `ẏ_⊥ = εE_⊥(y_⊥)×B₀`. This is the cleanest published "O(ε) error over O(1/ε)" GC drift theorem | No (C depends on derivative bounds, M, c) | **published** (read) |
| G. Benettin & P. Sempio, *Adiabatic invariants and trapping of a point charge in a strong nonuniform magnetic field*, Nonlinearity **7** (1994) 281–304, doi:10.1088/0951-7715/7/1/014 | Real-analytic B (complex strip), E = 0, `\|B\|` bounded below, region of phase space | Nekhoroshev–Neishtadt normal form: μ, plus a second invariant (parallel energy), conserved for times `exp(c/ε)`. The system is integrable up to an exponentially small remainder | c and the constants are constructive in principle but not given as numbers | **published** (abstract and Hairer–Lubich's summary; theorem numbers not read) |
| A. I. Neishtadt, *The separation of motions in systems with rapidly rotating phase*, J. Appl. Math. Mech. **48** (1984) 133–139 | Analytic `ẋ = εf(x,φ)`, `φ̇ = ω(x) ≥ ω₀ > 0` | Near-identity change removes the φ-dependence up to `O(e^{−c/ε})`. Adiabatic invariants (including a charge in a weakly inhomogeneous field) persist for exponentially long times. The exponential remainder cannot be removed | Constructive, implicit | **published** (abstract) |
| V. I. Arnold, *Small denominators and problems of stability of motion in classical and celestial mechanics*, Russ. Math. Surveys **18:6** (1963) 85–191, **Ch. II §4 "Magnetic traps"** | Axisymmetric trap: after p_φ, a 2-DOF system | Perpetual adiabatic invariance via KAM (invariant 2-tori separate the 3-D energy shell) | No | **lead** (section title verified; statement not read) |
| M. Kruskal, *Asymptotic theory of Hamiltonian and other systems with all solutions nearly periodic*, J. Math. Phys. **3** (1962) 806 | Smooth, nearly periodic systems | All-orders near-identity transformation; an adiabatic invariant to every order (μ series) | No | **published** (classical) |
| V. I. Arnold, V. V. Kozlov & A. I. Neishtadt, *Mathematical Aspects of Classical and Celestial Mechanics*, 3rd ed., Springer (2006), **Ch. 6** (§6.1 single-frequency averaging: `\|x(t) − J(t)\| = O(ε)` for `t ≤ 1/ε`; §6.4 adiabatic invariants, including charged particles) | `ẋ = εf(x,φ)`, `φ̇ = ω(x) ≥ c > 0`, Lipschitz | First-order averaging theorem. The proof is near-identity change plus Grönwall, and constants can be read off the proof | Implicit | **published** (locator from memory: verify section numbers) |
| J. A. Sanders, F. Verhulst & J. Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, 2nd ed., Springer AMS **59** (2007), Ch. 2 (periodic averaging; the first-order theorem in §2.8) and Ch. 7 (averaging over one angle) | `ẋ = εf¹(x,t) + ε²f^{[2]}`, f¹ T-periodic and Lipschitz | `‖x(t) − z(t)‖ = O(ε)` on `0 ≤ εt ≤ L` | Lipschitz and Grönwall constants are explicit in the proof | **published** (theorem numbers to verify) |
| S. Possanner, *Gyrokinetics from variational averaging: existence and error bounds*, J. Math. Phys. **59** (2018) 082702 | Variational averaging of the Lorentz Lagrangian | Existence and error bounds for the GC/gyrokinetic reduction | Not checked | **lead** (cited by HLS22 as [21]) |
| F. Filbet & L. M. Rodrigues, J. Éc. polytech. Math. **7** (2020) 1009; F. Golse & L. Saint-Raymond, J. Math. Pures Appl. **78** (1999) 791; M. Bostan, Multiscale Model. Simul. **8** (2010) 1923; C. Cheverry, J. Differential Equations **262** (2017) 2987 | Vlasov in a strong field (PDE level) | Rigorous GC limits, first-order drifts (E×B, ∇B, curvature); second-order gyrokinetics; anomalous transport | No | **published** (citations verified via Filbet–Rodrigues) |
| J. W. Burby, N. Kallinikos & R. S. MacKay, J. Math. Phys. **61** (2020) 093503; *Approximate symmetries of guiding-centre motion*, J. Phys. A **54** (2021) 125202 (corrigendum **57** (2024) 309501; arXiv:2010.08968) | First-order GC Hamiltonian structure | QS ⇔ a continuous symmetry of the first-order GC system. Under force balance, an approximate symmetry agrees with QS to leading order | No | **published** (abstract) |
| R. J. Goldston, R. B. White & A. H. Boozer, PRL **47** (1981) 647 | Trapped energetic ions in a rippled tokamak | Stochastic ripple diffusion above a threshold. A physical obstruction to any uniform-in-pitch averaging bound | n/a | **published** (classical; locator from memory) |

**Verdict.** Every published rigorous result has non-explicit constants. The strongest require analyticity (exponential
times) or many derivatives (polynomial times), plus an a-priori compact-region hypothesis. None can be turned directly
into a numerical confinement time without re-deriving the constants. For PlasmaLean the useful pattern is the elementary
step at the heart of all these proofs, done on a scalar observable with explicit constants: integration by parts against
a fast phase (§2).

---

## 2. Formalizable lemmas with explicit constants (proved informally)

### 2.1 Lemma A: oscillatory integration by parts

**Statement.** Let `T ≥ 0`. Let `P, Φ, a, b, Ω, e : ℝ → ℝ` with, for `s ∈ [0,T]`:
- `HasDerivAt P (a s · sin Φ s + b s · cos Φ s + e s) s` and `HasDerivAt Φ (Ω s) s`;
- `HasDerivAt (fun r => a r / Ω r) (α s) s` and `HasDerivAt (fun r => b r / Ω r) (β s) s`;
- `Ω s ≥ Ω₀ > 0`, `|a s| + |b s| ≤ A`, `|α s| + |β s| ≤ A₁`, `|e s| ≤ η`.

Then for `t ∈ [0,T]`: `|P t − P 0| ≤ 2A/Ω₀ + (A₁ + η) t`.

**Proof.** Put `F = (−a cosΦ + b sinΦ)/Ω`. Then
`F′ = a sinΦ + b cosΦ − α cosΦ + β sinΦ`, so `(P − F)′ = e + α cosΦ − β sinΦ`, which is bounded by `A₁ + η`.
Apply `invariant_drift` to `P − F`, then use `|F| ≤ A/Ω₀` at both ends. ∎

**Iteration.** The remainder `α cosΦ − β sinΦ` has the same form with `(a, b) ↦ (−β, α)`. So k applications give
`|ΔP| ≤ 2Σ_{j<k} A_j/Ω₀ + (A_k + η)t`, where `A_{j+1}` bounds the derivative of `(a_j, b_j)/Ω`.

**Comparison with SVM/AKN.** This is the scalar observable version of the first-order averaging theorem. Applied to the
slow variable it gives `O(ε)` oscillation plus `O(ε·ν/Ω)` secular drift, where ν is the slow rate. When `ν = O(ε)`
(standard form `ẋ = εf`) this is `O(ε²)` drift, i.e. `O(ε)` error up to `t ~ 1/ε`. It needs no Lipschitz/Grönwall step
because the observable's derivative is evaluated along the supplied true orbit, which is the library's style.

### 2.2 Theorem B: gyro-integrated Noether identity (full orbit, exact)

**Setting** (as in `Theory/Kinetic/Noether.lean`). Newton–Lorentz orbit `x′ = v`, `m v′ = q v×B(x)`, E = 0. K is a
Killing field, ψ has gradient G, and `noetherMomentum = m⟨K(x), v⟩ + qψ(x)` with derivative `q(⟨K, v×B⟩ + ⟨G, v⟩)`.
Define the **defect vector** `δ(y) := B(y)×K(y) + G(y)` (`SymmetricFlux B G K ⇔ δ ≡ 0`) and
`U(y) := B(y)×δ(y)/|B(y)|²`, with Fréchet derivative DU.

**Identity** (pointwise algebra, sympy-checked in `gyro_noether.py`, residual 0):

    q⟨v, δ⟩ = q (⟨v,B⟩⟨B,δ⟩/|B|²) − m⟨U, v′⟩,   using v′ = (q/m) v×B.

Hence, along the orbit, with `Q := p_K + m⟨U(x), v⟩`:

    Q′ = q v_∥ δ_∥ + m ⟨DU(x)[v], v⟩,    v_∥ δ_∥ := ⟨v,B⟩⟨B,δ⟩/|B|².

**Band.** If `|B| ≥ B_min > 0`, `|⟨B,δ⟩|/|B| ≤ δ_∥`, `|U| ≤ u ≤ |δ|/B_min` and `‖DU‖ ≤ u₁` on the region, then

    |q||ψ(x t) − ψ(x 0)| ≤ |m|s(‖K(x t)‖ + ‖K(x 0)‖) + 2|m| s u + (|q| s δ_∥ + |m| s² u₁) t.

**Gain.** The old rate is `|q| s |δ|`. The new perpendicular rate is `|m| s² u₁ ≈ |q| s |δ| · (ρ_L/L_δ)`, where L_δ is
the gradient scale of δ/B. The parallel part survives unchanged.
- If ψ is an exact first integral of the actual field lines (`B·∇ψ = 0`, flux surfaces exist) but K is only an
  approximate symmetry, then `δ_∥ ≡ 0` and the whole drift is reduced by ρ_L/L_δ.
- For tokamak TF ripple (K = rotation, `δ = δB×K`), the parallel part is `δ_∥ ~ R δB·B_pol/B`. The two rates are then
  comparable: `R B_pol/B ≈ 1.5 m` against `ρ_L N ≈ 0.054 × 18 ≈ 1 m` (estimate). The net gain is ~×7. That is not
  enough alone; the residual parallel forcing `v_∥δ_∥ ∝ cos Nφ` must then be fed into Lemma A (passing particles only).

### 2.3 Why the crude GC reduction bound is the wrong object to improve

The identity `dX/dt = v_∥b + (m/q)v×d(B/|B|²)/dt` splits the residual into three parts:
1. a gyro-oscillating part, which integrates by parts via `v_⊥ = −(m/(q|B|²)) v′×B`, the same trick as Theorem B;
2. the ∇B drift `(μ/(qB)) b×∇B`;
3. the curvature drift `(m v_∥²/(qB)) b×κ`.

Parts 2 and 3 are secular, of size ρ_L s/L_B, and physical. Doing step 1 with explicit constants gives the rigorous
first-order GC theorem
`|X̃(t) − X̃(0) − ∫(v_∥b + v_∇B + v_κ)| ≤ C₁ρ_L + C₂ (ρ_L/L)² s t`, where C₂ depends on `sup‖DB‖, sup‖D²B‖` and X̃ is X
plus an explicit O(ρ_L²/L) correction. That is the Northrop/Kruskal first-order statement, i.e. Hairer–Lubich–Shi
Thm 6.1 without the restricted geometry. **Conjectured** with constants of order 10 (not derived here). It does **not**
yield confinement by itself: one still needs drift ⊥ ∇ψ, which is exactly what p_K/P encode. Recommendation: do not
formalize this before §6 (i)–(iii).

---

## 3. Exactly symmetric fields: sharp band and 3.5 MeV alphas for all time

### 3.1 Sharp consequence of the two exact invariants (proved informally)

Axisymmetric B (`AxisymmetricFlux`, any toroidal part `F(Ψ)∇φ`, since the toroidal field exerts no z-torque),
`p_φ = m R v_φ + qΨ(x)` conserved, speed s conserved. Put `k = m s/q` (rigidity) and `σ₀ = v_φ(0)/s ∈ [−1,1]`.

    Ψ(x_t) = Ψ(x_0) + k(R₀σ₀ − R_t σ_t)   ⇒   Ψ(x_t) − kR_t ≤ Ψ₀ + kR₀σ₀  and  Ψ(x_t) + kR_t ≥ Ψ₀ + kR₀σ₀.

The accessible set is the Störmer region `{y : |p_φ − qΨ(y)| ≤ m s R(y)}`. Every point in it is consistent with the two
exact invariants (choose v with `v_φ = (p_φ − qΨ)/(mR)` and `|v| = s`). So **no argument using only energy and p_φ can
do better**. `CanonicalMomentum.flux_band` is this bound with R replaced by ‖x‖ (≥ R) and σ₀ by ±1.

**Width.** With `|∇Ψ| = R B_pol`, the band in minor radius is `Δr ≈ k(R₀ + R_t)/(R B_pol) ≈ 2ρ_pol`, where
`ρ_pol = m s/(qB_pol)`. Using `B_pol ≈ εB/q_s`, `ρ_pol = q_sρ_L/ε`. The true GC banana width is about
`2√ε ρ_pol = 2q_sρ_L/√ε` for fat trapped orbits. The Noether band is wider than that by about `1/√ε ≈ 2` at mid-radius.
So the band is ρ_pol, not ρ_L: it already exploits the symmetry. The remaining √ε needs μ.

**Conditional μ-band** (proved informally, a possible later target). If additionally `μ(t) ≥ μ_lo` (supplied, e.g.
from Benettin–Sempio or Hairer–Lubich, which have non-explicit constants), then
`|v_φ| ≤ |v_∥| + |v_⊥|B_pol/B` with `v_∥² ≤ s² − 2μ_loB_min/m`. This shrinks the band to about
`2ρ_pol (v_∥,max/s) + 2ρ_L`, i.e. banana order.

### 3.2 Numbers for the library Solov'ev family (numerical observation, `solovev_band.py`, `instance.py`)

Family: `Ψ = (A/L²)ψ̃`, `ψ̃ = R²z²/2 + (R² − L²)²/4`, region `ψ̃ ≤ L⁴/16`. The shape is fixed:
`R ∈ [L/√2, L√1.5]`, `a = 0.2588L`, `R₀ = 0.966L`, κ ≈ 1.41. `B_pol` at the midplane edge is exactly A/2.
Exact relations: `β_axis = 3A²L²/(8F²)` and `q₀ = (F/L)/(√2A)` (on-axis linearization: `Ψ ≈ A(x² + z²/2)`).

For a 3.5 MeV alpha, `k = 0.2694 T·m`, `v = 1.299×10⁷ m/s` and `ρ_L(5 T) = 5.4 cm`. B_axis = 5 T throughout. The last
column is the largest birth surface from which **every** alpha (any start point on the surface, any pitch) is
confined for all time by the sharp band, with the minor radius measured at the outboard midplane:

| L (m) | a (m) | A (T) | I_p (MA) | q_edge | β_axis | birth region confined forever |
| --- | --- | --- | --- | --- | --- | --- |
| 6 | 1.55 | 1.4 (`iter_like`) | 5.7 | 3.31 | 2.9% | **none** (the 14 Oct obstruction) |
| 6 | 1.55 | 2.0 | 8.2 | 2.32 | 6.0% | ψ/ψ_e ≤ 0.17 (r/a ≤ 0.43) |
| 6.57 | 1.70 | 1.4 | 6.3 | 3.31 | 2.9% | none |
| 6.57 | 1.70 | 2.0 | 8.9 | 2.32 | 6.0% | ψ/ψ_e ≤ 0.23 (r/a ≤ 0.51) |
| 9.66 | 2.50 | 1.4 | 9.2 | 3.31 | 2.9% | ψ/ψ_e ≤ 0.25 (r/a ≤ 0.53) |
| 9.66 | 2.50 | 2.0 | 13.1 | 2.32 | 6.0% | ψ/ψ_e ≤ 0.47 (r/a ≤ 0.71) |
| 10 | 2.59 | 1.4 | 9.5 | 3.31 | 2.9% | ψ/ψ_e ≤ 0.28 (r/a ≤ 0.55) |
| **10** | **2.59** | **7/4** | **11.9** | **2.65** | **4.6%** (⟨β⟩ 2.2%) | **ψ/ψ_e ≤ 0.415 (r/a ≤ 0.67)** |

Notes on the table:
- Pitch-resolved at L = 10, A = 1.4: σ₀ = +1 (worst) gives ψ/ψ_e ≤ 0.28; σ₀ = 0 gives ≤ 0.62.
- Fusion-power fraction born inside ψ/ψ_e ≤ f, for `P_fus ∝ p² ∝ (1 − ψ/ψ_e)²` (`birthfrac.py`): 0.57 at f = 1/4,
  0.62 at f = 0.277, 0.80 at f = 0.415.
- I_p uses `∮B_pol dl/μ₀`. q_edge is a field-line quadrature with F constant. Neither is certified.

**Conclusion.** At a ≈ 1.7 m and 5 T, the Solov'ev (FF′ = 0) family needs A ≥ 1.6 (β ≥ 3.8%, q_edge ≤ 2.9) before any
birth region works. At a ≈ 2.5 m, realistic B_pol ≈ 0.7–0.9 T (I_p ≈ 9–12 MA) confines alphas born in the inner
50–67% of minor radius, carrying 57–80% of fusion power, **for all time**. The criterion is roughly
`a ≳ 4–5 ρ_pol(3.5 MeV)`.

### 3.3 What is immediately Lean-provable

`Solovev.orbit_confined` (hypotheses: `|m|‖v₀‖ ≤ |q|AL/64`, `ψ̃₀ ≤ L⁴/64`, `‖x₀‖ ≤ 4L/3`) applies **unchanged**
with L = 10, A = 7/4, F = 50, because `AL/64 = 0.2734375 ≥ 0.26940`. The rigidity margin is 1.5%. From
`6.6447e-27 s² ≤ 2·3.5e6·1.6022e-19` we get `s ≤ 1.29918×10⁷`, and the threshold is `s ≤ 1.3187×10⁷`.

The sharp version (ψ/ψ_e ≤ 0.415 at the same A; or A = 7/5 with q_edge 3.3) needs a new region lemma: a
`R(y) ≤ R_out(c)` bound in place of `‖y‖ ≤ 4L/3`, and an R-based band. That is a modest extension of
`flux_band`/`orbit_trapped`.

---

## 4. Nearly symmetric fields: what averaging buys (numerical observation)

Model: the vacuum Boozer GC model of `near-axis-quasisymmetry.md` §4, with the truncated precise-QA field scaled to
a = 1.7 m and B₀ = 5.7 T: `G = 58.1 T·m`, `ι = 0.4226`, `η̄ = −0.0707 m⁻¹`, `B₂c = 0.01654`, `b₀ = −0.01367`,
`b₁ = −4.27×10⁻⁴ T/m²`. Then `ε_QS(a) = 2|b₁|a² = 2.47×10⁻³ T`. The forcing is
`P′ = a(t) sin 2φ` with `a = 2b₁r²(q²ρ²B/m + μ)` and `Φ = 2φ`, `Ω = 2qρB²/(Gm)`.

- **Actual drift** (`qa_gc.py`, `qa_growth.py`, DOP853, rtol 1e-11, energy conserved to 1e-13). For passing alphas
  (λ = v_∥/v ∈ {0.4, 0.9}, r₀ ∈ {0.5a, 0.75a}), `max|ΔP|/q = 3–8×10⁻⁴ T·m²`. It does not grow from 0.2 ms to 20 ms.
  The linear bound at 2 ms is `3.5 T·m²`, a ratio of about 10⁻⁴. Trapped alphas (λ = 0.15, 0.2) reach
  `6×10⁻³ – 1.8×10⁻² T·m²` and saturate. The available flux is ψ_a ≈ 8.2 T·m².
- **First-order Lemma A** (`qa_avg_consts.py`). The secular/linear rate ratio is
  `(A₁/Ω₀ + A₀W₁/Ω₀²)/A₀ ≈ 0.058` (r₀ = 0.5a, λ = 0.9), 0.053 (λ = 0.6) and 0.13 (λ = 0.4). The constant term
  `2A₀/(qΩ₀) ≤ 8×10⁻⁴ T·m²` is negligible.
- **k-fold** (`qa_kfold.py`, spline derivatives). `sup|a_k|/sup|a_0|` is 1, 5.3×10⁻², 1.2×10⁻² and 2.6×10⁻³ for
  k = 0..3. It is not geometric at the ν/Ω ≈ 0.05 rate, because a(t) contains θ-harmonics at `(2 ± jι)φ̇`. Near
  `2 − 5ι = −0.11` there is a small-denominator resonance, but its amplitude is about `(η̄r)⁵ ≈ 10⁻⁵`.

**Translation.** The note's linear-bound times (0.33–0.55 ms for λ ≥ 0.9, with ε_QS from the full B₂₀ fit) become:

| k | time |
| --- | --- |
| 1 | ≈ 6–10 ms |
| 2 | ≈ 30–50 ms |
| 3 | ≈ 0.13–0.2 s, the slowing-down scale (τ_s ≈ 0.4 s) |

These are **model** results (R1 Boozer GC, formal link to physics) and **not rigorous** until the A_k are bounded a
priori. A_k are explicit rational functions of (ψ, θ, φ, ρ): iterate `f ↦ L_X(f/Ω)`, where L_X is the Lie derivative
along the GC vector field. Their sup over `{r ≤ r_c, λ ≥ λ_min}` is therefore an interval-arithmetic certificate
(lane C). The trapping argument of `near-axis-quasisymmetry.md` §4 then applies with `ε T` replaced by the Lemma A
bound.

**Obstructions and caveats.**
1. Trapped and barely passing orbits: Φ′ changes sign, so Lemma A does not apply. Bounce-averaging (J_∥, T8) is the
   right tool. In rippled tokamaks there are genuine stochastic losses (Goldston–White–Boozer), so this is not a proof
   artefact.
2. The time scales as `1/(ε_QS·δ_k)`, i.e. it is ε_QS-linear with a better constant. A true ε² law needs the
   ε-dependence of Ω (the b₁ cos 2φ term in B), which produces a genuine `⟨cos²⟩ ≠ 0` second-order secular term.
3. A cleaner all-time route in the R1 model is a posteriori KAM. With μ fixed, the GC system is 2-DOF autonomous, so
   invariant 2-tori bound the 3-D energy shell (Arnold 1963 Ch. II §4 analogue). The bounded-P numerics are consistent
   with this. Shared machinery with T7 (de la Llave a posteriori KAM): **lead**, long term.

---

## 5. Counterexample attempts

- **Lemma A with Ω crossing zero.** It fails: F blows up. The hypothesis Ω ≥ Ω₀ > 0 is necessary (trapped particles).
- **Theorem B when B vanishes.** U is undefined. Hypothesis: `B ≠ 0` along the orbit and `|B| ≥ B_min` on the region.
- **Störmer band "sharpness" versus actual orbits.** Sharp as a statement from two invariants (§3.1, explicit
  velocity). Actual orbits stay in the much thinner banana shell because μ is adiabatic. That is not a contradiction.
- **Rescaling cheats?** The β and q values are reported. β_axis = 4.6% at q_edge ≈ 2.65 is aggressive but
  tokamak-plausible, and ⟨β⟩ ≈ 2.2%. No MHD stability is claimed for the instance. The Solov'ev profile has
  p ∝ (ψ_e − ψ) and constant F, with pressure-driven current only. A version with FF′ ≠ 0 (`ψ̃ + λL²z²/2`) would
  decouple I_p from β; p_φ conservation is unaffected by F(Ψ). **Not computed.**

---

## 6. Recommended Lean targets

### (i) `PlasmaLean/Design/SolovevAlpha.lean` — 3.5 MeV alphas confined for all time (feasibility ~95%, under a day, ~60 lines)

```lean
theorem alpha35_rigidity (s : ℝ) (hK : 6.6447e-27 * s ^ 2 ≤ 2 * (3.5e6 * 1.6022e-19)) :
    |(6.6447e-27 : ℝ)| * s ≤ |(2 * 1.6022e-19 : ℝ)| * (7 / 4 * 10 / 64)
theorem reactor_axis_field : field (7/4) 10 50 (toLp 2 ![10, 0, 0]) = toLp 2 ![0, 5, 0]
theorem reactor_beta (μ₀ : ℝ) (hμ : 0 < μ₀) :
    2 * μ₀ * (3 * (7/4 : ℝ) ^ 2 / (16 * μ₀)) / 5 ^ 2 = 147 / 3200
theorem reactor_alpha_confined {x v : ℝ → Space}
    (h : LorentzOrbit 6.6447e-27 (2 * 1.6022e-19) (fun _ => 0) (field (7/4) 10 50) x v)
    (hK : 6.6447e-27 * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * 1.6022e-19))
    (hψ0 : psiT 10 (x 0) ≤ 10 ^ 4 / 64) (hx0 : ‖x 0‖ ≤ 4 * 10 / 3) (t : ℝ) :
    psiT 10 (x t) ≤ 11 * 10 ^ 4 / 192 ∧ 10 ^ 2 / 2 ≤ R2 (x t)
```

The proof is `orbit_confined` plus `alpha35_rigidity`; the latter follows the same `nlinarith [sq_nonneg …]` pattern as
`alpha_rigidity`. Sanity corollaries: `reactor_pressure_nonneg` and the q₀ identity `(F/L)/(√2A)` (optional). The
docstring must say: idealized, axisymmetric, full orbit, collisionless, no MHD stability claim, and orbits supplied.
This closes the 14 Oct obstruction **in an exact symmetric equilibrium**.

### (ii) `PlasmaLean/Theory/Kinetic/GyroNoether.lean` — Theorem B (feasibility ~85%, 1–2 days, ~200 lines)

```lean
def defectVec (B G K : Space → Space) (y : Space) : Space := cross (B y) (K y) + G y
def gyroCorr (B G K : Space → Space) (y : Space) : Space :=
  (‖B y‖ ^ 2)⁻¹ • cross (B y) (defectVec B G K y)
theorem gyro_defect_identity (m q : ℝ) (hm : m ≠ 0) (β δ v : Space) (hβ : β ≠ 0) :
    q * ⟪v, δ⟫ = q * (⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2)
      - m * ⟪(‖β‖ ^ 2)⁻¹ • cross β δ, (q / m) • cross v β⟫        -- pure algebra (the sympy identity)
theorem gyroNoether_hasDerivAt (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hU : ∀ y, HasFDerivAt (gyroCorr B G K) (DU y) y)
    (hB : ∀ s, B (x s) ≠ 0) (s : ℝ) :
    HasDerivAt (fun r => noetherMomentum m q K ψ x v r + m * ⟪gyroCorr B G K (x r), v r⟫)
      (q * (⟪v s, B (x s)⟫ * ⟪B (x s), defectVec B G K (x s)⟫ / ‖B (x s)‖ ^ 2)
        + m * ⟪DU (x s) (v s), v s⟫) s
theorem gyroNoether_band  -- |q||Δψ| ≤ |m|s(‖K x_t‖+‖K x_0‖) + 2|m| s u + (|q| s δpar + |m| s² u₁) t
theorem gyroNoether_trapped_until  -- via trapped_until, as noether_orbit_trapped_until
```

Sanity cases:
- δ ≡ 0 gives U ≡ 0 and recovers `noether_flux_band`;
- an exact first integral (`⟪B, G⟫ = 0`) gives a pure `|m|s²u₁` rate;
- an explicit uniform-B witness with a linear defect.

Reuses `hasDerivAt_cross`, `cross_cross_eq` and the product rules already in `GuidingCentre.lean`.

### (iii) `PlasmaLean/Theory/Kinetic/OscillatoryAveraging.lean` — Lemma A (feasibility ~90%, 1 day, ~120 lines)

```lean
theorem osc_ibp_drift {P Φ a b Ω e α β : ℝ → ℝ} {T A A₁ η Ω₀ t : ℝ} (hΩ₀ : 0 < Ω₀)
    (hP : ∀ s ∈ Set.Icc 0 T, HasDerivAt P (a s * Real.sin (Φ s) + b s * Real.cos (Φ s) + e s) s)
    (hΦ : ∀ s ∈ Set.Icc 0 T, HasDerivAt Φ (Ω s) s)
    (ha : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => a r / Ω r) (α s) s)
    (hb : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => b r / Ω r) (β s) s)
    (hΩ : ∀ s ∈ Set.Icc 0 T, Ω₀ ≤ Ω s) (hA : ∀ s ∈ Set.Icc 0 T, |a s| + |b s| ≤ A)
    (hA₁ : ∀ s ∈ Set.Icc 0 T, |α s| + |β s| ≤ A₁) (he : ∀ s ∈ Set.Icc 0 T, |e s| ≤ η)
    (ht : t ∈ Set.Icc 0 T) :
    |P t - P 0| ≤ 2 * A / Ω₀ + (A₁ + η) * t
```

Plus `osc_ibp_remainder` (the exact form of `(P − F)′`, enabling iteration) and sanity cases (a constant, Ω constant:
pure `2A/Ω₀`, no secular term; and a = 0). Then a later M4 instance: the near-axis QA trapping theorem with an
interval-certified A_k (k = 2–3). That needs lane C; feasibility ~50% in one cycle.

**Not recommended yet:** the full first-order GC theorem with constants (§2.3), Benettin–Sempio-type exponential μ (no
constants, needs analyticity), and a posteriori KAM for the GC model (long term).
