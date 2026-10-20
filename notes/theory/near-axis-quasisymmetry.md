# Near-axis quasisymmetry for rung M4: a formalization-ready specification

Track: M4 (implementation plan §5), with T7/T8 dependencies. Lane A (discovery). **Nothing in this note is a compiled
Lean theorem.** Status tags follow `README.md`: **published**, **formal asymptotic**, **proved informally**
(sympy-checked where stated), **numerical observation**, **conjectured**.

Scripts: `/tmp/laneA3/{run1,b20,gc,alpha,alpha2}.py` (pyQSC 0.x, sympy). The numbers below were computed with
`qsc.Qsc.from_paper(...)` (Landreman's reference implementation of the Garren–Boozer/Landreman–Sengupta construction).

---

## 1. Summary and recommendation

1. **Representation choice.** There are three distinct objects, and a theorem must say which one it is about.
   - (R1) A *Boozer-coordinate model*: a prescribed function `B(ψ, θ, φ)` plus flux functions `G, I, ι`, with
     the guiding-centre (GC) equations written in those coordinates. It is a closed ODE system. Theorems about it are
     rigorous statements about a reduced model. Its link to a real field that satisfies Maxwell's equations is
     **formal asymptotic** only, up to the order of the expansion.
   - (R2) A *Maxwell-exact 3-D field* `B : ℝ³ → ℝ³` with `∇·B = 0` and `∇×B = 0`, for example an explicit harmonic
     potential. Theorems about it are about a physically admissible vacuum field. However, the QS structure (Boozer
     angles, flux surfaces) is not available exactly and would have to be certified, which is KAM-level work.
   - (R3) A *truncated near-axis potential* `Φ̃` with `|ΔΦ̃| ≤ ε_Δ` on a tube. `∇Φ̃` is curl-free but **not**
     divergence-free, so by itself it is not a magnetic field. It becomes honest only with an elliptic correction
     (§6.3).
2. **Recommended path for M4 (feasible now):**
   - (a) Prove a **guiding-centre Noether theorem with a symmetry defect in the Boozer model R1**. This is the exact
     GC analogue of `noether_orbit_trapped_until`. Its conserved quantity is the helical momentum
     `P = q(Nψ − ψ_p(ψ) + Gρ_∥)`. The derivative identity has been verified in sympy (§4).
   - (b) Instantiate it with an explicit **second-order near-axis QA model** fitted to Landreman–Paul's precise QA,
     with exact rational coefficients and an explicit defect `ε_QS(r) = 2|b₁| r²` (§5).
   - (c) In parallel, build the R2 substrate: Maxwell-exact rational vacuum fields `B = B₀R₀∇φ + ∇h` (§6.2). Make
     no QS claim for these until a certificate exists.
3. **Honest quantitative finding (numerical observation).** At reactor scale (a = 1.7 m, B = 5.7–9 T) the
   worst-case linear-in-time defect bound, fed with the second-order near-axis defect (`ε_QS ≈ 7×10⁻⁴ B₀`), confines
   3.5 MeV alphas for only **≈ 0.2–1.2 ms**. That is far below the slowing-down time (≈ 0.4 s). Reaching 0.4 s would
   need `ε_QS ≲ 10⁻⁶ B₀`, below even the precise-QS fields (≈ 5×10⁻⁵ in amplitude). So the defect theorem gives
   `T ∝ 1/ε_QS` as required, but with a constant that is not useful for alphas. **Closing the 14 Oct alpha
   obstruction needs an averaging lemma** (secular drift ∝ ε² or ∝ ε·ρ_*), proposed in §7 as the next lane-A target.
   Without a pitch-angle restriction, the ε-independent orbit-width term already exceeds the available flux for
   QA at 5.7 T (§5.3). A passing-pitch restriction is needed.

---

## 2. Sources (published)

- D. A. Garren & A. H. Boozer, *Existence of quasihelically symmetric stellarators*, Phys. Fluids B **3** (1991)
  2822; and *Magnetic field strength of toroidal plasma equilibria*, ibid. 2805. Near-axis expansion in Boozer
  coordinates. QS can be imposed at O(r) for any axis. At O(r²) there are more constraints than free functions
  (QS needs `B₂₀` constant). At O(r³) it is generically over-determined (the "Garren–Boozer obstruction").
- M. Landreman & W. Sengupta, *Direct construction of optimized stellarator shapes. Part 1*, J. Plasma Phys. **84**
  (2018) 905840616. First-order theory in cylindrical coordinates, the σ equation.
- M. Landreman, W. Sengupta & G. G. Plunk, *Part 2. Numerical quasisymmetric solutions*, JPP **85** (2019)
  905850103. Examples labelled "r1 section 5.x" below.
- M. Landreman & W. Sengupta, *Constructing stellarators with quasisymmetry to high order*, JPP **85** (2019)
  815850601. Second order, `B₂₀` variation; examples "r2 section 5.x".
- M. Landreman & E. Paul, *Magnetic fields with precise quasisymmetry for plasma confinement*, PRL **128** (2022)
  035001 (arXiv:2108.03711). Aspect ratio 6, ⟨B⟩ = 1 T, ι > 0.4. Symmetry-breaking mode amplitudes in the volume
  are "as small as the ∼50 μT geomagnetic field". pyQSC contains near-axis fits ("precise QA/QH").
- Alpha-loss tracing of the precise fields, scaled to ARIES-CS minor radius and field (5000 alphas, 3.5 MeV, traced
  for 0.2 s): Landreman & Paul 2022; Wiedman, Buller & Landreman, JPP 2024 (QH with coils: no losses from s = 0.5).
  Paul et al., Nucl. Fusion **62** (2022) 126054, explains residual losses through wide orbits even under precise QS.
- J. W. Burby, N. Kallinikos & R. S. MacKay, *Some mathematics for quasi-symmetry*, J. Math. Phys. **61** (2020)
  093503. Coordinate-free QS: a vector field `u` with `u×B = ∇ψ`, `∇·u = 0`, `u·∇|B| = 0`. **Before formalizing the
  R2 route, extract the exact list of conditions and the form of the conserved GC momentum from the paper.**
- G. G. Plunk, M. Landreman & P. Helander, *Part 3. Omnigenity near the magnetic axis*, JPP **85** (2019)
  905850602, and Camacho Mata, Plunk & Jorge, JPP **88** (2022) 905880503. Near-axis quasi-isodynamic (QI)
  fields. QI has **no** continuous symmetry, so there is no Noether invariant. Its confinement route is the bounce
  action J_∥ (T8), not this note's route.
- R. Jorge, W. Sengupta & M. Landreman, *Near-axis expansion of stellarator equilibrium at arbitrary order in the
  distance to the axis*, JPP **86** (2020) 905860106. The vacuum scalar potential in a Mercier/Frenet frame is
  relevant to R3.

---

## 3. First-order construction (formal asymptotic; conventions of pyQSC/LS2018)

Data: a closed smooth magnetic axis `r₀(φ)` with Frenet curvature `κ(φ) > 0`, torsion `τ(φ)`, `n_fp` field periods,
and stellarator symmetry. In the published examples it is given by

`R₀(φ) = Σ rc_k cos(k n_fp φ)`, `Z₀(φ) = Σ zs_k sin(k n_fp φ)` (`zc`, `rs` optional), with φ the cylindrical angle.

Inputs: `B₀`, `η̄`, `σ₀ = σ(0)`, `I₂` (on-axis current; vacuum `I₂ = 0`). Let `ℓ` be the arclength and `L` the
axis length. Then `|G₀|/B₀ = L/(2π)`. The Boozer toroidal angle `φ_B` satisfies `dφ_B/dℓ = 2π/L`.

**Field strength (QS by construction at O(r)):**

    |B|(r, θ, φ_B) = B₀ (1 + r η̄ cos(θ − N φ_B)) + O(r²),   ψ = B₀ r²/2  (toroidal flux / 2π).

Here `N` is set by the axis helicity, the number of rotations of the normal vector per period (QA: N = 0, QH: N ≠ 0).

**σ equation** (Riccati, periodic on the Boozer angle; residual implemented verbatim in `qsc/calculate_r1.py`):

    dσ/dφ_B + ι_N (η̄⁴/κ⁴ + 1 + σ²) − 2 (G₀/B₀)(η̄²/κ²)(I₂/B₀ − s_ψ τ) = 0,   σ(0) = σ₀,

with `ι_N = ι₀ + h·n_fp` (h = axis helicity, `ι₀` the on-axis rotational transform). The unknowns are the periodic
function `σ` and the scalar `ι₀`. First-order surface shape:
`X₁ = (η̄/κ) cos θ`, `Y₁ = s_G s_ψ (κ/η̄)(sin θ + σ cos θ)` in the Frenet frame.

**Published examples, recomputed** (`run1.py`; nφ = 201 for r1/r2; pyQSC sign conventions, so η̄ and ι signs may
differ from the papers):

| Config (pyQSC name) | Axis (`rc`, `zs`; `zc`) | n_fp | η̄ | σ₀ | type | ι₀ | ι_N | L | κ range |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| r1 section 5.1 (LSP19) | rc=[1, 0.045], zs=[0, −0.045] | 3 | −0.9 | 0 | QA | 0.418307 | 0.418307 | 6.3402 | 0.591–1.306 |
| r1 section 5.2 | rc=[1, 0.265], zs=[0, −0.21] | 4 | −2.25 | 0 | QH | 1.931097 | −2.068903 | 8.7245 | 1.887–2.813 |
| r1 section 5.3 | rc=[1, 0.042], zs=[0, −0.042], zc=[0, −0.025] | 3 | −1.1 | −0.6 | QA (no stell. sym.) | 0.311181 | 0.311181 | 6.3416 | 0.644–1.317 |
| r2 section 5.2 (LS19) | rc=[1, .173, .0168, .00101], zs=[0, .159, .0165, .000985] | 2 | 0.632 | 0 | QA | −0.423724 | −0.423724 | 6.6278 | 0.493–1.394 |
| r2 section 5.4 | rc=[1, .17, .01804, .001409, 5.877e-5], zs=[0, .1581, .01820, .001548, 7.772e-5] | 4 | 1.569 | 0 | QH | −1.144137 | 2.855863 | 7.5453 | 0.934–2.575 |
| precise QA (fit to LP22) | 10 coeffs; rc₁ = 0.18401, zs₁ = −0.15811, … | 2 | −0.67839 | 0 | QA | 0.422632 | 0.422632 | 6.6772 | 0.489–1.468 |
| precise QH (fit to LP22) | 9 coeffs; rc₁ = 0.19993, zs₁ = 0.17888, … | 4 | −1.50028 | 0 | QH | −1.244876 | 2.755124 | 7.9846 | 0.929–2.855 |

Values of ι to six digits are numerical solutions of the σ equation (Newton on a spectral grid). They are **not**
certified. A certified ι₀ would require validated Riccati-BVP enclosures (lane C, radii polynomial on a periodic
Riccati ODE; this is a good small M3-type exercise).

**Second order** (LS19). `|B| = B₀ + r B₁ cos χ + r²(B₂₀(φ_B) + B₂c cos 2χ + B₂s sin 2χ) + O(r³)` with χ = θ − Nφ_B.
In vacuum, `B₂₀(φ)` is determined by the axis, η̄ and `B₂c, B₂s`. QS at O(r²) requires `B₂₀` = const, which is
generically impossible (Garren–Boozer). The residual `B₂₀(φ) − ⟨B₂₀⟩` is the leading **symmetry defect**:

| Config | ⟨B₂₀⟩ | max B₂₀ − min B₂₀ | max\|dB₂₀/dφ_B\| | r_singularity |
| --- | --- | --- | --- | --- |
| r2 section 5.1 | 0.16212 | 0.37460 | 0.92247 | 0.2256 |
| r2 section 5.2 | 0.36550 | 0.03130 | 0.17178 | 0.4095 |
| r2 section 5.4 | 1.31258 | 0.11820 | 0.63481 | 0.3583 |
| precise QA | −0.22200 | 0.01465 | 0.02370 | 0.4116 |
| precise QH | 1.15369 | 0.12163 | 0.93290 | 0.3472 |

(Normalized units: R ≈ 1 m, B₀ ≈ 1 T.)

---

## 4. Guiding-centre Noether theorem in the Boozer model (proved informally; sympy-checked)

**Model (R1, vacuum).** Coordinates `z = (ψ, θ, φ, ρ)` with `ρ = ρ_∥ = m v_∥/(qB)`. Vacuum Boozer covariant form
`B = G∇φ` (so `I = K = 0`, G constant), and poloidal flux `ψ_p(ψ)` with `ψ_p′ = ι`. The phase-space Lagrangian
(Littlejohn, in Boozer variables; gyrophase ignored, μ constant) is

    L = qψ θ̇ + q(Gρ − ψ_p(ψ)) φ̇ − H,   H = q²ρ²B(ψ,θ,φ)²/(2m) + μ B(ψ,θ,φ).

Since `det ω = G² q⁴ ≠ 0`, the Euler–Lagrange equations are the explicit ODE (`gc.py` output):

    ψ̇ = −(mμ + q²ρ²B) ∂_θB / (m q)
    θ̇ = (μ/q) ∂_ψB + (qρ²B/m) ∂_ψB + q ρ B² ι /(G m)
    φ̇ = q ρ B² /(G m)
    ρ̇ = −[(mμ + q²ρ²B)(∂_φB + ι ∂_θB)] /(G m q)

**Identity.** For `ξ = ∂_φ + N∂_θ` and `P := q(Nψ − ψ_p(ψ) + Gρ)`,

    dP/dt = −(q²ρ²B/m + μ) · ξB = −((m v_∥² + μB)/B) · ξB,      dH/dt = 0.

Both identities were checked symbolically for generic `B(ψ,θ,φ)` and `ψ_p` (`gc.py`: `dP/dt − target = 0`,
`dH/dt = 0`). Since `m v_∥² + μB ≤ 2H`, we get **`|dP/dt| ≤ (2H/B_min) · sup|ξB|`**.

**Trapping theorem (target statement, analogue of `noether_orbit_trapped_until`).** Hypotheses:
`m > 0`, `q ≠ 0`, `G ≠ 0`. On the region `{ψ ≤ c}` assume `B ≥ B_min > 0`, `|ξB| ≤ ε` (`ε ≥ 0`), and
`N − ψ_p′(ψ) ≥ ι_min > 0` (or ≤ −ι_min) on `[0, c]`. Let `ρ_max(H) = √(2mH)/(|q| B_min)`, or a refined pitch-set
bound `Δρ` (below). If

    ι_min (c′ − ψ(0)) ≥ |G| Δρ + (2H/(|q| B_min)) ε T,   c′ < c,

then `ψ(t) ≤ c′` for all `t ∈ [0, T]`. With `ε = 0` this holds for all `t ≥ 0`, which is exact QS all-time
confinement in the model. Proof: the first-crossing argument (`trapped_until`), `invariant_drift` on `P`,
monotonicity of `ψ ↦ Nψ − ψ_p(ψ)`, and `|ρ(t) − ρ(0)| ≤ Δρ`.

Correspondence with the full-orbit theorem: `‖K‖`-term ↔ `|G|Δρ/ι_min` (orbit width) and
`δ‖v₀‖T` ↔ `(2H/(|q|B_min)) εT/ι_min`.

**Pitch-set bounds for Δρ** (proved informally, elementary). Let `δ_B = ΔB/B_min`, where ΔB is the oscillation of B
on the region. Energy gives `|v_∥(t)² − v_∥(0)²| ≤ v² δ_B`.
- Any pitch: `|Δv_∥| ≤ 2v√δ_B`.
- Passing set `|v_∥(0)| ≥ λv` with `λ² > δ_B`: `v_∥` keeps its sign and `|Δv_∥| ≤ v δ_B /(2√(λ² − δ_B))`.

Then `Δρ ≤ (m/|q|)(|Δv_∥|/B_min + v ΔB/B_min²)`.

**Axis regularity.** `(ψ, θ)` are singular at the axis (`∂_ψ` of `r ∝ √ψ` blows up). Lean statements should use
`x = r cos χ`, `y = r sin χ` (χ = θ − Nφ). Then `qψ dθ = (qB₀/2)(x dy − y dx) + N(…)dφ` and the second-order model
`B` is a **polynomial** in `(x, y)`, which avoids `Real.sqrt` at ψ = 0. Alternatively, state the theorem on
`{ψ ≥ ψ_min > 0}` with trajectories supplied, as `noether_orbit_trapped_until` does.

---

## 5. Explicit model instance and the defect bound

### 5.1 The model (definition, R1)

Precise-QA fit (pyQSC "precise QA", normalized units, QA so N = 0, n_fp = 2):
`B₀ = 1.006541`, `η̄ = −0.678391`, `B₂c = 0.268593`, `ι₀ = 0.422632`, `G₀ = 1.069660`.
`B₂₀(φ_B)` Fourier fit on the Boozer angle (`b20.py`) is `b₀ + Σ b_k cos(2kφ)`, with `b₀ = −0.222004` and
`b₁ = −0.006938`. Higher `|b_k| ≲ 6×10⁻⁴` are at the noise level of the 99-point fit.

Lean-ready **truncated model** (rational coefficients, e.g. `η̄ = −339/500`, `B₂c = 67/250`, `b₀ = −111/500`,
`b₁ = −7/1000`, `ι₀ = 211/500`, `G = 107/100`, `B₀ = 1`):

    B(x, y, φ) = B₀ (1 + η̄ x) + (x² + y²) (b₀ + b₁ cos 2φ) + B₂c (x² − y²).

- **Exact defect:** `ξB = ∂_φB|_{x,y} = −2 b₁ (x² + y²) sin 2φ`, so `sup_{r ≤ r_c} |ξB| = 2|b₁| r_c² =: ε_QS(r_c)`.
  With `b₁ = −7/1000` this gives `ε_QS(r) = 0.014 r²`. (Over the full pyQSC B₂₀, `max|dB₂₀/dφ| = 0.0237`, so
  `ε_QS ≈ 0.0237 r²`.)
- **Field range** on `r ≤ r_c`: `B_min ≥ B₀(1 − |η̄| r_c) − r_c²(|b₀| + |b₁| + |B₂c|)` and
  `ΔB ≤ 2B₀|η̄|r_c + r_c²(2|B₂c| + 2|b₁|)`. These are exact polynomial bounds, checkable by `norm_num`/`nlinarith`.
- **Status of the link to physics:** this `B` agrees with the `|B|` of a real vacuum field near the precise-QA axis
  only to the order of the expansion (**formal asymptotic**). The O(r³) remainder has no rigorous bound in the
  literature, and convergence of the near-axis series is open. The theorem is therefore about the model. This
  must be stated in its docstring.

### 5.2 Where ε_QS enters

- **GC Noether (§4):** `T_conf = [ι_min(c′ − ψ₀) − |G|Δρ] · |q|B_min /(2H ε_QS(r_c))`, with `ψ = B₀r²/2`.
- **Existing full-orbit theorem `noether_orbit_trapped_until`:** this is *not* directly applicable. Its `K` must be
  a Euclidean Killing field, and a toroidal QS field has none. The QS symmetry is `∂_φ` in Boozer coordinates
  (or `u` in BKM form), not an isometry. Only the helically symmetric straight model (`Design.HelicalStellarator`)
  fits it. The GC theorem above is the replacement. Its proof skeleton (`invariant_drift`, `trapped_until`) is
  reused verbatim.

### 5.3 Numbers for 3.5 MeV alphas (numerical observation, `alpha.py`, `alpha2.py`)

Scale precise QA to a = 1.7 m (aspect ratio 6, so R̄ ≈ 10.2 m) and B₀ = 5.7 T. Then `G = 58.1 T·m`, `ι₀ = 0.4226`,
`η̄ = 0.0707 m⁻¹`, `max|dB₂₀/dφ| = 1.457×10⁻³ T/m²` and `ε_QS(a) = 4.2×10⁻³ T = 7.4×10⁻⁴ B₀`. For the alpha,
`mv/q = 0.2694 T·m` and `v = 1.30×10⁷ m/s`.

| Field, pitch set, start → limit | orbit term `|G|Δρ/ι₀` (T m²) | available `ψ_c − ψ₀` | T_conf |
| --- | --- | --- | --- |
| 5.7 T, any pitch, 0.5a → a | 10.45 | 6.18 | **none** (orbit term too large) |
| 5.7 T, \|v_∥/v\| ≥ 0.9, 0.25a → a | 3.81 | 7.72 | 0.55 ms |
| 5.7 T, \|v_∥/v\| ≥ 0.9, 0.5a → a | 3.81 | 6.18 | 0.33 ms |
| 9 T, any pitch, 0.25a → a | 10.45 | 12.19 | 0.25 ms |
| 9 T, \|v_∥/v\| ≥ 0.9, 0.25a → a | 3.81 | 12.19 | 1.18 ms |

Slowing-down time (NRL formula): `τ_s ≈ 0.37 s · (T_e/10 keV)^{3/2}/(n_e/10²⁰)`, which is ≈ 0.45 s at 15 keV and
1.5×10²⁰ m⁻³. **ε_QS needed for 0.4 s: ≈ 4×10⁻⁷ to 2×10⁻⁶ B₀.** Even the Landreman–Paul fields (mode amplitudes
≈ 5×10⁻⁵ B₀, so `|ξB| ≳ 2·n_fp·5×10⁻⁵`) give only a few ms. The precise-QH near-axis model is not usable at
r = a (`ΔB/B_min > 1`, outside the expansion's validity), so QH cases need r_c ≲ 0.5a.

**Interpretation.** The linear bound treats `ξB` as a worst-case constant-sign forcing. In the model, for passing
particles, `ξB = −2b₁ r² sin 2φ` is an oscillating function of a monotone angle (`φ̇ = qρB²/(Gm)` has a fixed sign).
So the secular drift of P actually cancels at leading order. This is the gap to close next.

---

## 6. Honest paths to a Maxwell-exact statement

### 6.1 Why the Boozer model is acceptable as M4's first step
It is a well-defined Hamiltonian reduced model, and the theorem is exact for it. The physics gap (does a real
vacuum field have this |B| in Boozer coordinates?) is the same gap as the near-axis expansion's, and the docstring
must state it.

### 6.2 Exact rational vacuum fields (recommended R2 substrate)
`B = B₀R₀ (−y, x, 0)/(x² + y²) + ∇h`, with h a harmonic polynomial. Examples are `h = ε(x² − y²)z`,
`h = ε Re((x+iy)^n) z`, or solid harmonics `r^l Y_l^m`, or Dommaschk potentials (W. Dommaschk, Comput. Phys.
Commun. **40** (1986) 203: finite sums in R^k, ln R, z^j; exactly harmonic). Then `∇·B = 0` and `∇×B = 0` on
`{x² + y² > 0}` hold by **polynomial/rational identities** (`field_simp; ring`), so Maxwell holds exactly. QS
properties of such a field (closed axis, ι, defect) are numerical until certified. The certificate would be a
BKM-style approximate symmetry `(u, ψ_h)` with `|u×B − ∇ψ_h| ≤ δ₁` and `|u·∇|B|| ≤ δ₂` on a tube, by interval
arithmetic, plus a Cartesian GC Noether theorem with these defects. That is M5-level work.

### 6.3 Truncated potential plus elliptic correction (R3, conditional)
Let `|ΔΦ̃| ≤ ε_Δ` on a tube Ω of radius `ρ_Ω`, and let Φ be harmonic with `Φ = Φ̃` on ∂Ω. Existence of Φ is a
Dirichlet-problem hypothesis, since Mathlib lacks it. Then:
- Comparison with `ε_Δ|x − c|²/6` (the weak maximum principle already in `Kernel/Vacuum` and `Theory/Fields/Subharmonic`) gives
  `|Φ − Φ̃| ≤ ε_Δ ρ_Ω²/6` (proved informally).
- The interior gradient estimate for `Δw = f` on a ball of radius d (Gilbarg–Trudinger Thm 3.9) gives
  `|∇Φ − ∇Φ̃|(x) ≤ (3/d) ε_Δ ρ_Ω²/6 + (d/2) ε_Δ` at distance d from ∂Ω. This yields an exact vacuum field within an
  explicit distance of `∇Φ̃`.

**Caveat:** Φ is *a* vacuum field with those boundary values, not the coil field. Transferring orbit bounds from
∇Φ̃ to ∇Φ also needs a Grönwall orbit-perturbation estimate. This path is honest but has three extra obligations,
so it is not recommended for the first M4 deliverable.

---

## 7. Proposed Lean targets (in order)

1. `Theory/Kinetic/BoozerGuidingCentre.lean`:
   - `BoozerGCOrbit` (the four ODEs above as `HasDerivAt` hypotheses, vacuum `I = 0`).
   - `boozerGC_energy_conserved`.
   - `helicalMomentum_hasDerivAt` (`dP/dt = −(q²ρ²B/m + μ)ξB`; a pure `HasDerivAt` computation).
   - `helicalMomentum_drift_le` (`|ΔP| ≤ (2H/B_min) ε t`).
   - `boozerGC_trapped_until` and `boozerGC_trapped` (ε = 0, all time).
   - Sanity cases: (a) degenerate `B` constant gives P exactly conserved and ψ constant; (b) tokamak-like
     `B = B₀(1 + η̄x)` gives exact QS; (c) a non-vacuity witness (an explicit circular passing orbit in the ε = 0 model).
2. `Design/NearAxisQA.lean`: the polynomial model of §5.1 with rational coefficients. Prove `ξB` exactly,
   `ε_QS(r) = 2|b₁| r²`, and the B_min/ΔB bounds. Then the M4 theorem: "every 3.5 MeV alpha GC orbit in the model
   with `|v_∥/v| ≥ 0.9` starting at `r ≤ a/4` stays in `r ≤ a` for `t ≤ T*`", with an explicit `T*` (≈ 0.5 ms at
   5.7 T). Label it honestly as a model result with a sub-ms time.
3. Lane A, next: **averaging lemma**. If along an orbit `ξB = d/dt F + R`, with `|F| ≤ ε/ω_min` (from
   `φ̇ ≥ ω_min > 0` for passing orbits) and `|R| ≤ C ε²` (or `C ε ρ_*`), then `|ΔP| ≤ 2ε/ω_min + Cε²t`. Hence
   `T ∝ 1/ε²`. For the §5.1 model, `F = (b₁ r²/φ̇) cos 2φ` up to the variation of r and φ̇ along the orbit. Trapped
   particles need the bounce-averaged version, which links to T8 (J_∥, omnigeneity).
4. `Theory/Fields/ToroidalHarmonic.lean`: the exact rational vacuum family of §6.2, with div/curl identities. No QS
   claim.

---

## 8. Counterexample attempts and caveats

- **Pure first-order model (`b₁ = 0`):** ε = 0 and all-time confinement in the model. This is not evidence about
  real fields (Garren–Boozer: O(r²)/O(r³) obstruction).
- **QH at r = a:** the near-axis series is outside its validity (`ΔB/B_min > 1`). Do not instantiate QH beyond
  `r_c ≈ 0.5a` without a remainder bound.
- **Sign conventions:** pyQSC's η̄ and ι signs differ from LSP19's printed values (e.g. LSP19 §5.1 prints η̄ = 0.9,
  pyQSC uses −0.9). Lean data should cite the pyQSC call used.
- **Finite β:** `I ≠ 0` and `K ≠ 0` add `ρI θ̇` and `ρK ψ̇` terms. P becomes `q(Nψ − ψ_p) + qρ(G + NI)`, which
  requires K to be QS as well. Not covered here.
