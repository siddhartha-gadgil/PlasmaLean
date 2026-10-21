# Trapped (banana) 3.5 MeV alphas: status

Phase 12 note, 21 October 2026. Companion to [near-qa-trapped-particles.md](near-qa-trapped-particles.md) and
[robust-alpha-confinement.md](robust-alpha-confinement.md) §3. Everything below is about **models**: the vacuum Boozer
guiding-centre equations (`Kinetic.BoozerGuidingCentre`) in the reactor near-axis QA family (`reactorQA`, with
`ε_QS(a) = 2.49×10⁻³ T`, and `exactQA = qaField 0`). Orbits are supplied, not constructed. Pitch window: tip field
`E/μ ∈ [5.4, 5.5] T`, i.e. moderately deep bananas, away from the trapped–passing boundary.

## 1. Compiled results

New modules (not yet imported in `PlasmaLean.lean`):
- `PlasmaLean/Theory/Kinetic/BounceShear.lean`
- `PlasmaLean/Design/NearAxisQATrappedReanchor.lean`

Both use standard axioms only and build with zero warnings.

| Declaration | Statement | Regime |
| --- | --- | --- |
| `exactQA_trapped_confined_forever` | **All time.** Exact QA: tips with `ψ₀ ∈ [4.75, 5.79] T m²` stay in `[ψ_lo, ψ_a]` with `\|ρ\| ≤ 1.77 cm` for every `t ≥ 0`. | Exact QS, any `t`. This repackages `exactQA_band`; `boozerGC_trapped` already covered trapped particles, because it only uses `\|Δρ\| ≤ ρ_max`. |
| `reactorQA_trapped_confined_until` | **Unconditional, near QA.** Tips with `ψ₀ ≤ 5` stay at `ψ ≤ 8.23 < ψ_a` for `t ≤ 1.8×10⁻⁴ s`. | About 3 bounce periods (simulated `P ≈ 6.5×10⁻⁵ s`). |
| `reactorQA_trapped_band_until` | Two-sided band `[ψ_lo, ψ_a]` for `ψ₀ ∈ [5.2, 5.3]` and `t ≤ 10⁻⁴ s`. | |
| `abs_sum_shear_le`, `abs_sum_shear_cos_le` | Abel summation with **varying** phase increments: `\|Σ_{k≤n} c_k sin x_k\| ≤ M + n(γ + M(e+σ))/2`. | Pure analysis. Sharp: `abs_sum_shear_resonant`. |
| `reanchored_drift_le`, `reanchored_band` | Re-anchored bounce map: `\|y_{n+1} − y_0\| ≤ 2M + (n+1)R + n(γ + M(e+σ))`. Discrete first-exit argument keeps anchors in a window. | Pure analysis. |
| `reference_kick_decomp` | Each fresh exact-QA reference bounce in the start window has `Δ ∈ [0.7, 2.6]` and `\|sin Δ\| ≥ 1/2`. Its kick is exactly `C sin 2φ₀ + S cos 2φ₀` with `\|C/sin Δ\|, \|S/sin Δ\| ≤ 2∫₀ᴾ\|g\|`. | Exact QA, certified precession. |
| `reactorQA_trapped_reanchored` | **Conditional N-bounce bound.** If, while the anchors are in `[4.75, 5.79]`, the one-bounce remainders are `≤ R` (kick) and `≤ e` (phase), and the shears are `≤ σ` (precession) and `≤ γ` (amplitude), then all `N` anchors stay in the window. This holds provided `2M + N(R+γ+M(e+σ)) + 2M + R ≤ gap`. | `reactorQA`; `R, e, σ, γ` are hypotheses. |
| `reanchored_budget_simulated` | With the RK4 constants of §2, the gap closes for `N = 300` bounces, about `0.02 s`. | Arithmetic only. |

### Why re-anchoring settles the phase-shear problem

The phase-shear objection to a single global reference was that the bounce phase drifts with `ψ₀`, so one reference
cannot stay close for many bounces. Re-anchoring removes this:
- every error is incurred over **one** bounce;
- the shear appears only as the per-step variation `σ` of `Δ` and `γ` of `C/sin Δ, S/sin Δ` between consecutive
  anchors;
- this enters additively as `M(e+σ) + γ` per bounce, the Chirikov/GWB-type term.

## 2. Numbers (untrusted oracle)

The oracle is `scripts/trapped_reanchor/reanchor_sim.py` (pure Python RK4, `h = 2×10⁻⁸ s`, 60 bounces per start). In
the table, `M` is in T m², and `R` and `γ` are in ψ units (T m²).

| `ψ₀`, `B_t` | `P` (s) | `Δ` | `R` | `e` | `σ` | `γ` | `M` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 5.27, 5.45 | 6.50e-5 | 2.08 | 1.7e-4 | 0.0138 | 0.0064 | 5.5e-4 | 0.0199 |
| 4.85, 5.42 | 6.55e-5 | 2.25 | 2.1e-4 | 0.0141 | 0.0075 | 7.0e-4 | 0.0228 |
| 5.70, 5.48 | 6.45e-5 | 1.93 | 1.6e-4 | 0.0125 | 0.0043 | 5.4e-4 | 0.0167 |

What these numbers give:
- **Error per bounce.** `R + γ + M(e+σ) ≈ 1.4×10⁻³ T m²`, against a window gap of 0.52 T m² from `ψ₀ = 5.27`. This
  gives `N ≈ 300` bounces, about **0.02 s**: roughly 110 times the unconditional 0.18 ms, and 1/20 of the 0.4 s
  slowing-down time.
- **Actual excursion.** The tip excursion over 60 bounces is only about 0.02 T m², a bounded oscillation. So the
  linear `N·(…)` growth is the price of worst-case summation.

## 3. What remains (precise)

1. **One-bounce remainders `R` and `e`.** A Lipschitz–Grönwall comparison is hopeless here.
   - The reduced exact-QA field has a sampled Lipschitz constant `K ≈ 4.5×10⁸ s⁻¹` in the `(ψ, θ, ρ)` sup norm, so
     `e^{KP}` with `P ≈ 6.5×10⁻⁵ s` is about `e^{29000}`.
   - Even in a rescaled norm the bounce rotation gives `KP ≳ 2π`.
   - Viable routes:
     - (a) compare **conserved quantities**: `E` is exact, `P_φ` drifts at `O(ε)`, and the exact-QA orbit is an
       explicit algebraic function of `(x; ψ₀, B_t)` (`NearAxisQATrappedCells.OrbitRel`). This bounds the near-QA
       state on the exact-QA banana without exponentials, using the same `x`-cells as the precession certificate.
     - (b) a validated enclosure of the variational equation over one bounce.
2. **Shears `σ` and `γ`.** These are properties of the exact-QA field alone: Lipschitz dependence of `Δ_b` and of the
   harmonic coefficients on the anchor `(ψ₀, B_t)`. They are a cell-certificate target, the derivative of the existing
   precession cells.
3. **Bounce-time enclosure.** The proved `P ≤ 1.6 ms` (against `6.5×10⁻⁵ s` simulated) makes even the worst-case
   amplitude `M ≤ 2P sup|g|/(qι₀) ≈ 12.8 T m²` exceed the window (`crude_amplitude_exceeds_window`). A validated
   bounce-time quadrature is a prerequisite for any proved instance.
4. **Existence of re-anchored references.** Exact-QA orbits from a given tip state are supplied, not constructed.
   - The fresh reference must use `μ_k = E/B_exact(tip)`, which is slightly different from `μ`, because
     `B_near ≠ B_exact` at the tip.
   - Picard–Lindelöf for the `C¹` field `vred` on `redBox` would remove this hypothesis.

## 4. Option (a) of the brief (exact stellarator field, Littlejohn, μ > 0): not pursued

In `field(1/4)`, trapped orbits are not field lines of any fixed field (robust note §3). The only cheap bounds are:
- energy (`|B(X)| ≤ E/μ`), which is not a spatial bound there;
- a drift-speed Grönwall bound giving `T ~ 10⁻⁵ s`.

That is physically empty, and it does not use the field's invariant tori in any essential way. The exact-QA result
plus the re-anchored scheme above is strictly more informative.

## 5. Follow-up: tight bounce period, constructed references, shears (21 October 2026)

New modules (not yet imported in `PlasmaLean.lean`; standard axioms only, zero warnings):
- `PlasmaLean/Design/NearAxisQATrappedTimeCells.lean`: cell checker for the bounce time and the amplitude integral.
- `PlasmaLean/Design/NearAxisQATrappedTimeRows.lean`: the 16 kernel checks of a `4 × 4` grid of the window.
- `PlasmaLean/Design/NearAxisQATrappedBouncePeriod.lean`: period and amplitude theorems, generic legs.
- `PlasmaLean/Design/NearAxisQATrappedReference.lean`: existence and uniqueness of the reference orbits.

### 5.1 Item 3: validated bounce period (done)

| Declaration | Statement |
| --- | --- |
| `exactQA_bounce_period` | Every `Setup` orbit (start window, `T ≥ 1.6 ms`): the bounce closes at `P ≤ 83 μs`, with `Δφ_b ∈ [0.7, 2.6]` and `∫₀ᴾ A·(2ψ/B₀) dt ≤ 58`. Here `A = μ/q + qρ²B/m`. RK4: `P = 6.36–6.66 × 10⁻⁵ s`, `J = 38.8–46.5`. |
| `time_cert` | Cell certificate on `[4.75, 5.875] × [5.4, 5.5]`: uniform `4 × 4` grid, `decide +kernel`, about 36 s in total. |
| `inner_leg_gen`, `outer_leg_gen` | The leg decomposition of `inner_leg` / `outer_leg` for an arbitrary continuous integrand `F`. Hypotheses: `F ≤ K_i A\|∂_θB\|` on flank cells and `F ≤ K_b\|θ̇\|` at the bottom. |
| `Afac_eq_AmR` | `A = 10⁶ · (7/4)(2B_t − B)/(B_t B)` along the orbit, by energy conservation. |
| `bottom_thetaDot` | `Ω = \|θ̇\| · ratR` at the bottom. |

How the time integral is handled: there are no singular endpoints.
- On the flanks, `dt = dx/(A|∂_θB|)` with `|∂_θB| ≥ sin δ · (…) > 0`.
- At the bottom, `dt = ratR dθ/(A(−∂_ψB))` with `θ̇` bounded away from zero.

The amplitude integral `∫ A·w dt` is even simpler: `A` cancels on the flanks.

**Amplitude constant** (`reference_kick_tight`, `tight_amplitude_le`):
- In kick units, `|C/sin Δ|, |S/sin Δ| ≤ 2∫₀ᴾ|g| ≤ 4|b₁| q · 58`.
- In flux units, `M = 4|b₁| · 58/ι₀ ≤ 0.2364 T m²` for `reactorQA`. The crude period gave `12.8`.

**It does not fit the window** (`reanchored_gap_forces_small_M`, `tight_amplitude_too_large`, `certified_constants_fail`):
- The gap of `reactorQA_trapped_reanchored` needs `4M + R ≤ min(ψ₀ − 4.75, 5.79 − ψ₀) ≤ 0.52`, i.e. `M ≤ 0.13`.
- With `M = 0.2364` the hypothesis fails for every `N`, `R`, `e`, `σ`, `γ`.
- Worse, the exact value of `2∫|g|/(qι₀)` is `0.158–0.189` (RK4), already above `0.13`. So no sharper period or quadrature can rescue a bound of the form `M = 2∫|g|/(qι₀)`.

What is needed is an enclosure of the **oscillatory** integrals `C = ∫ g cos 2(φ − φ₀)`, `S = ∫ g sin 2(φ − φ₀)` themselves (RK4: `|C/sin Δ| ≤ 0.023`). This requires tracking `φ(t) − φ₀` along the banana:
- On the flank cells, `dφ/dx = qρB²/(G m A |∂_θB|)`.
- At the bottom, `2φ` turns by about `5.7` rad during each crossing, so θ-resolved bottom cells are needed (the present bottom uses a single ratio per leg).

### 5.2 Item 4: reference orbits constructed (done)

| Declaration | Statement |
| --- | --- |
| `exactQA_reference_exists` | For every tip state `(ψ₀, θ₀, φ₀)` with `ψ₀ ∈ [4.75, 5.79]`, `θ₀ ∈ (0, π/2)`, `μ B_exact(ψ₀, θ₀) = E` and `μ` in the pitch window, there is an **all-time** `BoozerGCOrbit` of `exactQA` through it with `ρ(0) = 0`. It satisfies `Setup μ T` for every `T` and stays in `ψ ∈ (ψ_lo, ψ_a)`, `\|θ\| < π/2` for all `t ∈ ℝ`. |
| `exactQA_reference_unique` | Two `Setup μ T` orbits with the same initial state agree on `[0, T]`. |
| `exactQA_reference_existsUnique` | The combination. |

Method: `ODEGlobal.existsUnique_global` (`FieldLineExistence`), applied to `vred μ` on `U = {ψ > 0}` and `K = redBox`. The invariant set is `refSet = {E_red = E, ρ − kinv ψ = −kinv ψ₀, ψ ∈ [ψ_lo, ψ_a], |θ| ≤ π/2}`.
- Conservation of `E_red` and `ρ − kinv ψ` is checked directly from `vred`.
- Strictness on the level set: `|ρ| ≤ ρ_max` and `μB ≤ E < μB(±π/2)`.
- Then a first-exit argument; backward time follows from the reflection symmetry `vred(ψ, −θ, ρ) = (−v₁, v₂, −v₃)`.

So the fresh reference with `μ_k = E/B_exact(tip_k)` exists whenever the tip lies in the start window and the pitch window. The `Setup` hypothesis of every exact-QA theorem is discharged.

### 5.3 Item 2: shears (partial)

Proved, but only crude:
- `precession_shear_crude`: `|Δ' − Δ| ≤ 1.9` for any two anchors.
- `amplitude_shear_crude`: `γ ≤ 2M ≤ 0.473`.

A derivative (Lipschitz) cell cover for `Δφ_b(ψ₀, B_t)` and `C/sin Δ` was **not** built. Two-sided enclosures of `Δφ_b` from the present cells have a floor of width `0.17–0.24` rad even on a single index box (untrusted evaluation, with lower flank sums over fully-flank cells). The floor comes from the single bottom ratio `[m_b, M_b]`. So any oscillation-based `σ` is at least that large.

This is moot until `M` is fixed: with the certified `M` the gap fails before `σ, γ` enter.

### 5.4 Exact remaining requirement

From `reactorQA_trapped_reanchored`, `N` bounces from `ψ₀` require

`4M + R + N (R + γ + M (e + σ)) ≤ min(ψ₀ − 4.75, 5.79 − ψ₀)`, with `R, e, σ, γ, M` per bounce.

1. **Oscillatory amplitude `M`.** Needed: `M ≤ (0.52 − R)/4 < 0.13`. Proved: `M ≤ 0.236`, which fails for every `R, e`.
2. **Shears `σ, γ`.** With the simulated `M = 0.023` and `σ = 0.0076`, `γ = 7 × 10⁻⁴`, the requirement on the one-bounce remainders from `ψ₀ = 5.27` is
   `0.092 + R + N (R + 7×10⁻⁴ + 0.023 (e + 0.0076)) ≤ 0.52`.
   For example, `N = 300` needs `301 R + 6.9 e ≤ 0.165`. The RK4 values `R ≈ 2×10⁻⁴`, `e ≈ 0.014` give `0.157`.
   In time, `N = 300` is about `0.02 s` at the simulated period. The proved `P ≤ 83 μs` only caps this at `0.025 s`; converting bounces into a guaranteed time would need a *lower* period bound, which is not proved.
3. **Remainders `R, e`.** Still unproved, as in §3 item 1.

## 6. Phase 12c: the oscillatory kick enclosed (21 October 2026)

New modules (not imported in `PlasmaLean.lean`; standard axioms only; zero warnings):
- `PlasmaLean/Theory/Kinetic/BounceClamp.lean`: signed cell sums (exact per-cell weights).
- `PlasmaLean/Design/NearAxisQATrappedOscTrig.lean`: fixed-point `cos`/`sin` enclosures.
- `PlasmaLean/Design/NearAxisQATrappedOscCells.lean`: the cell checker and its soundness.
- `PlasmaLean/Design/NearAxisQATrappedOscLegs.lean`: rate identities, generic pieces, the two legs.
- `PlasmaLean/Design/NearAxisQATrappedOscKick.lean`: assembly, conditional on a cover.
- `PlasmaLean/Design/NearAxisQATrappedOscRows01.lean`–`Rows16.lean`: the kernel checks of the 126 leaves.
- `PlasmaLean/Design/NearAxisQATrappedOscCover.lean`: the cover and the final theorems.

Untrusted scripts in `scripts/trapped_reanchor/`:
- `osc_cells.py`: float prototype, used to design the cells;
- `osc_mirror.py`: a bit-exact integer mirror of the Lean checker (checked against the kernel on
  `CTI_tab` and on a full box);
- `osc_gen.py`: the adaptive cover, the oracle data and the generated Lean files.

### 6.1 Item 1: the oscillatory amplitude is certified (done)

| Declaration | Statement |
| --- | --- |
| `exactQA_kick_osc` | Every reference bounce of the start window closes at `P ∈ [59, 72] μs`, with `Δ = φ(P) − φ(0) ∈ [1.70, 2.49]` and `sin Δ ≥ 3/5`. The normalised kick integrals `Ĉ = ∫₀ᴾ A w cos 2(φ − φ₀)`, `Ŝ = ∫₀ᴾ A w sin 2(φ − φ₀)` satisfy `√(Ĉ² + Ŝ²) ≤ 40 sin Δ`. RK4: `≈ 11 sin Δ`. |
| `reference_kick_osc` | For `reactorQA` (`b₁ = −4.3×10⁻⁴`): the reference kick is `C sin 2φ₀ + S cos 2φ₀`, and in flux units `√(C² + S²)/(q ι₀ sin Δ) ≤ M_eff = 0.0816 T m²`. Hence `\|C/(q ι₀ sin Δ)\|, \|S/(q ι₀ sin Δ)\| ≤ 0.0816`. |
| `exactQA_kick_osc_of_cover`, `reference_kick_osc_of_cover` | The same statements for any `OscCover Kn Pmin Pmax DlS DhS 0 120 0 128`. |
| `inner_leg_osc`, `outer_leg_osc` | The leg checks enclose the leg integrals of `A w cos`, `A w sin`, of `Ω` and of `1`. |
| `osc_cover` | 126 leaves on the `PBI × TBI` index grid; `ψ₀ ∈ [4.75, 5.8047]`, `B_t ∈ [5.4, 5.5]`. |

`M_eff = 0.0816` compares as follows:
- previously certified: `0.2364`;
- simulated: `0.023`;
- needed for the window: `< 0.13`.

So the amplitude obstruction of §5.1 is removed: the certified data `(C k, S k, Δ k, dC k, dS k)`
of every fresh exact-QA reference are admissible for `reactorQA_trapped_reanchored` with
`M = 0.0816`.

**Method.**
- **Rates.** Every rate is `A` times an explicit function of the leg coordinate `x` and `c = cos θ`:
  - `ẋ = A |∂_θB|`, `Ω = A n`, `|φ̇| = A K/ι₀`;
  - `θ̇ = −A (n + K)` (inner leg) or `A (K − n)` (outer leg), with `K = 2λ B_t x B³/(2B_t − B)`;
  - so `A` cancels from all ratios (`Afac_mul_KR`, `phiDot_eq`, `thetaDot_eq`).
- **Cells.**
  - Flanks (`|θ| ≥ 3/5`): `x`-cells of width `1/40`.
  - Bottom: `θ`-cells of width `1/40`. The leg coordinate of a bottom cell is the hull of the
    `x`-cells whose cosine enclosure meets the cell's cosine range.
  - The bottom densities use `|θ̇|/A = K ± n` directly. This avoids the `n`-dependency blow-up of
    the old `ratR` form.
- **Phase.** `Φ = 2(φ − φ₀)` is never integrated over the large streaming swings.
  - On a flank it is accumulated from the nearer turning point. All cells between are full, so
    the partial-cell losses vanish.
  - On the bottom it is `(2/ι₀)(θ − θ₀ + ∫₀ᵗ Ω)`, with `θ` known to the cell width (`prec_eq`).
  - `θ₀` is enclosed once per box from the tip cosine, checked with `cosSinC`. At the lower tip
    `θ = −θ₀`.
- **Signed integrands.** `integral_le_clamp_sum` integrates `Ω ≤ U_i ẋ` exactly cell by cell, for
  `U_i` of either sign.
- **Trigonometry.** `cosSinC` is the centred form around the midpoint (quadrant reduction, Taylor
  at `y/16`, four doublings). Its width is close to the true range.
- **Kernel budget.** The box check is split into the two legs, with literal interfaces from the
  exact mirror. This keeps every kernel process at `≤ 4.6 GB` and about `5.5 s` per leg.
- **Resolution floor.** Even a point box gives `√(Ĉ² + Ŝ²)/sin Δ ≈ 20` (`M ≈ 0.04`) at this cell
  size. The adaptive boxes add the rest, up to `40`.

### 6.2 Item 2: the re-anchored budget and the period lower bound

Certified per reference bounce:
- `59 μs ≤ P ≤ 72 μs` (RK4: `63.6–66.6`);
- `Δ ∈ [1.70, 2.49]`, so `sin Δ ≥ 3/5`;
- `M = 0.0816`.

From `ψ₀ = 5.27` (gap `0.52`), the hypothesis of `reactorQA_trapped_reanchored` for `N` bounces is

`0.3264 + R + N (R + γ + 0.0816 (e + σ)) ≤ 0.52`.

- **Crude shears fail** (`osc_crude_shears_fail`).
  - With `σ = 2.49 − 1.70 = 0.79` and `γ = 2M`, the hypothesis fails for every `N ≥ 1`, every
    `R, e ≥ 0` and every start, since `4M + γ + Mσ = 0.554 > 0.52`.
  - Certified shears at the `10⁻³` level are therefore indispensable.
  - They are a Lipschitz (derivative) property of `Δ` and of `(C, S)/sin Δ` in `(ψ₀, B_t)`. The box
    enclosures cannot give them, because each box's `dC` enclosure is itself about `±M` wide.
- **Simulated shears and remainders** (`osc_budget_simulated`).
  - With `σ = 0.0076`, `γ = 7×10⁻⁴`, `R = 2.1×10⁻⁴`, `e = 0.0141`, the hypothesis closes for
    `N = 72`.
  - In reference time this is at least `72 · 59 μs = 4.2 ms`. With the simulated `M = 0.023` it
    was `N = 300`: the certified `M` multiplies the shear term `M(e + σ)`.
  - Converting bounces of the actual orbit into time needs a lower bound on its inter-tip intervals.
    That is the reference period `≥ 59 μs` minus one more one-bounce remainder `δP` (unproved).

### 6.3 Item 3: conserved-quantity comparison (not achieved)

`conserved_quantity_insufficient` shows the gap:
- Over one bounce (`P ≤ 72 μs`), the worst-case helical-momentum drift of a `reactorQA` orbit
  (`helicalMomentum_drift_le`, `ε_QS = 0.0024854 T`) bounds the tip-flux change only by
  `≥ 0.30 T m²`.
- The requirement is `R ≤ 0.0027` (`N = 72`, simulated shears), or `R ≤ 0.097` even for `N = 1`.

Conserved quantities fix the banana (exactly `E`, and `P_φ` to `0.3`) but not the phase along it.
`R` compares the near-QA kick integrand `−2b₁ q A w sin 2φ_near` (plus `O(b₁²)`) with the reference
`−2b₁ q A w sin 2φ_ref`. So it needs:
- `|φ_near − φ_ref| ≲ 10⁻²` rad along one bounce;
- the leg-coordinate relation `x ↦ c` of the near orbit to the same relative accuracy;
- and the analogous statement for `e` (the phase step) and for `δP`.

The term `b₁ cos 2φ` changes `B` by at most `|b₁| r² ≤ 1.6×10⁻³ T` at fixed `(ψ, θ)`. One plausible
route is therefore to run the same cell machinery on the near-QA reduced equations, with this term
as an interval perturbation of the parameter box. That is the variational content that the
Grönwall estimate fails to provide.

### 6.4 What remains (precise)

1. **Remainders `R`, `e`, `δP`** over one bounce, at the levels of §6.2 (`R ≲ 2×10⁻³`,
   `e ≲ 0.015`). They are not touched by the conserved-quantity bound (§6.3).
2. **Shears `σ`, `γ` at the `10⁻³` level**, between anchors `≤ 2M + R ≈ 0.17 T m²` apart in `ψ₀`
   and `≤ 1.6×10⁻³ T` apart in `B_t`. This needs a derivative (Lipschitz) certificate for `Δ` and
   for `(C, S)/sin Δ`.
3. **Resolution of `M`.** `M = 0.0816` (target `Kn = 40`) against the simulated `0.023`:
   - smaller boxes give `0.077` (`Kn = 38`, 152 leaves) and `0.071` (`Kn = 35`, 207 leaves);
   - the cell floor is `≈ 0.04`, and finer cells cost proportionally more kernel time.
