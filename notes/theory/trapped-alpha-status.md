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
