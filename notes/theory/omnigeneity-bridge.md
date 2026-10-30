# Quasisymmetry ⇒ omnigeneity in the Boozer guiding-centre model (Q-23)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-29` |
| Title | The quasisymmetry ⇒ omnigeneity bridge: exact and quantitative, Boozer guiding-centre model |
| Kind | definition / proof / counterexample / formalization |
| Addresses | `Q-23`; clause C2 of the stellarator contract; `G-10`, `G-2`, `Q-16`; rung M4 |
| Depends on | Lean: `Kinetic.Boozer.BoozerGCOrbitOn`, `helicalMomentum_hasDerivAt_on`, `helicalMomentum_drift_le`, `invariant_drift`, `constField`; `Design.NearAxisQATrappedBounce.exactQA`, `qaField`; `Design.NearAxisQA.reactorQA`, `reactorQA_B_bounds`, `nearAxis_symmetryDefect_le`. Notes: N-27 (`quasisymmetric-solution.md`), `near-qa-trapped-particles.md` |
| Dependency requirement | All compiled (default build). The Boozer GC equations and the near-axis field are **supplied models** |
| Produces | `IsBounce`, `TrappedBounce`, `bounceAvgDrift`, `radialDrift`, `OmnigenousOn`, `ApproxOmnigenousOn`, `TwistOn`; the exact and quantitative theorems; the sanity triad; the `exactQA` / `reactorQA` instances |
| Difficulty | routine once the momentum identity exists; the content is in the definitions and the counterexample |
| Status | verified (in the model) |
| Lean evidence | `PlasmaLean/Theory/Kinetic/Omnigeneity.lean`, `PlasmaLean/Design/NearAxisQAOmnigeneity.lean` (default build, standard axioms, zero warnings) |
| Audit evidence | not audited |
| Last updated | 30 October 2026: created; exact and quantitative bridge compiled |

## Purpose and scope

C2 asks for omnigeneity: trapped particles have zero bounce-averaged radial drift. A certified
small quasisymmetry defect (Q-16) is only useful for C2 if it turns into a bound on that drift.
This note gives the bridge in the **vacuum Boozer guiding-centre model** of
`Theory/Kinetic/BoozerGuidingCentre`. State `(ψ, θ, φ, ρ)`, field data `B(ψ, θ, φ)`, `ψ_p`,
`ι = ψ_p'`, constant `G`. The equations of motion and the orbits are supplied, the chart is
`ψ > 0`, and helicity `(N, M)` means `ξ = N ∂_θ + M ∂_φ` with defect `ξB = N ∂_θB + M ∂_φB`.
Nothing here is about the Lorentz force, a physical field, collisions or `ε_eff`.

## Definitions (compiled)

* **Bounce period** `IsBounce ρ τ`: `τ > 0`, `ρ(0) = 0`, `ρ(τ) = 0`, and there is `σ ∈ (0, τ)`
  with `ρ(σ) = 0` and `ρ(s) ρ(t) < 0` for `s ∈ (0, σ)`, `t ∈ (σ, τ)`. This is one full banana:
  turning point, one leg, turning point, the opposite leg, turning point. The turning points use
  `ρ = m v_∥/(qB)`, which is equivalent to `v_∥ = 0` when `B > 0`. `IsBounce.unique`: `τ` is
  determined by `ρ`. Starting at `t = 0` is no restriction because the model is autonomous.
* **Trapped bounce in the region** `TrappedBounce F m q μ c ψ θ φ ρ τ`: an orbit on `[0, τ]`,
  `IsBounce ρ τ`, and `ψ ≤ c` on `[0, τ]`. The radial bounce map is `ψ(0) ↦ ψ(τ)`.
* **Omnigeneity** `OmnigenousOn F c`: every trapped bounce in `0 < ψ ≤ c` returns to the same
  `ψ`. This holds for every species `m > 0`, `q ≠ 0`, every `μ ≥ 0` and every energy.
  Equivalently, the bounce-averaged drift `bounceAvgDrift ψ τ = (ψ(τ) − ψ(0))/τ` vanishes
  (`omnigenousOn_iff_bounceAvgDrift`). That quantity is the time average of `ψ̇ = radialDrift`
  (`bounceAvgDrift_eq_avg_radialDrift`, when `ψ̇` is continuous).
* **Approximate omnigeneity** `ApproxOmnigenousOn F c κ`: `|ψ(τ) − ψ(0)| ≤ κ (H(0)/|q|) τ`.
  Here `κ` is dimensionless. `omnigenousOn_iff_approx_zero` gives `κ = 0` ⇔ omnigenous.
* **Twist** `TwistOn F N M c ι_min`: `ι_min |x − y| ≤ |f(x) − f(y)|` on `(0, c]`, where
  `f(x) = N x − M ψ_p(x)`. For QA, `ι ≥ ι_min` implies it (`twistOn_qa_of_iota_ge`, by the mean
  value theorem).

## Claims and evidence

1. **Exact (compiled)** `psi_return_of_QS`. Suppose `ξB = 0` on `0 < ψ ≤ c` and `f` is injective
   on `(0, c]`. Take any orbit on `[0, τ]` in the region with `ρ(τ) = ρ(0)` (for example one
   bounce). Then `ψ(τ) = ψ(0)`.
   Proof: `P = q (f(ψ) + M G ρ)` is conserved, and the correction `M G ρ` returns.
   `omnigenousOn_of_exactQS`: an exactly QS Boozer field is omnigenous.
2. **Quantitative (compiled)** `psi_drift_le_of_defect`, `bounce_psi_drift_le`.
   Hypotheses on the region: `B ≥ B_min > 0`, `|ξB| ≤ δ`, and `TwistOn` with `ι_min > 0`.
   Conclusion, per bounce: `|ψ(τ) − ψ(0)| ≤ 2 H(0)/(|q| B_min ι_min) · δ · τ`.
   `bounceAvgDrift_le` gives the bounce average `≤ 2 H(0) δ/(|q| B_min ι_min)`.
   `approxOmnigenousOn_of_defect_le` gives `κ = 2δ/(B_min ι_min)`.
   Proof: `|ΔP| ≤ (2H/B_min) δ τ` (`helicalMomentum_drift_le`), the correction term cancels
   because `ρ` returns, and the twist converts `Δf` into `Δψ`.
3. **Sanity triad (compiled)**:
   - Degenerate case: `constField_omnigenousOn`, constant `B` with helicity `(1, 0)`.
   - Concrete non-constant instance: `exactQA_omnigenousOn`.
   - Counterexample: `driftMirror k`, with `B = 1 + φ² + k sin θ`, `ι = 0` and `G = 1`. It has the
     explicit orbit `ρ = −sin 2t · D`, `φ = cos 2t/(2D)`, `θ = 0`,
     `ψ = 10 − k(2t − sin 4t/8)`, where `D = √(1 − cos² 2t/4)`. The parameters are `m = q = 1`,
     `μ = 3/2` and `H = 2`.
   - `dm_orbit` and `dm_isBounce` show that this is a full bounce of period `π`.
     `dm_displacement` gives `ψ(π) − ψ(0) = −2πk`.
   - `driftMirror_not_omnigenous` (`0 < k ≤ 1/2`): the field is not omnigenous.
     `driftMirror_zero_omnigenous` covers the symmetric member `k = 0`.
   - `dm_quantitative_check`: the quantitative theorem applies to this orbit (so it is not
     vacuous). It gives `8πk` against the actual `2πk`, so the linear dependence on `δ` cannot be
     improved.
4. **Applications (compiled)**:
   - `exactQA` (`b₁ = 0`) is omnigenous on every region.
   - `reactorQA_approxOmnigenousOn`: `κ = 2 · 0.0024854/(4.93 · 0.422)`.
   - `reactorQA_alpha_bounce_drift`: 3.5 MeV alphas, any `μ ≥ 0`, trapped bounce in
     `0 < ψ ≤ ψ_a`. Then `|Δψ| ≤ 4182 τ` T m² and `|Δψ/τ| ≤ 4182 T m²/s`.

## What is in the model, not the physical field

- The Boozer guiding-centre equations are supplied. They are not derived from Newton–Lorentz,
  and `μ` conservation is not proved.
- The orbits, and the existence of trapped bounces, are supplied. Existence of a bounce for a
  given field is shown only for the explicit counterexample.
- `reactorQA` is the truncated near-axis field. It has no `O(r³)` remainder bound.
- `ξB` is the Boozer-chart defect. Its identification with the Cartesian `qsError` of
  `Fields.WeakQS` (N-27) is not formalized.

## Difficulty, barriers and readiness

The bound is worst-case. It treats the forcing as constant-sign, so it is linear in the bounce
time. With the simulated alpha bounce time `≈ 6.6 × 10⁻⁵ s` it gives `≈ 0.28 T m²` per bounce.
That is useless as a transport estimate, though correct as a bound. The true bounce-averaged drift
of the `sin 2φ` defect is much smaller, because the defect oscillates along the banana. The
averaging machinery (`BounceClamp`, `BounceShear`, `NearAxisQATrappedOsc*`) is the route to a
sharp bound, which would use bounce integrals of `ξB` rather than its sup.

## Outputs and next dependencies

- **Connection to `ε_eff` (not done).** `ε_eff^{3/2}` is a velocity-space and flux-surface
  average of the squared bounce-averaged radial drift, weighted by the bounce time (Nemov et al.,
  Phys. Plasmas 6 (1999) 4622). The pointwise bound `|Δψ/τ| ≤ 2Hδ/(|q| B_min ι_min)` gives
  `ε_eff^{3/2} ≲ C δ²` once a precise definition of `ε_eff` in this model and the measure on the
  trapped region are fixed. That is the next step towards C5 (1/ν transport).
- A sharp bound via bounce integrals of `ξB` (oscillation), and the quasi-isodynamic route, are
  open. Quasi-isodynamic fields are omnigenous without QS, so the converse implication fails.
- The plan registry entry for Q-23 should be updated (not edited here).
