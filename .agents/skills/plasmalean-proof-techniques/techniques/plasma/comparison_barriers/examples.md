# Examples: Comparison Principles, Barriers and Grönwall/Riccati Arguments

## Example 1: Temperature stays above a lower profile

**Problem shape:** For the radial transport equation with nonnegative diffusion, show that the
temperature `u.T ψ t` stays above a profile `f ψ` on `[0, 1] × [0, τ]`.

**Use of technique:**
1. Barrier: `f` with margin `κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ)`, `κ > 0`.
2. Ordering: `f ψ ≤ u.T ψ 0` initially and `f 1 ≤ Tedge t` at the edge; the axis is handled by
   `DegenerateAxis c`.
3. At a first crossing values and slopes agree and curvatures are ordered, so `first_crossing`
   gives a strict inequality contradicting the PDE.
4. Conclusion: `le_of_lowerMargin_axisFree`
   (`PlasmaLean/Theory/Transport/BarrierCheck.lean`), for a supplied `AxisFreeSolution`.

## Example 2: Field lines cannot cross a barrier surface

**Problem shape:** A field line starting where `G < 0` stays there while it remains in a region
`U`.

**Use of technique:**
1. Grönwall hypothesis `GronwallOn B G L U`: the derivative of `G` along `B` is bounded by
   `L |G|` on `U`.
2. Then `|G(γ t)|` cannot reach zero in finite time from a nonzero value.
3. Conclusion: `fieldLine_sign_preserved` (`PlasmaLean/Theory/Fields/InvariantBarrier.lean`),
   used for torus trapping in `TorusTrapping.lean`.

## Example 3: Riccati comparison for a perturbation energy

**Problem shape:** A perturbation energy satisfies `Y' ≤ −νY + CεY²`. Show it does not grow.

**Use of technique:**
1. Smallness: `C * ε * Y 0 < ν` makes the right side negative at `Y 0`.
2. A first time with `Y > Y 0` would have `Y' > 0` but the inequality forces `Y' < 0`.
3. Conclusion: `riccati_le_initial` (and the decay version `riccati_exp_decay`,
   `PlasmaLean/Theory/Stability/RiccatiComparison.lean`). An additive residual `ε(t)` needs the
   inward-radius version (Q-27, N-39), not yet in Lean.

## Example 4: Finite-time confinement from an approximate invariant

**Problem shape:** A guiding-centre quantity `K` drifts slowly; show the particle is not lost
before time `T`.

**Use of technique:**
1. Bound `|K'| ≤ ε` on `[0, T]` and start with `K 0 ≤ k₀`.
2. If `ε * t < kloss - k₀` then `K t < kloss`: `excludes_loss`
   (`PlasmaLean/Theory/Kinetic/ApproximateInvariant.lean`).
3. The conclusion is a finite-time statement; its horizon is `(kloss − k₀)/ε`.
