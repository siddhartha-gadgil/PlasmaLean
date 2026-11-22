# Skill: Comparison Principles, Barriers and Grönwall/Riccati Arguments

**Pre-condition:** The claim says that a solution of an evolution equation (a transport PDE, a
field-line or guiding-centre ODE, a scalar energy inequality) stays on one side of a threshold,
stays in a region, or decays, over a stated time interval. The equation must have a comparison
structure: a parabolic operator with nonnegative diffusion, an ODE along which a quantity has a
controlled derivative, or a scalar differential inequality.

**Goal:** Prove `u ≥ f` (or `u ≤ f`, `G(γ t) < 0`, `Y t ≤ Y 0`) for all times in the interval by
exhibiting a barrier and ruling out a first crossing.

**Instructions:**
1. **Choose the barrier:** a sub- or super-solution profile `f` (transport), a function `G` whose
   zero level set bounds the region (field lines, orbits), or a scalar comparison ODE (Riccati,
   Grönwall).
2. **Margin inequality.** Prove the strict inequality for the barrier: the operator applied to `f`
   exceeds the time derivative by `κ > 0`, or `|d/dt G(γ)| ≤ L |G(γ)|` on the region (Grönwall),
   or `Y' ≤ −νY + CεY²` with `CεY(0) < ν` (Riccati).
3. **Initial and boundary ordering.** Check the order at `t = 0` and on the boundary for all
   times (edge data), and handle degenerate points separately (the magnetic axis: a
   `DegenerateAxis` hypothesis, or an axis-free formulation).
4. **First crossing.** Suppose a first time and place where the order fails. There the values
   agree, slopes agree and curvatures are ordered, so the operator gives the opposite strict
   inequality: contradiction. For ODEs this is the sign-preservation or exponential-bound lemma.
5. **Approximate invariants.** If a quantity `K` changes at most `ε` per unit time, it stays
   below a loss threshold while `ε t < k_loss − k₀`: a finite-time confinement statement.
6. **State the horizon.** Results hold on `[0, τ]` and on the region the trajectory is assumed to
   stay in; an "always" claim needs a separate argument for staying in the region.

**Lean:** `PlasmaLean/Theory/Transport/Comparison.lean` and `BarrierCheck.lean`,
`PlasmaLean/Theory/Fields/InvariantBarrier.lean` and `TorusTrapping.lean`,
`PlasmaLean/Theory/Stability/RiccatiComparison.lean`,
`PlasmaLean/Theory/Kinetic/ApproximateInvariant.lean`,
`PlasmaLean/Certificates/DiscreteMaxPrinciple.lean` for the discrete scheme. Solutions are usually
supplied as hypotheses (`AxisFreeSolution`); say so in the claim.
