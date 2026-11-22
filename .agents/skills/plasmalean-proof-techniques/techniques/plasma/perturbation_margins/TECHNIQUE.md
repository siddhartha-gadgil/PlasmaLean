# Skill: Perturbation Bounds and Robust Margins

**Pre-condition:** A property is proved (or certified) for nominal data, and the claim is that it
survives every perturbation in a stated set: coil placement and tangent errors, current errors,
parameter boxes, measured coefficients with error bars, truncated modes. The property must be
an inequality with a margin, or an open condition.

**Goal:** Prove `property(actual)` for every `actual` within the tolerance, from
`property(nominal)` with margin `m` and a proved bound `‖Q(actual) − Q(nominal)‖ ≤ δ(tolerance)`
with `δ ≤ m`.

**Instructions:**
1. **Name the quantity** `Q` the property depends on (field at a point, a coefficient, an energy
   constant) and the property as `Q ∈ S` with a margin: distance from the boundary of `S` at least
   `m`.
2. **Parameterize the perturbation** with explicit norms and constants: position error `ε`,
   tangent error `η`, separation `d`, speed `V`, current difference.
3. **Bound the change** by the mean value theorem, a difference identity
   (`F(a) − F(b) = ∫ DF`), or an explicit kernel estimate. Keep every constant explicit; no `O(·)`.
4. **Close with the margin:** `δ ≤ m` gives the property for every perturbation. Report the
   largest certified tolerance, not the hoped-for one.
5. **Guard the hypotheses.** Perturbation bounds usually need a separation or non-degeneracy (the
   evaluation point stays a distance `d + ε` from the coil, `|B|` stays away from zero). These are
   part of the claim.
6. **Compose:** bounds add along a chain (coil error → field error → equilibrium or orbit error);
   propagate them explicitly, and recompute dependent certificates when data change.

**Lean:** `PlasmaLean/Theory/Fields/CoilPerturbation.lean`, `FieldVariation.lean`,
`PlasmaLean/Theory/Geometry/PlacedCircle.lean` (`placedCircle_position_error`,
`placedCircle_tangent_error`), `robust_mono` in `PlasmaLean/Bridge/Contracts.lean`; skill
`plasmalean-design-stellarator` for tolerance studies.
