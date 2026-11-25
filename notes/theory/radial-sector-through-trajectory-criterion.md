# The signed trajectories are the remaining input to physical radial action attainment

For the actual QA2R candidate, the long analogue of the sixteen-row signed ODE theorem in N-175 is now sufficient by itself. On each of four radial tiles, start at an arbitrary point of its initial ball. The required signed solution has an ordinary physical derivative and the regular spatial enclosure through $[-331/64,331/64]$, and follows the first 332 canonical tubes on each of the two clocks. Lean proves that these four trajectory statements imply N-178's complete sector conclusion on the original nested embedded tori. The field signs, the first-mirror derivative tests, continuity of the physical family, and the endpoint action comparison have already been discharged. [Physical implication](../../scripts/dommaschk_kam/verify_radial_action_attainment.py)

More explicitly, under this trajectory hypothesis, both first mirror positions and the physical one-way arclength action are continuous jointly in launch phase and radius, and every admissible phase has a strictly interior radius attaining the exact upper-height target. The input requires 332 original steps each way on each tile so that the derivative at the cap is ordinary. Position-tube membership supplies the entire observed interval, including seams. [Signed chain](radial-ribbon-through-chains.md) · [Complete physical signs](radial-ribbon-through-cap-signs.md) · [Continuous sector](compact-sector-first-well-actions.md)

## Replay

The generated implication `DommaschkRadialAttainmentOn391_328_48_16_48_16_8_5.from_tracks` and its section-sign theorem share receipt `720989f0f9ec9810f50162f7a447d6e9db9e351a12e765f18dccb5a88e95be82`. At this checkpoint, that receipt has `through_key = null`. A completed physical trajectory receipt for the same signed packet is required to generate the unconditional theorem `.on_nested_tori`. The field-sign receipt is `94d766bf455298a2ad003c9809cc650a50503608d2663a9ce355876ec81f4f16`.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_action_attainment.py \
  --sector /tmp/plasma-n178-sector.json --signs /tmp/plasma-n181-through-cap.json \
  --output /tmp/plasma-n183-conditional.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_action_attainment.py \
  --sector /tmp/plasma-n178-sector.json --signs /tmp/plasma-n181-through-cap.json \
  --through /tmp/plasma-n175-through332.json --wait --output /tmp/plasma-n183-unconditional.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-183 |
| Kind | Composition of original-field sector certificates |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-175, N-176, N-178, N-181 |
| Dependency requirement | Original two-face physical sector attachment and all four signed field histories on the same packet. |
| Produces | A candidate-specific target theorem conditional only on completion of the four signed trajectory solves. |
| Status | Composition kernel-verified and audited. Long physical propagation is in progress. |
| Lean evidence | Generated `.sections` and `.from_tracks`. |
| Audit evidence | Both generated proofs depend only on propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
