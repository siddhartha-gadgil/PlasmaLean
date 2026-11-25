# A compact target-action set over launch phase and radius

Let $P=[-2^{-19},2^{-19}]\times[0.470,0.478]$ be the compact rectangle of original phase and radial interpolation label. For the QA2R field, the four signed section checks of N-176 imply that the left and right first mirrors around the zero section and their physical arclength action vary continuously **jointly in both parameters**. The set of points of $P$ at the exact prescribed action is compact. For every phase its fiber contains a strictly interior radius. The same pair of nested embedded invariant tori is fixed throughout the rectangle. [Candidate sector theorem](../../PlasmaLean/Design/DommaschkSectorAction.lean)

## Two reusable statements

1. For solutions of a smooth autonomous ODE enclosed in a common compact region on a common finite interval, continuous birth positions at continuously varying birth times determine a jointly continuous solution in parameter and time. The birth time may move across the observation time. In the proof, evaluate the fixed reference solution at the varying birth time, compare the two positions there, and use the two-sided Grönwall bound. This avoids a separate uniform speed estimate. [Moving birth clocks](../../PlasmaLean/Theory/Fields/MovingBirthClock.lean)
2. In a jointly continuous family of field strengths, arclength densities and heights, assume common low birth and high cap signs. If both first contacts are transverse at every parameter, then both first times and the first-well action vary continuously. No regularity of later wells is required. Accessibility before the first contact and the existence of superlevel points immediately beyond it provide the two continuity inequalities. Adding the signed action integrals gives continuity of the physical integral. [Continuous first-well positions and actions](../../PlasmaLean/Theory/Kinetic/ContinuousFirstWellAction.lean)

For the candidate, the Cartesian original birth is continuous jointly in phase and interpolation radius because both tori supply smooth coordinate functions. The angle ODE implies joint continuity of Cartesian position, field strength and the norm of the physical Cartesian angle velocity throughout the time window. The latter is the arclength density appearing in the action. The closed level of this continuous action on the compact rectangle is compact; the verified radial comparison supplies an interior point in each phase fiber. A connected component spanning the phase interval would strengthen this conclusion.

## Verification

The concrete theorem is `DommaschkSectorTargetOn391_328_48_16_48_16_8_5.from_sections`; its receipt is `cb0d28f409b120995edb207d1357c2b5d827e47deb57fe843d9cce9bc4c8ca62`. The conditional statement uses the same four physical section checks as N-176. The all-radius signed verification is still advancing through the long window. [Section criterion](four-section-prescribed-action-criterion.md) · [Through-path proof](radial-ribbon-through-chains.md)

```sh
lake build PlasmaLean.Design.DommaschkSectorAction
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_section_target.py --sector \
  --flow /tmp/plasma-n171-flow.json --output /tmp/plasma-n178-sector.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-178 |
| Kind | Parameter-dependent ODE theorem and topology of the physical action level |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-167, N-169, N-171, N-176 |
| Dependency requirement | The embedded torus geometry, endpoint action bracket and the four signed section checks. |
| Produces | Jointly continuous first mirrors and first-well action, a compact target set projecting onto the entire phase sector. |
| Status | Generic results and original-candidate implication kernel-verified. The physical long-path hypotheses remain open. |
| Lean evidence | `TrajectoryFamily.continuousOn_of_moving_birth`, `CappedFamily.continuous_first_wells`, `DommaschkSectorAction.sector_of_sections` and generated `.from_sections`. |
| Audit evidence | Both generic theorems, their physical specialization and the generated candidate implication use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
