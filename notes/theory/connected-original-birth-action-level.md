# A connected set of original births at the prescribed first-well action

Let $P=[-2^{-19},2^{-19}]\times[0.470,0.478]$. The radial coordinate in $P$ is the interpolation label between the two original QA2R tori. At the archived upper height $h_U$ and action $J_*$, the following implication has passed Lean and the axiom audit.

**Hypothesis.** Every point of each of the four specified section balls has a genuine signed field line following the first 332 canonical slabs on each clock. The ordinary ODE and regular spatial enclosure hold on the interior closed window through $\pm331/64$.

**Conclusion.** On one pair of nested embedded invariant tori, there is a compact connected set $K\subset P$ of original birth parameters with the following properties.

- Its phase projection is the entire interval $[-2^{-19},2^{-19}]$.
- There is a common $\delta>0$ such that every label in $K$ lies in $[0.470+\delta,0.478-\delta]$.
- Each parameter in $K$ gives a true field line through its original torus-interpolated birth at phase $\phi$. Its first accessible well **around $\phi$ itself** has two transverse mirrors and physical arclength action exactly $J_*$. The two mirror times are restrictions of continuous functions on $P$.

The physical lines at the two radial faces have strictly opposite action signs relative to $J_*$. Joint continuity and the rectangle crossing theorem select one connected part of the level spanning the whole phase interval. Its compactness makes the interior radial clearance uniform. The independent short-field-line proof places every original birth in the component containing the symmetry section, so the selected mirror pair applies at the true birth. The result gives neither a parametrization of $K$ by a single radius per phase nor a numerical value of $\delta$. [Physical crossing theorem](../../PlasmaLean/Design/DommaschkConnectedActionLevel.lean) · [Browder continuation](connected-rectangle-action-level.md) · [Original face signs](radial-sector-face-actions.md) · [Birth accessibility](accessible-radial-birth-window.md)

## Proof state and replay

The generated candidate implication `DommaschkConnectedLevelOn391_328_48_16_48_16_8_5.from_tracks` has receipt `62f79d52472b34907d9c7e8f6ee60e6d6e324db83b7c5f3f86b5810fd591d47b`. At this checkpoint the long signed trajectories remain the only undischarged hypothesis. The verifier separately supports the completed physical trajectory receipt and produces `.on_nested_tori` when that receipt is available. [Exact composition](../../scripts/dommaschk_kam/verify_connected_action_level.py) · [Signed trajectory criterion](radial-sector-through-trajectory-criterion.md)

```sh
lake build PlasmaLean.Design.DommaschkConnectedActionLevel
.venv-ws/bin/python scripts/dommaschk_kam/verify_connected_action_level.py \
  --faces /tmp/plasma-n182-sector-faces.json --accessible /tmp/plasma-n179-birth.json \
  --attainment /tmp/plasma-n183-conditional.json --output /tmp/plasma-n184-conditional.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-184 |
| Kind | Connected-level topology applied to first wells of actual torus-interpolated births |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-178, N-179, N-180, N-182, N-183 |
| Dependency requirement | Actual radial-face actions, continuous mirror times and action, accessibility at the original birth, and the four signed physical trajectories. |
| Produces | A connected target-action set covering the complete phase sector, with uniformly interior labels and true birth-centered transverse mirrors. |
| Status | Candidate implication kernel-verified. Completion of all four through-cap trajectories remains open. |
| Lean evidence | `DommaschkConnectedActionLevel.crossing_of_sector` and generated `.from_tracks`. |
| Audit evidence | Both declarations use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
