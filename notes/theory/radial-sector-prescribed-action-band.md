# A common interval of prescribed actions across the original launch sector

At the fixed upper mirror height \(h_U=5300546391395933/5000000000000000\), put \(J_*\) equal to the archived action target (approximately 1.35992219). The physical first-well actions at the two radial faces strictly enclose the entire closed interval
\[
I=[J_*-21/10000,\ J_*+19/10000],\qquad |I|=1/250.
\]
This strict bracket holds for every admitted launch phase on the same pair of nested embedded tori. It follows from the actual inner action upper bound \(1146552112157123/844424930131968\) and outer action lower bound \(790254733800996141875465767/580284393415022003858964480\). Both inequalities survive comparison with independently chosen enclosed endpoint trajectories through the same original births. [Endpoint action arithmetic and comparison theorem](../../PlasmaLean/Design/DommaschkSectorActionBand.lean) · [Original endpoint recovery](radial-sector-face-actions.md)

Let \(P=[-2^{-19},2^{-19}]\times[47/100,239/500]\). Let \(j\) be **any continuous function of launch phase** taking values in \(I\). If the four section balls admit enclosed trajectories tracking the 332 signed rows in each direction, there exists one compact connected subset \(K_j\) of \(P\) whose phase projection is the entire interval. Every point of \(K_j\) has first-well action exactly \(j(\phi)\) about its own birth. These wells have two transverse mirrors, and all radial labels in \(K_j\) have a common positive clearance from the boundary. Different prescriptions can select different connected subsets. This includes constant prescriptions at either endpoint of \(I\). The theorem concerns the indicated phase sector and the fixed mirror height; it leaves the full periodic bracket and thermal confinement open. [Connected level proof](connected-original-birth-action-level.md)

## Verification

The strict face theorem `.from_nested_tori` has receipt `9ad6a7ca85047b3659a563e2c7cda7cdaa2d43496b9358b9443736e246b46edd`. The connected-level implication `.from_tracks` has receipt `702d424c113e82c79cc83a1b26f18d6010ce04ef2c5227258abd9e634e2837d2`. Both axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. The second verifier also accepts the completed physical-trajectory composition to discharge the remaining hypothesis.

```sh
lake build PlasmaLean.Design.DommaschkSectorActionBand
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_sector_faces.py \
  --flow /tmp/plasma-n171-flow.json --action-window --output /tmp/plasma-n188-faces.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_connected_action_level.py \
  --faces /tmp/plasma-n188-faces.json --accessible /tmp/plasma-n179-birth.json \
  --attainment /tmp/plasma-n183-conditional.json --output /tmp/plasma-n188-band.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-188 |
| Kind | Quantitative face comparison and connected first-well level sets |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-162, N-178, N-179, N-180, N-182, N-183, N-184 |
| Dependency requirement | Actual two-face action inequalities, true accessible births, a continuous first-well family and the four through-going signed trajectories. |
| Produces | A uniform action interval of width 1/250 and a connected exact level for every continuous phase prescription in this interval. |
| Status | Face actions checked. The connected-level conclusion is conditional on 332 physical slabs in each direction on all four tiles. |
| Lean evidence | `DommaschkSectorActionBand.of_endpoint_witnesses`, `.prescriptions_of_sector`, and the generated `.from_nested_tori` and `.from_tracks`. |
| Last updated | 25 November 2026 |
