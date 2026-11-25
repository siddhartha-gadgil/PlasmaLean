# The original radial births share an accessible interval around phase zero

**Verified on the original field.** Choose the common pair of nested embedded QA2R tori. For **every** $u\in[0.470,0.478]$ and **every** $|\phi|\le2^{-19}$ there is a signed physical field line $y$ through the original interpolated torus position at angle $\phi$. Its ordinary angle derivative solves the QA2R ODE throughout $[-15/64,15/64]$. It stays in the regular spatial box there. Most importantly,
$$\lVert B(y(t))\rVert<h_U\qquad(-1/8\le t\le 1/8),$$
where $y(t)$ denotes the point on the line at azimuth $t$. This interval contains both the launch phase and the zero section, so they are in the same accessible component at $h_U$. No long-trajectory or transversality hypothesis enters this conclusion. [Physical proof and replay](../../scripts/dommaschk_kam/verify_radial_accessible_birth.py)

## Why the birth angle matters

Earlier first-well certificates center their accessible interval at the symmetry section. A line through a birth at nonzero $\phi$ must also place that birth inside the well. The submirror interval settles this for every radius and launch phase in the rectangle. Two independently selected regular solutions through the same original birth have identical field strengths on the common interval by ODE uniqueness. A first mirror around zero cannot fall between zero and $\phi$, since its strength would equal $h_U$ inside the strictly submirror region. The same mirror endpoints and action therefore apply with the well centered at the original birth. [Transfer to any independent long line](../../PlasmaLean/Design/DommaschkRadialAccessibleBirth.lean) · [Section-centered action criterion](four-section-prescribed-action-criterion.md)

## Evidence

The proof composes the sixteen true ODE slabs in each direction on every tile with the first eight signed field exclusions. Only the first and last derivative endpoints of the sixteen-slab solve are removed when forming the closed smooth window. The strict field inequalities include the endpoints at $\pm1/8$. Terminal-value uniqueness on the short approach places the same trajectory at the original torus interpolation. [Through-line verification](radial-ribbon-through-chains.md) · [Signed field inequalities](radial-ribbon-mirror-orientation.md)

The two unconditional declarations, `DommaschkRadialAccessibleBirth016.in_ball` and `.from_nested_tori`, share receipt `27e0524be90ab17c7c92b064e3ce2e4e840e965a11ea06e62926c6c1c843d4d8`. The through-path parent is `e8e4d6765daeabb73679a1ce2a0add4f1ac959a3db589f36e5d6c485e016e837`. The target-action criterion over the longer window still requires physical trajectories reaching the outer caps.

```bash
lake build PlasmaLean.Design.DommaschkRadialAccessibleBirth
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_accessible_birth.py \
  --through /tmp/plasma-n175-through16.json --below /tmp/plasma-n172-birthsign-{0,1,2,3}.json \
  --output /tmp/plasma-n179-birth.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-179 |
| Kind | Unconditional original-field continuum enclosure and transfer of the first well to the birth phase |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-169, N-171, N-172, N-175, N-176 |
| Dependency requirement | Common original birth and seed balls, genuine signed lines, and four verified early field histories. |
| Produces | All continuous original radial births lie in a single accessible time interval on their own line. Section-centered first wells on independent continuations are also birth-centered. |
| Status | Kernel-verified on both signs and the full phase–radius rectangle. |
| Lean evidence | `DommaschkRadialAccessibleBirth.well_at_birth`, generated `.in_ball` and `.from_nested_tori`. |
| Audit evidence | All declarations use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
