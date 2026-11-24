# Field strength and arclength at two nearby QA2R births

Lean compares the true QA2R field at radial labels $0.470$ and $0.478$ throughout the signed toroidal-angle interval $[-1/64,1/64]$. At every common angle the outer field strength is at least $1/18000$ below the inner strength. Its arclength per radian is at least $3999/4000$ of the inner arclength per radian. Both strengths are at most $17/16$. The result holds for every pair of points in the two original outgoing tubes at the given angle. [Physical comparison theorem](../../PlasmaLean/Design/DommaschkPairedActionProfiles.lean) · [Ground certificate](../../scripts/dommaschk_kam/verify_paired_action_profiles.py)

For every launch angle $|\varphi|\le 2^{-19}$, a second theorem supplies two actual field lines through the two original interpolated births at $\varphi$, on the same pair of nested, embedded, invariant QA2R tori. The strength and arclength inequalities hold on those lines on the full closed interval. In its interior the arclength weights equal the norms of the derivatives of the Cartesian field lines. The theorem takes the common choice of surfaces before the choice of launch angle. Separate entry and passage theorems allow composition with a longer certification on a specified pair of surfaces. [Birth and ODE identification](../../PlasmaLean/Design/DommaschkPairedActionBirth.lean) · [Common embedded family](../../scripts/dommaschk_kam/verify_paired_action_births.py)

## Certified launch-slab ranges

These decimal endpoints are exact outward-rounded multiples of $10^{-7}$ in the archived QA2R normalization, valid in both signed directions. Each label uses its own archived radius and height polynomials and the larger of its original two outgoing remainders after reflecting the backward coordinates.

| Launch label | Field-strength interval | Arclength per radian |
| --- | --- | --- |
| $0.470$ | $[1.0440737,1.0440845]$ | $[0.9982610,0.9984671]$ |
| $0.478$ | $[1.0439811,1.0439920]$ | $[0.9983457,0.9985524]$ |

The independent strength intervals give a gap of at least $0.0000817$. The lower outer arclength bound also exceeds $3999/4000$ times the upper inner bound. No derivative with respect to the radial label enters the proof. Exact arithmetic on the degree-seven time models encloses the compensated strength numerator $R^{16}(h_{\rm upper}^2-\|B\|^2)$, the full numerator $R^{16}\|B\|^2$, $R^{16}$ and the positive toroidal denominator $D$. The arclength follows from $D w=R^8\|B\|$. The two signed rows at each radius retain their distinct frame data. [Harmonic physical field identity](../../PlasmaLean/Design/DommaschkNativeActionGeometry.lean) · [Reflection identity](../../PlasmaLean/Design/DommaschkNativeActionReflection.lean)

This certificate supplies the two inequalities in N-126 on the launch-adjacent part of the well. The finite action increment requires the inequalities at all angles between the raised pilot's first mirrors and a first-well identification for the second line. The all-row assessment in N-126 uses an external exact-arithmetic screen. [Finite radial action comparison](finite-radial-action-comparison.md)

## Reproduction

```bash
lake build PlasmaLean.Design.DommaschkPairedActionBirth
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_action_profiles.py \
  --row 0 --output /tmp/plasma-paired-action-profile000.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_action_births.py \
  --profiles /tmp/plasma-paired-action-profile000.json \
  --launches /tmp/plasma-signed-all-eight-launches.json \
  --output /tmp/plasma-paired-action-birth000.json
```

The launch input is the signed eight-endpoint receipt from N-91, key `00d2435ba6f701921afb68b8863175e6ac12e5d4ec2a672c79261395f1dea663`. The ten tube declarations passed with key `19cb7931a211c8713fdf9b23addbb3a67141e8f589b188c1c5aebeaab7fda443`. Two independently compiled final assemblies gave key `b31df84535123139dee4d846013f430b35006ecece4964444a2925ef46a133a5`. The final tube and birth checks took 4.020 and 3.381 seconds respectively after their model inputs were available. Both audits reported `propext`, `Classical.choice` and `Quot.sound`. [Signed launch input and reproduction](dommaschk-eight-signed-launches.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-128 |
| Title | Field strength and arclength at two nearby QA2R births |
| Kind | Paired physical observable certificate and original launch-family application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-91, N-94, N-99, N-126 |
| Dependency requirement | True signed physical launch tubes on a common Q-16 pair, harmonic identities for the actual QA2R field, and original outgoing coordinate records for both radii. |
| Produces | Ground common-angle strength and arclength inequalities throughout the two signed launch slabs, through both exact births on explicitly embedded tori. |
| Difficulty | Preserve the original signed tubes and identify the same physical paths during the angle-shifted approach to the section. |
| Status | Verified physical launch-slab comparison and independently replayed common-family ground theorem. |
| Lean evidence | `DommaschkPairedActionProfiles.Compared`, `.field_range`, `.weight_range`, `DommaschkPairedActionProfile000.forward`, `.backward`, `DommaschkPairedActionBirth000.from_passages`, `.from_entries`, `.from_embedded_tori`. |
| Last updated | 25 November 2026 |
