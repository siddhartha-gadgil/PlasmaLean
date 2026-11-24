# Local physical level contacts at both Dommaschk mirror heights

At section zero and radius 0.470, the archived action calculation uses two mirror heights. For each row below and in each clock direction, Lean proves that every admissible local entrance state has a solution of the magnetic field-line ODE reaching the specified height at an interior time. That same solution remains in its certified tube, including at the joins, and ends in the stated exit ellipsoid. For the backward launch the signed toroidal angle is the negative of the listed elapsed angle.

| Height in the dimensionless field normalization | Open interval of elapsed angle | Forward hit key | Backward hit key |
| --- | --- | --- | --- |
| 5297961656084411 / 5000000000000000 | (316/64, 317/64) | `ca9b6cfab897` | `5f8c1b598406` |
| 5300546391395933 / 5000000000000000 | (324/64, 325/64) | `321f55ca84c4` | `c1ebeb6041cf` |

Eight spatial signs underlie the four level contacts. The entire physical tube at the left endpoint is strictly below the row's height, and the entire tube at the right endpoint is strictly above. The endpoint certificates keep the same radial variable in the magnetic field and the radius-dependent denominators. Vertical reflection supplies the backward signs. Continuity of the true field strength at positive cylindrical radius then applies to any continuous enclosed path. Composing this result with the physical step gives the four ODE existence theorems. [Endpoint arithmetic](../../scripts/dommaschk_kam/verify_mirror_endpoint_signs.py) · [Physical hit generator](../../scripts/dommaschk_kam/verify_mirror_physical_hit.py)

## Earliest contact from launch

Lean also proves a general criterion. Suppose one path lies in consecutive certified tubes from a launch at $a$, each preceding tube has observable strictly below $h$, and on the last bracket $[l,r]$ the path observable is continuous with value greater than $h$ at $r$. If the observable is below $h$ through $l$, the earliest level contact occurs at some $c$ strictly between $l$ and $r$, and the observable stays below $h$ on $[a,c)$. Continuity on the final bracket suffices even when the certified information on earlier slabs consists only of inequalities. The packed-row version accepts a prefix of a longer trajectory and uses its original path throughout. [Earliest-contact criterion](../../PlasmaLean/Theory/Fields/TrajectorySlabObservable.lean) · [Packed-row theorem](../../PlasmaLean/Certificates/PositionFrameObservables.lean)

Applying the criterion to a Q-16 birth requires the continuous field-line proof from launch to the bracket and an all-slabs sign certificate through the left endpoint. The target also admits a distinct question about transversality, namely whether field strength has nonzero derivative at the contact. None of the four local theorems uses a transversality assumption.

## Reproduce

Build the two on-demand modules and prepare the ordinary shared Jacobian and central defect for each bracket row as in N-76. The two sign and physical generators audit all final declarations.

```sh
lake build PlasmaLean.Design.DommaschkFirstMirrorLaunchSign PlasmaLean.Design.DommaschkMirrorBracketSlab
.venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_endpoint_signs.py --output /tmp/qa2r-brackets.json
for i in 316 324; do
  .venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_slabs.py --range "$i" "$i" --shared-from 16 --output "/tmp/qa2r-fwd-$i.json"
  .venv-ws/bin/python scripts/dommaschk_kam/verify_backward_physical_prefix.py --row "$i" --output "/tmp/qa2r-back-$i.json"
  for dir in fwd back; do
    .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_physical_hit.py --physical "/tmp/qa2r-$dir-$i.json" --brackets /tmp/qa2r-brackets.json --index "$i"
  done
done
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-77 |
| Kind | Physical field-strength and ODE certificates |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-60, N-66, N-70, N-75, N-76 |
| Dependency requirement | Positive cylindrical radius, authenticated signs on both endpoint tubes, and a checked physical step from the specified entrance ellipsoid. |
| Produces | Four local field-line level hits, eight directed endpoint signs, and a reusable earliest-contact criterion. |
| Difficulty | A Q-16 first-contact result needs the entire physical prefix and its strict signs. A simple turning point further requires transversality. |
| Status | Compiled and audited. The local hypotheses and intervals are listed above. |
| Lean evidence | `DommaschkPhysicalMirrorHit{316,324}.hit_from_entry` and their `Backward` counterparts; `PositionFrameSlabs.first_contact_after_prefix`. |
| Audit evidence | Standard axioms only. Signed bracket keys `f56a4f10f2b9` and `0df4dae1b967`; four physical hit keys above. |
| Last updated | 24 November 2026 |
