# Unique transverse physical field-line contacts in both mirror brackets

From every admissible local entrance at section zero and radius 0.470, a physical field line reaches the specified mirror height exactly once in its closed bracket. The contact is interior. With $t$ the outward toroidal angle and $h$ the attained positive field strength, the following strict inequalities hold in either direction.

| Closed bracket | Height | Lower bound for $d|B|^2/dt$ throughout the interior | Lower bound for $d|B|/dt$ at contact |
| --- | --- | --- | --- |
| [316/64,317/64] | 5297961656084411 / 5000000000000000 | 1/128 | $1/(256h)$ |
| [324/64,325/64] | 5300546391395933 / 5000000000000000 | 1/400 | $1/(800h)$ |

The exact argument differentiates the three sparse field expressions along the physical ODE, including their explicit dependence on toroidal angle. A positive polynomial denominator converts the derivative inequality to a certified numerator bound on the whole trial box. The corresponding squared strength is strictly increasing on each closed bracket. The N-77 endpoint signs then give existence and uniqueness on the same field line. Positivity of $h$ gives the slope estimate for field strength itself. [Physical chain rule](../../PlasmaLean/Design/DommaschkMirrorStrengthSlope.lean) · [Exact spatial derivative certificates](../../scripts/dommaschk_kam/verify_mirror_slopes.py) · [Local existence and uniqueness](../../scripts/dommaschk_kam/verify_transverse_mirror_hit.py)

On the backward branch the signed toroidal angle decreases as $t$ increases. Thus the derivative in the table is positive when moving away from the common section on either side. These statements locate a unique crossing of a field-strength level from a **local** entrance. Connecting the launch to both mirror slabs and excluding all earlier encounters is the remaining trace problem. Lean now separately excludes such encounters along the entire signed interval $[-2,2]$ at this birth family, covering 128 slabs each way, with position error below $2.216×10^{-6}$. The signed exclusion has key `39d9f69d7f1b`. [Launch, path and earlier-sign replay](dommaschk-signed-submirror-trace.md)

## Reproduce

Prepare the two ordinary spatial Jacobian packages and the four physical hit manifests in N-77. Build `PlasmaLean.Design.DommaschkMirrorStrengthSlope`, then run the per-row and per-direction checks.

```sh
for i in 316 324; do
  .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_slopes.py --index "$i" --part angles
  .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_slopes.py --index "$i" --part tube --output "/tmp/qa2r-slope-$i.json"
  for dir in fwd back; do
    .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_physical_hit.py --physical "/tmp/qa2r-$dir-$i.json" --brackets /tmp/qa2r-brackets.json --index "$i" --output "/tmp/qa2r-hit-$dir-$i.json"
    .venv-ws/bin/python scripts/dommaschk_kam/verify_transverse_mirror_hit.py --hit "/tmp/qa2r-hit-$dir-$i.json" --slopes "/tmp/qa2r-slope-$i.json" --output "/tmp/qa2r-transverse-$dir-$i.json"
  done
done
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-81 |
| Kind | Physical field-line transversality |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-66, N-76, N-77, N-79 |
| Dependency requirement | Physical ODE, strict endpoint signs, positive radius and denominator, directed angular and spatial field derivatives. |
| Produces | Four unique, quantitative local field-strength crossings, and exclusion of earlier contacts through ±2 radians on the signed birth trajectory. |
| Difficulty | Reach the brackets from the same launch and certify the whole intervening path below the height. |
| Status | All four local ODE theorems and the signed exclusion compiled and audited. |
| Lean evidence | `DommaschkTransverseMirrorHit{Forward,Backward}{316,324}.transverse_from_entry` and `.squared_strictMonoOn`; `DommaschkSubmirror128Of128.below_from_birth`. |
| Audit evidence | Lower keys `84b9af33c9b5`, `4859f1de71fe`; upper keys `739d60ddcb1e`, `105502480318`. Standard axioms only. |
| Last updated | 24 November 2026 |
