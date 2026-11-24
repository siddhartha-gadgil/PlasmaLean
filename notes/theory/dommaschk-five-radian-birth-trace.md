# A five-radian physical birth trajectory below both mirror heights

At the phase-zero, radius-0.470 launch, every admissible birth defined by interpolation between the two certified Q-16 tori reaches its section state and lies on one physical field line enclosed for $-5/2\le t\le5/2$. Here $t$ is signed geometric angle in radians. Lean certifies **160 consecutive physical slabs on each side**, with the physical ODE also satisfied at the common section and the slab joins. The maximum dimensionless position error from the archived moving references is

$$
2678772121456213228 / 2^{80} < 2.216\times10^{-6}.
$$

On this same trajectory and throughout the closed five-radian interval, the physical field strength stays strictly below both archived mirror heights. The bounds apply to every allowed angular birth in the phase-zero sector, $|\phi|\le 2^{-19}$. They cover five radians of field-line geometry. The mirror brackets start at outward angles $316/64$ and $324/64$, and the thermal-particle confinement criterion remains open. [Signed trajectory verifier](../../scripts/dommaschk_kam/verify_paired_physical_prefix.py) · [Physical field-strength comparison](../../scripts/dommaschk_kam/verify_signed_submirror_prefix.py)

| Ground proof | Content-key prefix |
| --- | --- |
| Forward 160-slab physical passage | `145afb03c236` |
| Backward 160-slab physical passage | `b553acc30e79` |
| Joined birth path and uniform error | `f22dd8e9662b` |
| Lower height along the signed path | `5586a0503646` |
| Upper height along the signed path | `9b54965a2d48` |
| Negative-clock solution from the forward chain by reflection | `f1c67a78a51e` |

There is a second proof of backward propagation. At either symmetry section, reflecting $Z$ reverses the outward field-line clock and preserves field strength, geometric arclength and action. All eight launch ellipsoids are invariant as sets. To start the backward solution at a prescribed state $x$, solve the forward problem at the **reflected state** and reflect its path. The two seeds coincide exactly on $Z=0$. The resulting enclosure uses reflected forward tubes. For this 160-row application, cylinder radius positivity on every tube follows from a single check over all 391 forward archive rows. [Physical reflection](../../PlasmaLean/Design/DommaschkReflectedPath.lean) · [Full-archive radial positivity](../../PlasmaLean/Design/DommaschkReflectedPilot.lean)

## Reproduce

Prepare the per-row residual and Jacobian proofs as in [N-76](dommaschk-signed-trace-spatial-split.md) and the strict signs as in [N-84](dommaschk-complete-pre-mirror-signs.md). Within the 160-slab prefix, row 68 uses the time-panel certificate and rows 69–71 and 118–119 use the projected rectangle.

```sh
for dir in forward backward; do
  if [ "$dir" = forward ]; then verifier=verify_physical_trace_prefix; else verifier=verify_backward_physical_prefix; fi
  .venv-ws/bin/python "scripts/dommaschk_kam/$verifier.py" --length 160 --shared-from 16 --square-panels 68 --projected 69 70 71 118 119 --output "/tmp/qa2r-$dir-160.json"
done
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_physical_prefix.py --forward /tmp/qa2r-forward-160.json --backward /tmp/qa2r-backward-160.json --output /tmp/qa2r-paired-160.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_submirror_prefix.py --paired /tmp/qa2r-paired-160.json --signs /tmp/pre-lower.json --length 160
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_submirror_prefix.py --paired /tmp/qa2r-paired-160.json --signs /tmp/pre-lower.json --length 160 --upper
.venv-ws/bin/python scripts/dommaschk_kam/verify_reflected_physical_prefix.py /tmp/qa2r-forward-160.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-89 |
| Kind | Physical propagation milestone; updates the C2 progress assessment in N-69 |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-66, N-69, N-76, N-79, N-81, N-84 |
| Dependency requirement | Archived signed row sequence, checked Jacobians, central residuals and strict physical signs. |
| Produces | A single physical trajectory from each allowed Q-16 birth over five signed radians with a uniform error and both strict height bounds. |
| Difficulty | Extend the physical chain to the ends of mirror rows 316 and 324, then certify the action over the whole well. |
| Status | Both 160-row chains, the joint passage and both field-strength comparisons passed. |
| Lean evidence | `DommaschkPairedPrefix160.exists_nested_paired`, `.uniform_paired_error`, the two `.below_from_birth` theorems and `DommaschkReflectedPrefix160.trajectory`. |
| Audit evidence | Each concrete theorem uses only `propext`, `Quot.sound` and `Classical.choice`. |
| Last updated | 24 November 2026 |
