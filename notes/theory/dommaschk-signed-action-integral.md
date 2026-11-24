# Physical action near birth on a six-radian field line

For every admissible phase-zero birth at interpolation parameter 0.470, one physical field line reaches signed angles $-3$ and $3$ radians and stays in all 192 original tubes each way. Its dimensionless position error is bounded by $2678772121456213228/2^{80}<2.216\times10^{-6}$. Its strength stays strictly below the lower and upper mirror heights throughout the interval. [Signed path producer](../../scripts/dommaschk_kam/verify_paired_physical_prefix.py) · [Height history](../../scripts/dommaschk_kam/verify_signed_submirror_prefix.py)

On this **same field line** the 96 archived action panels in $[-1/64,1/64]$ enclose the actual arclength density and clipped squared speed. At the upper archived height $h_U$, the dimensionless contribution from that central interval satisfies

$$\int_{-1/64}^{1/64}\left\lVert\frac{dX}{dt}\right\rVert\sqrt{2(h_U-|B(X(t))|)_+}\,dt < 0.005587.$$

The proof establishes integrability for the actual Cartesian derivative and compares the integrand to a constant. The density is at most $1046878/2^{20}$ and the squared speed at most $2151939/2^{26}$. The latter is less than $(179071/10^6)^2$. Multiplying these bounds for density and speed by the angular width $1/32$ gives the stated strict inequality. [General bound for the integral](../../PlasmaLean/Certificates/MirrorActionBlockBounds.lean)

The proof establishes the local action bounds for any sufficiently extended signed path with the checked first rows. This quantifier preserves the trajectory already chosen for a level or mirror-contact proof. A path that also reaches backward row 324 with that row's checked data satisfies the first panel in chronological order. The whole-well action and an estimate across birth labels remain open. [Same-trajectory proof](../../scripts/dommaschk_kam/templates/signed_action_physical.lean.tpl) · [Original two action blocks](dommaschk-two-physical-action-blocks.md)

## Reproduce

Use the first chronological cell from N-86, the two launch blocks from N-90, and the lower-height pre-mirror sign report from N-84. The commands below use the workstation virtual environment.

```sh
py=.venv-ws/bin/python
scripts=scripts/dommaschk_kam
lake build PlasmaLean.Certificates.MirrorActionBlockBounds PlasmaLean.Design.DommaschkSignedMirrorSlope
for dir in forward backward
do
  generator=verify_physical_trace_prefix.py
  if test "$dir" = backward; then generator=verify_backward_physical_prefix.py; fi
  $py "$scripts/$generator" --length 192 --shared-from 16 --square-panels 68 --projected 69 70 71 118 119 171 189 --output "/tmp/qa2r-$dir-192.json"
done
$py "$scripts/verify_paired_physical_prefix.py" --forward /tmp/qa2r-forward-192.json --backward /tmp/qa2r-backward-192.json --output /tmp/qa2r-paired-192.json
$py "$scripts/verify_signed_submirror_prefix.py" --paired /tmp/qa2r-paired-192.json --signs /tmp/pre-lower.json --length 192 --output /tmp/qa2r-below-192.json
$py "$scripts/verify_signed_action_prefix.py" --blocks /tmp/qa2r-birth-blocks.json --first-cell /tmp/qa2r-first-cell.json --paired /tmp/qa2r-paired-192.json --below /tmp/qa2r-below-192.json --output /tmp/qa2r-action-192.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-92 |
| Kind | Physical trace and integral on one trajectory |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-84, N-86, N-89, N-90 |
| Dependency requirement | Signed physical path, lower-height tube signs and the two original action blocks around the same section. |
| Produces | A six-radian physical birth trajectory, both strict height bounds and an unconditional upper integral over its launch-adjacent 96 panels. |
| Difficulty | Extend the original physical action covers across the rest of the well. |
| Status | Six-radian signed trajectory, height history, both action covers and integral compiled and replayed on the workstation. |
| Audit evidence | Joint theorem key `209dae555c25fb7b6fa410af0a8acf92e8657bc339798850e02bdbd83ad8e493`. Only the standard three axioms. |
| Lean evidence | `DommaschkSignedActionBelow192.from_birth`, `DommaschkSignedActionBounds.launch`, `MirrorActionQuadrature.action_le_uniform`. |
| Last updated | 25 November 2026 |
