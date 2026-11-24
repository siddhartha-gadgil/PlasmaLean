# Four first mirror contacts on a physical field line from a Q-16 birth

Every admitted phase-zero-sector birth at interpolation parameter $u=0.470$ reaches its section. One signed physical field line through that section state reaches the first mirror at each of the two archived heights on either side. The following are open intervals in outward geometric angle, in radians. [Signed physical theorem generator](../../scripts/dommaschk_kam/verify_signed_mirror_passage.py)

| Height | First contact in each direction | Lower bound for outward derivative of squared field strength at contact |
| --- | --- | --- |
| $h_L=5297961656084411/5000000000000000$ | $(316/64,317/64)$ | $1/128$ |
| $h_U=5300546391395933/5000000000000000$ | $(324/64,325/64)$ | $1/400$ |

Between the section and each first contact, field strength is strictly below the corresponding height. Each contact is unique in its own closed bracket. The field-strength derivative in the outward coordinate is greater than $1/(256h_L)$ or $1/(800h_U)$ respectively. On the negative branch the outward clock runs opposite to increasing geometric angle. [First-contact and slope definitions](../../PlasmaLean/Design/DommaschkSignedMirrorSlope.lean)

The proof follows 325 physical slabs on each side, covering $[-325/64,325/64]$. The dimensionless position error from the moving references is at most $4022059640817442909/2^{80}<3.327\times10^{-6}$. The two chains start from the same section state. Combining their enclosures with the ordered strict signs and the four local slope bounds rules out all earlier contacts. The original 96 launch-adjacent action panels and the panel at the far negative end also hold on this field line. [Ordered signs](dommaschk-complete-pre-mirror-signs.md) · [Local slope certificates](dommaschk-transverse-physical-mirror-brackets.md) · [Same-path action](dommaschk-signed-action-integral.md)

The result is for one interpolation parameter and two dimensionless heights. A thermal C2 application additionally needs a band of births and pitches, action variation across it, and the physical guiding-centre and return map estimates.

## Reproduce

The commands use the workstation environment. N-77, N-81 and N-84 give the physical brackets, raw slope and pre-mirror sign reports. The physical prefix builders reuse the exact spatial Jacobians and central reference certificates. Row 68 uses a square subdivision, row 226 a vertical split, and the listed rows use projected rectangles.

```bash
py=.venv-ws/bin/python
scripts=scripts/dommaschk_kam
opts=(--length 325 --shared-from 16 --square-panels 68 --vertical-split 226 --projected 69 70 71 118 119 171 189 210 225 227 268 269 270 271 272 273 274 275 276 277 278 279 280 281 282 283 284 285 286 287 288 289 290 291 292 293 314 315)
$py "$scripts/verify_physical_trace_prefix.py" "${opts[@]}" --output /tmp/qa2r-f325.json
$py "$scripts/verify_backward_physical_prefix.py" "${opts[@]}" --output /tmp/qa2r-b325.json
$py "$scripts/verify_paired_physical_prefix.py" --forward /tmp/qa2r-f325.json --backward /tmp/qa2r-b325.json --output /tmp/qa2r-p325.json
$py "$scripts/verify_signed_submirror_prefix.py" --length 316 --paired /tmp/qa2r-p325.json --signs /tmp/pre-lower.json --output /tmp/qa2r-lower325.json
$py "$scripts/verify_signed_submirror_prefix.py" --length 324 --upper --paired /tmp/qa2r-p325.json --signs /tmp/pre-lower.json /tmp/pre-upper.json --output /tmp/qa2r-upper325.json
for i in 316 324
do
  $py "$scripts/verify_signed_mirror_slopes.py" --slopes "/tmp/qa2r-slope-$i.json" --output "/tmp/qa2r-signed-slope-$i.json"
done
$py "$scripts/verify_signed_mirror_passage.py" --brackets /tmp/qa2r-brackets.json --paired /tmp/qa2r-p325.json --lower-prefix /tmp/qa2r-lower325.json --upper-prefix /tmp/qa2r-upper325.json --output /tmp/qa2r-first325.json
$py "$scripts/verify_signed_mirror_passage.py" --brackets /tmp/qa2r-brackets.json --paired /tmp/qa2r-p325.json --lower-prefix /tmp/qa2r-lower325.json --upper-prefix /tmp/qa2r-upper325.json --slopes /tmp/qa2r-signed-slope-316.json /tmp/qa2r-signed-slope-324.json --output /tmp/qa2r-contacts325.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-95 |
| Kind | Ground physical mirror-contact theorem |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-69, N-77, N-81, N-84, N-92 |
| Dependency requirement | The two signed physical chains, all earlier strict signs and both local derivative bounds. |
| Produces | Four earliest transverse mirror contacts on the same physical field line for each admitted birth. |
| Difficulty | Extend the physical well and action comparisons across the whole family of births and heights. |
| Status | Compiled on the workstation. |
| Lean evidence | `DommaschkTransverseMirrorBirth325.contacts_from_birth`, `DommaschkSignedActionContacts325.from_birth`. |
| Audit evidence | Signed chain `e613201e5062`, first transverse contacts `80d9224f5eadb156877cfdd2568aa50d0820c61a65147b864800aecbe0201ff7`, joint physical action `46d84e5fed8b`. Standard three axioms. |
| Last updated | 25 November 2026 |
