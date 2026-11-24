# One certified QA2R field line through the original birth on all 782 slabs

For the phase-zero QA2R sector at interpolation parameter $u=47/100$, Lean proves that every allowed birth angle $|\phi|\le 2^{-19}$ lies on a physical field line on the full signed angular interval $[-391/64,391/64]$. One pair of certified, nested Q-16 tori supplies all these births. At its original geometric angle $\phi$, the field line takes precisely the interpolated radial and vertical coordinates. It solves the angular field-line ODE throughout the closed interval, including the section and all slab joins. [Full theorem](../../scripts/dommaschk_kam/templates/full_signed_birth.lean.tpl) · [Identification with the original birth by ODE uniqueness](../../PlasmaLean/Design/DommaschkSignedBirthApproach.lean)

Write $y(t)$ for those dimensionless cylindrical position coordinates at signed angle $t$. For either sign $\sigma$, every original row $i=0,\ldots,390$, and every elapsed angle $t\in[i/64,(i+1)/64]$, the numerical reference polynomial $c_{\sigma,i}$ satisfies

$$
\|y(\sigma t)-c_{\sigma,i}(t)\|_2
\;\leq\;\frac{4022059640817442909}{2^{80}}
\;<\;3.327\times10^{-6}.
$$

The row index in this bound selects the exact original signed polynomial. At an interior slab boundary the bound applies to the reference on each side. Lean first takes membership in that row’s physical tube and then checks its individual radius against the common cap. The forward and backward maximum radius numerators are respectively $4022059640817442881$ and $4022059640817442909$. [Physical tube definition](../../PlasmaLean/Certificates/PositionFrameODE.lean) · [Signed row access](../../PlasmaLean/Design/DommaschkSignedObservable.lean)

The same $y$ has all four transverse first mirror contacts. The brackets below use outward angle from the common section on either side. Before the first hit the strength stays strictly below the height. Each signed bracket has exactly one hit, and the outward derivative of the strength at the hit is strictly greater than the stated bound. The allowed birth angle lies inside the interval of strictly smaller strength between the two first contacts at either height. [Transverse contact predicate](../../PlasmaLean/Design/DommaschkSignedMirrorSlope.lean) · [Original mirror certificates, N-95](dommaschk-first-mirrors-from-birth.md)

| Height | Outward-angle bracket on each branch | Outward strength derivative at the hit |
| --- | --- | --- |
| $h_L=5297961656084411/5000000000000000$ | $(316/64,317/64)$ | $>1/(256h_L)$ |
| $h_U=5300546391395933/5000000000000000$ | $(324/64,325/64)$ | $>1/(800h_U)$ |

The proof applies the existing sign and slope implications to the 391-row path itself. Only the first 316 or 324 rows enter the strict pre-contact signs, so the two shorter authenticated sign histories still apply. No equality between separately chosen 325-row and 391-row solutions is assumed. The dimensionless result gives field-line geometry for this one radial interpolation label. The thermal-confinement application still requires work across labels and on guiding-centre dynamics.

## Evidence

| Compiled result | Content key |
| --- | --- |
| 391-slab forward physical chain | `eab47e03e007691135b91d4f412eb07b5eec161064307fd7f5d4e015db17b641` |
| 391-slab backward physical chain | `61eb51657fa7ca994b5af7c4e25b86a9fcf9d4c810ff40a701af5ee4648f84a3` |
| Joined signed passage through the Q-16 section entry | `0359fd624abf0f3fc37453addef690496b6c21524051c5507be3da805d46b2b6` |
| Indexed error, four contacts, and identification at the actual birth | `3fc1ab33bcec8304140af7e42056277bccf1bcb76a786cd56cff89bbf0ea5884` |

The final composition compiled twice in independent output directories with the same content key. The first run took 7.389 seconds and peaked at 8,383,032 KiB RSS, after its parents were available. All four declarations use only `propext`, `Classical.choice` and `Quot.sound`. [Replay driver](../../scripts/dommaschk_kam/verify_full_signed_birth.py)

## Reproduction

Begin with the first 325 physical rows, signs and signed slopes of N-95, and its original transverse contact report `/tmp/qa2r-contacts325.json`. Build the following remaining central and spatial certificates, assemble the two ODE chains, then join the trajectory to the signed signs and slopes. These commands use Bash; the range endpoints are inclusive.

```bash
py=.venv-ws/bin/python
d=scripts/dommaschk_kam
lake build PlasmaLean.Design.DommaschkSignedBirthApproach
$py "$d/verify_sparse_reference_slabs.py" --range 325 390 --workers 2
for bounds in '325 341' '343 383' '385 390'; do
  read -r first last <<< "$bounds"
  $py "$d/verify_shared_forward_jacobians.py" --range "$first" "$last" --workers 2
done
for i in 342 384; do
  $py "$d/verify_explicit_jacobians.py" --range "$i" "$i" --workers 1
done
opts=(--length 391 --shared-from 16 --square-panels 68 --vertical-split 226
      --projected 69 70 71 118 119 171 189 210 225 227 {268..293} 314 315 342 384)
$py "$d/verify_physical_trace_prefix.py" "${opts[@]}" --output /tmp/qa2r-f391.json
$py "$d/verify_backward_physical_prefix.py" "${opts[@]}" --output /tmp/qa2r-b391.json
$py "$d/verify_paired_physical_prefix.py" --forward /tmp/qa2r-f391.json --backward /tmp/qa2r-b391.json --output /tmp/qa2r-p391.json
$py "$d/verify_full_signed_birth.py" --paired /tmp/qa2r-p391.json --contacts /tmp/qa2r-contacts325.json --output /tmp/qa2r-full-birth391.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-110 |
| Title | One certified QA2R field line through the original birth on all 782 slabs |
| Kind | Ground physical trace certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-76, N-84, N-92, N-95, N-97 |
| Dependency requirement | The two original physical chains, their common section birth, the regularity needed for approach uniqueness, and the earlier tube signs and transverse slope bounds at both heights. |
| Produces | The full 391-slab solution in each direction through the actual interpolated birth, an indexed uniform Euclidean error bound and four first mirror contacts on that same path. |
| Difficulty | Retain the original birth and same solution in all claims, including the particular reference polynomial attached to each signed row. |
| Status | Compiled Lean theorem, reproduced in a fresh output directory. |
| Lean evidence | `DommaschkFullSignedBirth.length_rowsFor`, `.indexed_error`, `.contacts`, `.through_birth`. |
| Last updated | 25 November 2026 |
