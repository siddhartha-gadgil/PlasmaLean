# Physical action enclosure between the first upper mirrors

For every admitted phase-zero QA2R birth at launch parameter $u=47/100$ and birth angle $|\phi|\le 2^{-19}$, the one-way action $J_U$ on the actual field line between its first mirrors at the upper certified height satisfies

$$
\frac{553}{2000}<J_U\leq\frac{1146552112157123}{844424930131968}
<\frac{6799610938322487}{5000000000000000}.
$$

The interval is dimensionless. Its upper end is approximately $1.3577904574394057$, below the prescribed action target by approximately $0.002131730225091734$. The theorem follows the same birth, section point and physical trajectory through the complete quadrature and both mirror identifications. [Exact rectangle mass](../../PlasmaLean/Design/DommaschkActionArchiveMass.lean) · [First-well theorem](../../PlasmaLean/Design/DommaschkNativeWellAction.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-101 |
| Title | Physical action enclosure between the first upper mirrors |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-94, N-95, N-96 |
| Dependency requirement | A common Q-16 birth and signed trajectory through 326 slabs in each direction, first-contact and strict core-action proofs on that trajectory, and the 650 original action blocks. |
| Produces | Strict lower and upper bounds for the true upper-height first-well action, the exact upper rectangle sum, and a reusable block-cover checker. |
| Difficulty | Preserving the original rounding, negative clock, arclength density, and chosen trajectory across all 31,200 closed panels. |
| Status | Verified after end-to-end kernel audit. |
| Lean evidence | `DommaschkNativeFirstWellComplete326.from_birth`, `DommaschkNativeCover326L000R650.path_cover`, `DommaschkActionArchiveMass.closed_upper`. |
| Audit evidence | The on-demand compiled applications report only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Statement and evidence

Write $X(t)=(R(t)\cos t,R(t)\sin t,z(t))$, $\beta(t)=\lVert B(X(t))\rVert$, and $w(t)=\lVert X'(t)\rVert$. The certified height is $h_U=5300546391395933/5000000000000000$. For an ordered interval define $J(a,b)=\int_a^b w(t)\sqrt{2(h_U-\beta(t))}\,dt$, with the nonnegative real square root and value zero in forbidden regions. The chosen signed trajectory reaches $\pm326/64$ so the ordinary Cartesian derivative exists at every closed panel endpoint through $\pm325/64$.

**[Lean]** The first upper mirrors satisfy $l\in(-325/64,-324/64)$ and $r\in(324/64,325/64)$. On $(l,r)$ the field strength is strictly below $h_U$, with equality at each end. The trajectory also retains its transverse first-contact data at the lower certified height. Integration of the nonnegative clipped action gives
$$
J(-324/64,324/64)\le J(l,r)\le J(-325/64,325/64).
$$
The established strict action floor on $[-316/64,316/64]$ gives the strict lower bound. The 255-node proof tree covers all 31,200 original panels in chronological order. Its 650-block certificate bounds the last, padded integral from above. [First physical mirrors](dommaschk-first-mirrors-from-birth.md) · [Core action floor](dommaschk-first-well-action-floor.md)

**[Lean]** The archive bounds the density in units of $2^{-20}$, the positive part of squared parallel speed in units of $2^{-26}$, and its speed in units of $2^{-20}$. All 48 panels of outward row $i$ realize the original chronological blocks $325+i$ and $324-i$. On the negative branch, panel $j$ uses digit $47-j$ at physical angle $-t$. A single physical Taylor model per row covers both reflected outgoing tubes. Each 80-bit coefficient is rounded outward to 52 bits for interval Horner evaluation. The absolute model error is rounded upward and added to both sides of the resulting enclosure. The intermediate integer square roots are checked against their adjacent integers, as are the published speed digits. [Native panel arithmetic](dommaschk-native-action-panels.md) · [Signed chronological cells](../../scripts/dommaschk_kam/verify_native_path_cells.py)

**[Lean]** The sum of the 31,200 integer density-speed products is exactly $4586208448628492$. Multiplying by the angular panel width $1/3072$ and both digit units $2^{-20}$ gives the upper bound $4586208448628492/(3072\cdot 2^{40})$. The gap between this upper bound and the target is exactly $274671348019911459639037/128849018880000000000000000$. This is the below-target sign at the inner radial endpoint of the phase-zero upper-height bracket $(0.470,0.478)$. The other seven physical endpoint comparisons remain open. [Local action-graph specification](dommaschk-local-action-graphs.md)

The reusable theorem `MirrorActionQuadrature.exact_upper_mass` applies to any list of upper-bound blocks with a physical cover, continuous field strength and density, and nonnegative arclength density. Every rational number above the scaled integer sum is an admissible strict target for the packet checker. If the physical integral exceeded the sum, a rational strictly between them would contradict packet soundness. [Exact upper-mass lemma](../../PlasmaLean/Certificates/MirrorActionExactMass.lean)

## Dependencies and scope

N-60 records the phase sectors, mirror heights and the target defining the four prospective fixed-action graph arcs. N-94 identifies the original density and speed digits on the traced pilot field. N-95 grounds the first physical contacts, and N-96 gives the strict inner action floor. This result closes the upper quadrature inequality for the phase-zero $u=47/100$ endpoint. The other endpoint inequalities and the continuous radial parameter dependence are separate hypotheses of the graph construction. The time coordinate here is geometric toroidal angle. [Action-graph design](dommaschk-local-action-graphs.md) · [Native panel identity](dommaschk-native-action-panels.md) · [Signed physical contacts](dommaschk-first-mirrors-from-birth.md) · [Core floor](dommaschk-first-well-action-floor.md)

## Reproduce

Start from the authenticated pilot paired-trajectory receipt with 326 slabs each way and its two-height transverse-contact and 316-slab lower-height sign receipts. Follow the N-95 signed replay with a length of 326. The model campaign and the panel consumer may run together. The example uses four workers. Two independent compilations of the final theorem produced the content key below. [Signed trajectory and contacts](dommaschk-first-mirrors-from-birth.md) · [Chronological cover verifier](../../scripts/dommaschk_kam/verify_native_action_archive.py) · [Final theorem producer](../../scripts/dommaschk_kam/verify_native_first_well_action.py)

```sh
lake build PlasmaLean.Design.DommaschkNativeWellAction \
  PlasmaLean.Design.DommaschkNativeActionReflection \
  PlasmaLean.Design.DommaschkFirstMirrorWell PlasmaLean.Design.DommaschkSignedActionFloor \
  PlasmaLean.Design.DommaschkNativeActionColumns \
  PlasmaLean.Certificates.NativeActionArchivePair

py=.venv-ws/bin/python
src=scripts/dommaschk_kam
"$py" "$src/verify_signed_action_floor.py" --paired /tmp/plasma-action-signed326.json \
  --submirror /tmp/plasma-action-lower326.json --output /tmp/plasma-native-lower-core326.json
"$py" "$src/verify_native_action_campaign.py" --range 0 324 --workers 4 \
  --output /tmp/dktrace-native-action-campaign.json
"$py" "$src/verify_native_path_cells.py" --range 0 324 --workers 4 \
  --output /tmp/plasma-native-path-cells-adaptive.json
"$py" "$src/verify_native_action_archive.py" --paired /tmp/plasma-action-signed326.json \
  --output /tmp/plasma-native-archive326.json
"$py" "$src/verify_native_first_well_action.py" --paired /tmp/plasma-action-signed326.json \
  --contacts /tmp/plasma-action-contacts326.json --floor /tmp/plasma-native-lower-core326.json \
  --cover /tmp/plasma-native-archive326.json --output /tmp/plasma-native-first-well326.json
```

| Receipt | Content key |
| --- | --- |
| Paired trajectory | `9f34e32228b00ca614451559518ddaa4ce80bdb426e6059575028e544d8a11eb` |
| Both transverse first mirrors at both heights | `e2a9c87b1a8404a1a548abe23e62227fa7be768673e9ddf529e29ce07583fa24` |
| Upper-height core floor | `ca37a7923fe0881d8eae62dc73e435837dd1ea64b83ef426d51ecc645e5a4649` |
| Original 650-block cover | `43a3610026b189c2378b760832d7ca138e565fd712d9400b684a26993774a637` |
| First-well action enclosure | `e6e025e1ccba98eb4df7de15697cf820b6564dd88475764027cea45ddc89b4a5` |
