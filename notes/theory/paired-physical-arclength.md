# Correlated arclength bounds at the two QA2R radii

On the last pilot mirror slab, Lean proves the complete pointwise comparison needed by N-126. For every elapsed angle $t\in[324/64,325/64]$ and all points in the two original signed outgoing tubes at that angle,

$$
f_{478}\le f_{470}-1/18000,\qquad
(3999/4000)\,w_{470}\le w_{478},\qquad
f_{470},f_{478}\le 17/16 .
$$

Here $f$ is the physical QA2R field strength and $w$ is arclength per radian. The theorem applies separately to the physical angles $t$ and $-t$, allowing every pair of predecessor frames. It joins the verified squared-strength drop from N-129 to two new field ceilings and an arclength comparison. The arclength comparison and both ceilings also hold on row 296, where the external sparse-polynomial screen found the smallest arclength margin. [Arclength and strength identities](../../PlasmaLean/Design/DommaschkPairedArcRatio.lean) · [Signed physical join](../../scripts/dommaschk_kam/verify_paired_profile_join.py)

## Comparing the two weights

Write $D$ for the positive angular denominator, $R$ for cylindrical radius, and $A=n_R^2+n_z^2$ for the squared transverse numerator. The physical field identity gives $D^2 w^2=R^2D^2+A$. With $k=3999/4000$, Lean checks the following expression at **one common normalized time** for both tubes:

$$
\bigl((R_o-R_i)(R_o+R_i)+(1-k^2)R_i^2\bigr)D_i^2 D_o^2
+A_oD_i^2-k^2 A_iD_o^2
= D_i^2 D_o^2(w_o^2-k^2w_i^2).
$$

The Taylor models include the original outgoing spatial remainder on each signed row. The inner and outer coordinates can vary independently within their respective tubes. The time shared by their angular harmonics is retained in each product and sum. Positivity of both denominators and nonnegativity of physical arclength give $kw_i\le w_o$. At row 324 the certified lower bound on the cleared margin is $9446828973525429341/302231454903657293676544$. At row 296 it is $572594193972424413/37778931862957161709568$. [Original sparse-field producer](../../scripts/dommaschk_kam/verify_paired_arc_ratio.py)

The native packets for the physical action offer a second calculation. Their checked columns give $U=R^{16} f^2=D^2 w^2$ and $N=R^{16}(h_{\rm upper}^2-f^2)$. Thus $U_oD_i^2-k^2 U_iD_o^2$ certifies the arclength comparison. The same columns give both field ceilings. A compensated cross-product of $N_i,N_o,R_i^{16},R_o^{16}$ can additionally certify the squared field drop. Both sign proofs reuse the model files used independently for action integration. [Native comparison](../../PlasmaLean/Design/DommaschkNativePairedProfiles.lean) · [Native packet consumer](../../scripts/dommaschk_kam/verify_native_paired_profiles.py)

## Coverage and remaining work

The **exact external screen** succeeds for arclength and both ceilings on all 325 indices in both directions. The native direct comparison additionally succeeds for the strength drop on rows 0 through 235. The 89 rows from 236 through 324 require a sharper strength estimate by this method. Row 324 has the joined kernel proof, and N-128 separately locates both launch-adjacent paths on a common pair of embedded surfaces. The all-row kernel campaign records each signed pair's checked declarations and distinguishes a complete comparison from arclength and field ceilings alone. An action increment over the complete neighboring well requires its own ordered coverage and its physical mirror passage. [Launch comparison, N-128](paired-physical-launch-profiles.md) · [Finite increment criterion, N-126](finite-radial-action-comparison.md)

## Replay

```bash
lake build PlasmaLean.Design.DommaschkPairedArcRatio PlasmaLean.Design.DommaschkNativePairedProfiles
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
$py "$dir/verify_paired_arc_ratio.py" --screen --output /tmp/plasma-paired-arc-screen325.json
$py "$dir/verify_native_paired_profiles.py" --screen --output /tmp/plasma-native-paired-screen325.json
$py "$dir/verify_paired_arc_ratio.py" --row 296 --backend sparse --output /tmp/plasma-paired-arc296.json
$py "$dir/verify_paired_arc_ratio.py" --row 324 --backend shared --output /tmp/plasma-paired-arc324.json
$py "$dir/verify_paired_profile_join.py" --arc /tmp/plasma-paired-arc324.json \
  --strength /tmp/plasma-centered-strength324.json --output /tmp/plasma-paired-profiles324.json
$py "$dir/verify_native_paired_profiles.py" --row 0 --output /tmp/plasma-native-paired-profile000.json
$py "$dir/verify_native_profile_campaign.py" --workers 3 --reserve-gib 32 --reserve-cpus 2 \
  --output /tmp/plasma-paired-native-campaign.json
```

The arclength and ceiling keys are `00e272ba1d7bf0b8aa5b0eb29abc6d25b88a557e515ebede406aaac59c667e7d` for row 296 and `be71cc3c616c6a28ea187e0ad78221eb1c71ee09eb6ffbe60eecf4b490804042` for row 324. The joined row-324 key is `5195a2913abc946dcba16c4ae9425d43ec21de8566826310de176402e986b9f1`. Its physical comparison and axiom audit took 3.001 seconds and peaked at 3,980,384 KiB after the component proofs were available. The native row-zero comparison key is `b5675c955709c729ba8e3d8ee6b5d6df617cdd0b45514f09a4a8e4213c37615f`. The theorem audits reported `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-132 |
| Title | Correlated arclength bounds at the two QA2R radii |
| Kind | Physical observable theorem, certificate and replay |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-94, N-126, N-128, N-129 |
| Dependency requirement | Signed outgoing tube coordinates, exact QA2R field and arclength identities, and the centered squared-strength separation for the last row. |
| Produces | The complete signed comparison on the upper-mirror slab, arclength at its smallest screened sparse margin, and two reusable verification methods for the paired profiles. |
| Difficulty | Preserve common-angle cancellation across nearby orbits, track both independent spatial errors and identify the actual arclength on both physical clocks. |
| Status | Ground kernel comparisons at the cited rows. All-row arithmetic was checked externally and the remaining individual kernel comparisons have a resumable producer. |
| Lean evidence | `DommaschkPairedArcRatio.physical_identity`, `.compare`, `.compared_of_squared`, `DommaschkNativePairedProfiles.native_ratio`, `.native_field`, `DommaschkComparedProfiles324.forward`, `.backward`, `DommaschkPairedArcRatio296.forward_bounds`, `.backward_bounds`. |
| Last updated | 25 November 2026 |
