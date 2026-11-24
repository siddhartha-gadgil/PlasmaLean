# Full signed field-profile comparison at the two radial launches

For each sign of toroidal angle and each of the 325 original angular slabs from the canonical section through \(325/64\), Lean compares every point of the physical tube for \(u_i=0.470\) with every point of the simultaneous physical tube for \(u_o=0.478\). Both strengths lie below or at \(17/16\). The outer field is below the inner field by at least \(1/18000\), and its arclength density is at least \(3999/4000\) times the inner density. The four signed incoming states are arbitrary. [Two-radius observable](../../PlasmaLean/Design/DommaschkPairedActionProfiles.lean) · [Ordered-interval builder](../../scripts/dommaschk_kam/verify_grouped_profile_interval.py)

In particular, suppose the forward and backward restrictions of two paths meet the respective original outgoing tube bounds. Write \(f_i(\theta), f_o(\theta)\) for the strengths of the actual QA2R field at those paths, and \(w_i,w_o\) for the physical arclength densities per radian. The theorem `DommaschkComparedInterval000To325.on_signed_interval` gives, at every physical angle \(-325/64\le\theta\le325/64\),
\[
  f_o(\theta)\le f_i(\theta)-\frac{1}{18000},
  \qquad
  \frac{3999}{4000}w_i(\theta)\le w_o(\theta).
\]
The two paths may continue beyond this interval. On its negative half the proof evaluates each globally signed path at \(-t\) on the original backward elapsed clock. [Signed path gluing](compared-signed-trace-prefixes.md)

## Original rows and spatial estimates

| Indices in each direction | Proof used | Number of indices |
| --- | --- | --- |
| 0–109 | Individual native physical strength and arclength models | 110 |
| 110–175 | Five centered groups | 66 |
| 176–191 | Individual native physical strength and arclength models | 16 |
| 192–235 | Three centered groups | 44 |
| 236–324 | Thirteen centered groups from N-143 | 89 |

The 126 individual paired proofs use the original action columns of both physical labels. The other 199 indices use the common-angle mean-value and arclength bounds on 21 groups of separately enclosed curves. Together these give 650 signed comparisons on 1,300 original archived rows. The interval proof preserves the entry and exit frames and includes the common endpoints of consecutive slabs. [Individual comparison](paired-physical-arclength.md) · [Grouped comparison](grouped-paired-physical-profiles.md) · [Outer interval evidence](ordered-paired-profile-suffix.md)

The eight new groups use the half-open index ranges \([110,124),[124,137),[137,150),[150,164),[164,176),[192,209),[209,224),[224,236)\). A reference polynomial retains the shared time dependence on each group. Both paths may occupy their respective spatial error rectangles independently at that time. Exact arithmetic first selected the ranges, and Lean checked the physical polynomial and derivative identities, both error charges and every individual signed row inclusion. [Group verifier](../../scripts/dommaschk_kam/verify_grouped_profile_suffix.py)

The eight new grouped packages and their 81 distinct dependencies account for 4,325.5 seconds summed over individually recorded compilations. The final 325-row join took 7.314 seconds at 7.91 GiB peak resident memory. That final measurement excludes the interval-block builds and the preceding arithmetic checks.

## Application and replay

The ground result supplies the complete paired field and arclength premise of the finite radial action comparison. Applying it to the two actual births additionally uses their signed through-birth trajectories on the common nested embedded tori and the physical first wells at the specified heights. The field comparison itself holds for every enclosed pair independently of the launch angle or selected mirror height. [Finite action change](finite-radial-action-comparison.md) · [Pilot calibration on the common tori](common-torus-pilot-action.md)

~~~bash
lake build PlasmaLean.Design.DommaschkGroupedProfileCompare \
  PlasmaLean.Design.DommaschkGroupedHarmonicGap PlasmaLean.Design.DommaschkComparedTracePrefixes
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
$py "$dir/verify_native_profile_campaign.py" --range 0 109 --workers 3 --output /tmp/direct000-109.json
$py "$dir/verify_native_profile_campaign.py" --range 176 191 --workers 2 --output /tmp/direct176-191.json
$py "$dir/verify_grouped_profile_suffix.py" --spans 110:124 124:137 137:150 150:164 164:176 \
  192:209 209:224 224:236 --workers 2 --output /tmp/compared-eight-groups.json
# Use N-143's three suffix manifests (236, the middle eleven groups, and 319).
$py "$dir/verify_grouped_profile_interval.py" --range 0 325 \
  --reports /tmp/direct000-109.json /tmp/direct176-191.json /tmp/compared-eight-groups.json \
  /tmp/paired236.json /tmp/paired-middle.json /tmp/paired319.json \
  --evidence-output /tmp/all325-compared-row-map.json --output /tmp/all325-compared.json
~~~

The ordered input map lists 147 unique proof receipts and maps all 325 indices back to those files. Missing signed comparisons and conflicting overlap are rejected before assembly. The final key is `a406b9f37fd9c31b175cc458625354738aa13b69046e5f097b27091c98e04fe5`. All eight declarations have the standard axiom audit `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-146 |
| Kind | Complete paired physical observable certificate and signed path implication |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-126, N-132, N-136, N-137, N-143 |
| Dependency requirement | The two original signed witness packets, certified field and arclength models, and matched clocks at both radii |
| Status | Complete kernel-checked paired-row cover and closed-interval implication for any two enclosed paths |
| Produces | Both signed physical row chains and the pointwise field-profile premise through the pilot's last mirror slab |
| Lean evidence | `DommaschkComparedInterval000To325.forward_append`, `.backward_append`, `.forward`, `.backward`, `.forward_on_paths`, `.backward_on_paths`, `.signed_on_paths`, `.on_signed_interval` |
| Last updated | 25 November 2026 |
