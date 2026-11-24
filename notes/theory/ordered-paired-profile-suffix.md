# The ordered paired comparison on the outer 89 signed slabs

On each original QA2R tube at radial label 0.470 and each original tube at 0.478, Lean proves the field drop and the arclength comparison throughout both closed angle intervals
\[
 [59/16,325/64]\quad\text{and}\quad[-325/64,-59/16].
\]
The same angle is used for both physical profiles. For any pair of paths enclosed in the original tubes on these intervals, put \(f_i(\theta)=\lVert B(x_i(\theta),\theta)\rVert\) and \(w_i(\theta)=d\ell_i/d\theta\) in the increasing-angle convention. There, \(f_{478}\le f_{470}-1/18000\), \((3999/4000)w_{470}\le w_{478}\), and both strengths are at most \(17/16\). These are closed-interval conclusions, including every boundary between rows. [Field and arclength definitions](../../PlasmaLean/Design/DommaschkPairedActionProfiles.lean) · [Grouped estimates](grouped-paired-physical-profiles.md)

## The ordered result

The proof consumes all 13 group receipts for the 89 indices 236 through 324. Each index gives two joint comparisons, one from the pair of original forward rows and one from the original backward rows. Four lists therefore contain 356 original archived rows. The entry states at index 236 may be arbitrary. Its immediate predecessor on a through-birth trace can thus be supplied by a separate proof for the initial 236 indices. The append theorems also accept further certified intervals beyond index 324. [Finite signed assembly](../../scripts/dommaschk_kam/verify_grouped_profile_interval.py)

The declarations `forward` and `backward` in `DommaschkComparedInterval236To325` give the synchronized predicates on the two original lists for each direction. The declarations `forward_on_paths` and `backward_on_paths` apply to any two paths which meet their respective original tube bounds. The latter uses positive elapsed time on the backward branch. The joint statement `signed_on_paths` restores the physical angle by substituting \(x(-t),y(-t)\), and quantifies over both intervals on one pair of globally parameterized functions. A birth on the common embedded tori invokes this result when its physical trace reaches the complete interval. [Prefix and path lemmas](../../PlasmaLean/Certificates/PairedPositionFrameObservables.lean) · [Through-birth application](compared-signed-trace-prefixes.md)

## Benchmark and replay

The first complete interval used 130 group-level receipts. Summing their recorded single-process Lean wall times gives 7,002.698 seconds, including their audits. Nine shared harmonic polynomial identities took a further 50.557 seconds and can be reused between groups. The twelve ordered blocks and the final assembly together account for 44.021 seconds. These sums count each distinct recipe once and exclude the ordinary project build. Parallel workers executed independent group checks. The final seven-declaration compilation and audit took 3.935 seconds after the blocks were available and peaked at 5,370,248 KiB RSS.

On the identical joint spatial box for indices 236–246, the nine field values and partial derivatives took 456.313 seconds with the sparse evaluator and 175.210 seconds with seven-harmonic Horner evaluation, a factor of 2.60. The respective peak RSS values were 3,805,688 and 3,974,416 KiB. Both produced exactly the same radial and vertical derivative bounds, and each inclusion in the common enclosing polynomial model is checked by Lean. This comparison reused the fixed harmonic polynomial identities. [Both evaluators](../../scripts/dommaschk_kam/verify_grouped_profile_suffix.py)

The whole 89-index suffix has kernel proofs. At this checkpoint, the separate native campaign had also checked the first 76 consecutive paired indices of the 236-index initial section, whose complete external arithmetic screen passes. The second actual through-birth path had a 160-slab signed checkpoint each way. Applying the finite action-increment criterion on the two full through-birth paths still requires the rest of the initial physical comparisons and propagation of the second birth through the well. [Direct initial-section method](paired-physical-arclength.md) · [Finite increment](finite-radial-action-comparison.md)

~~~bash
lake build PlasmaLean.Design.DommaschkGroupedProfileCompare \
  PlasmaLean.Design.DommaschkGroupedHarmonicGap PlasmaLean.Design.DommaschkComparedTracePrefixes
py=.venv-ws/bin/python
verify=scripts/dommaschk_kam/verify_grouped_profile_suffix.py
$py "$verify" --group 236 --backend sparse --output /tmp/paired236.json
$py "$verify" --group 319 --backend hybrid --output /tmp/paired319.json
$py "$verify" --groups 247 252 258 263 269 274 280 285 291 302 313 \
  --workers 2 --output /tmp/paired-middle.json
$py scripts/dommaschk_kam/verify_grouped_profile_interval.py \
  --reports /tmp/paired236.json /tmp/paired-middle.json /tmp/paired319.json \
  --output /tmp/paired-interval236-325.json
~~~

Each group receipt identifies the two physical witness digests, start and stop, exact squared-strength and arclength margins, and its checked declarations. The interval builder requires a contiguous cover before it imports any proof. All seven exported declarations pass the standard axiom audit with `propext`, `Classical.choice` and `Quot.sound`. The ordered receipt key is `8ca2d6a6de59f5658813082af54594e5394b53450cc607d6baead33fa4f7197d`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-143 |
| Kind | Ordered physical observable bound and through-interval path implication |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-126, N-129, N-132, N-136, N-137 |
| Dependency requirement | Actual signed outgoing tubes at both radial labels, 13 physical group comparisons, affine time bounds and synchronized path evaluation |
| Status | Both signs kernel-checked for the complete 89-row suffix |
| Produces | Four lists with arbitrary initial frames, a paired relation on each signed direction, and the strength and arclength bounds on both closed physical angular intervals |
| Lean evidence | `DommaschkComparedInterval236To325.forward_append`, `.backward_append`, `.forward`, `.backward`, `.forward_on_paths`, `.backward_on_paths`, `.signed_on_paths` |
| Last updated | 25 November 2026 |
