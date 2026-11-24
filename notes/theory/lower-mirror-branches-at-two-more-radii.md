# First lower-height mirror brackets at two further phase-zero radii

At $u=0.523$ and $0.531$, a physical signed trajectory through the corresponding original QA2R slab tubes and beyond the lower bracket has a simple first mirror on each side at the archived lower height $h_L$. The earlier field values are strictly below $h_L$. On each bracket the outward derivative of $|B|^2$ is strictly greater than $1/400$, including at the shared slab boundary. At contact the outward strength derivative exceeds $1/(800h_L)$. [Physical branch construction](../../scripts/dommaschk_kam/verify_secondary_mirror_band.py) · [Earlier field clearance](outer-phase-zero-submirror-births.md)

| Phase-zero label | Earlier slabs on each clock | First lower-height times, in radians | Upper-height cap bracket, in radians |
| --- | ---: | --- | --- |
| 0.523 | 322 | $(322/64,324/64)$ | $(335/64,336/64)$ |
| 0.531 | 323 | $(323/64,325/64)$ | $(336/64,337/64)$ |

The proof combines a signed exclusion over the entire prehistory, the signs at the bracket ends, and two closed-slab derivative estimates for each radius on each clock. The upper-height cap signs also passed on both clocks at both radii. A band-wide branch needs the intervening slopes or another regularity argument. At this checkpoint the attached physical birth paths reach $48/64$ and $16/64$ radians each way at these two labels, respectively. Continuing the trajectories into their brackets will remove the remaining passage hypothesis. [Original birth trajectories](common-original-birth-margins.md) · [Second launch with the passage completed](two-physical-first-well-actions.md)

| Original launch | Both-height signed caps | First lower-height branch implication |
| --- | --- | --- |
| 0.523 | `0176fe1d98492447301dbb5f9cc0e3a1d2bf9e2ae13c90610156e12a7a045da5` | `b7e264f34835ffe660b078dca32486e979e0d5b920d5b5b3f081fd7007c5d245` |
| 0.531 | `fbdae36efa2a56b3d6b8f2eed09965cc66b23640153b640468a4ca2165a649ef` | `ec80c66d8f30f5e36dc74b6fa15f154604644bdbbca83308897965d5044f1bfe` |

## Replay

Use the signed incoming exclusion receipts from the field-margin campaign. The same generator produces either a conditional theorem or an attachment to a matching signed trajectory via `--signed`.

~~~bash
for launch in 523 531; do
  first=322
  if [ "$launch" = 531 ]; then first=323; fi
  .venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_caps.py \
    --launch "$launch" --output "/tmp/plasma-next-caps$launch.json"
  .venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_slopes.py \
    --launch "$launch" --rows "$first" "$((first+1))" --output "/tmp/plasma-n151-lowerslopes$launch.json"
  .venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_band.py \
    --launch "$launch" --lower-only --caps "/tmp/plasma-next-caps$launch.json" \
    --slopes "/tmp/plasma-n151-lowerslopes$launch.json" \
    --exclusion "/tmp/plasma-n131-q0r$launch-exclusion.json" \
    --output "/tmp/plasma-n151-firstlower$launch.json"
done
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-151 |
| Kind | Two conditional physical first-mirror branches and upper-height cap certificates |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-115, N-126, N-131 |
| Dependency requirement | Original signed caps, complete prehistories, two lower bracket slope certificates and a physical through-passage |
| Produces | A simple first contact at the lower archived height on both clocks for each of two additional launches |
| Status | The prehistory, cap and lower-bracket slope inputs are kernel verified. The physical trajectory from each original birth through the bracket remains open. |
| Lean evidence | `DommaschkQ0R523MirrorBranch324.of_signed_chain` and `DommaschkQ0R531MirrorBranch325.of_signed_chain` |
| Audit evidence | Both branch packages use propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
