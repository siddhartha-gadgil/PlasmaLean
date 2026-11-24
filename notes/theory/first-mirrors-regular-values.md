# First mirror heights from topology and the area formula

A continuous field-strength profile with a quiet interior and a high exterior cap has a first mirror at every intermediate height. The mirror can change discontinuously with height. Its time always increases strictly with height and is continuous from below. For a differentiable field profile almost every height gives a simple mirror on both signed clocks. The one-dimensional area formula gives a quantitative way to discard the heights with shallow crossings using just the bracket lengths. [First-contact and measure theorems](../../PlasmaLean/Theory/Kinetic/FirstMirrorRegularValues.lean)

## First contacts and exceptional heights

Let $f$ be the strength on one outward clock. Assume $0≤a<b$, $f(t)<L$ for $0≤t≤a$, $f$ is continuous on $[a,b]$, and $U<f(b)$. For each $h∈[L,U]$ there is a uniquely determined earliest contact $τ(h)∈(a,b)$ with $f(τ(h))=h$ and $f(t)<h$ for every earlier nonnegative time. There may be other contacts later. This construction makes no monotonicity assumption on $f$. [Earliest hit in a bracket](../../PlasmaLean/Theory/Fields/TrajectorySlabObservable.lean)

The contacts at distinct heights are strictly ordered by the intermediate value theorem. If $x<τ(h)$ lies in the bracket, the maximum of $f$ on $[a,x]$ is strictly less than $h$. Heights approaching $h$ from below therefore have contacts after $x$ and no later than $τ(h)$. It follows that $τ$ is left-continuous on the closed height band. Its discontinuities form an at most countable set. The distinction between left and right matters. A continuous profile that rises from 0 to 1 on $[0,1]$, falls to 0 on $[1,2]$, and then rises with unit slope has $τ(1)=1$, while $τ(h)=2+h$ just above 1.

For differentiable profiles, the critical values have zero Lebesgue measure by Sard’s lemma in dimension one. At any first contact with a nonzero derivative the outward derivative is positive, since all earlier values were below the level. Two signed profiles therefore have simple first contacts simultaneously at almost every height. The vector-field form takes the norms of two differentiable fields along their curves. A positive lower band height guarantees differentiability of the norm at all relevant preimages. The exceptional set may depend on the chosen curves. [Formal two-sided theorem](../../PlasmaLean/Theory/Kinetic/FirstMirrorRegularValues.lean)

## A numerical height-measure bound without checking each slope

Suppose the two outward brackets have widths $w_+$ and $w_-$. If the scalar profiles are differentiable in the open brackets and $m≥0$, the Lebesgue outer measure of heights at which either first-contact slope has magnitude at most $m$ is at most $m(w_++w_-)$. On a single clock those heights lie in the image of the set where $|f'|≤m$. The area formula bounds that image measure by the integral of $|f'|$ on the set, at most $m$ times its length. The union bound combines the two clocks. Consequently the measure of heights with both outward slopes greater than $m$ is at least $U-L-m(w_++w_-)$. This argument permits oscillations anywhere in either bracket. [Quantitative bound](../../PlasmaLean/Theory/Kinetic/FirstMirrorRegularValues.lean)

For the archived QA2R band, take $m=1/1250$ and widths at most $10/64$ on each clock. The bad heights have measure at most $1/4000$. The good heights have measure at least

$$
667367655761/2500000000000000 = 0.0002669470623044 ,
$$

which is **at least 51.639% of the height band**. Lean checks the exact lower bound and the strict majority inequality. To apply it to a new launch requires a true passage, an interior field bound up to each bracket, the high caps and differentiability of its two physical strength profiles. The fraction here weights height uniformly for a fixed field line. Thermal birth weights and radial evolution require separate results. [Exact QA2R height budget](../../PlasmaLean/Design/DommaschkFirstContactHeightBudget.lean) · [Derivative estimates valid at every height on the initial pilot](dommaschk-mirror-height-band.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-159 |
| Kind | Candidate-independent first-contact topology and a measure estimate with a QA2R specialization |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | The first-contact theorem for trajectory slabs and the one-dimensional area inequality in Mathlib |
| Dependency requirement | A capped scalar profile on each clock, differentiability for the measure conclusions, and a known height band and bracket widths for the numerical specialization |
| Produces | Strictly ordered, left-continuous earliest mirror times, simultaneous almost-every-height transversality and an explicit measure budget for shallow contacts |
| Status | Generic Lean theorem and exact conditional numerical specialization |
| Lean evidence | `FirstMirror.Family.continuous_from_below`, `FirstMirror.exists_ae_field_mirrors`, `FirstMirror.two_sided_good_heights`, `DommaschkFirstContactHeightBudget.good_height_measure`, `.majority` |
| Last updated | 25 November 2026 |
