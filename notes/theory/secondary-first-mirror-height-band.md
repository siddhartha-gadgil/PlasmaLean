# A common first-mirror branch at the second phase-zero launch

Consider the $239/500$ launch radius of QA2R at section zero and the two heights $h_L=5297961656084411/5000000000000000$ and $h_U=5300546391395933/5000000000000000$. On each of the ten closed slabs from $317/64$ through $327/64$, in both outward directions, the squared field magnitude on an actual enclosed ODE solution has derivative strictly greater than $1/400$. N-121 shows that the earlier 317 slabs stay below $h_L$. N-115 supplies a strictly super-$h_U$ exterior cap at $327/64$. [Exclusion certificates](secondary-qa2r-submirror-exclusion.md) · [Mirror caps](secondary-qa2r-mirror-brackets.md)

For a single joined physical trajectory following those archived rows and extending beyond $327/64$, each half of the line therefore has a first mirror time $\tau(h)\in(317/64,327/64)$ for **every** height $h\in[h_L,h_U]$. The field magnitude stays below $h$ before this time and exceeds $h$ up to the outer endpoint afterwards. Each branch is strictly increasing and continuous. At the root the outward derivative of field magnitude exceeds $1/(800h)$. For any two heights in the band one has

\[
\tfrac1{400}|\tau(h)-\tau(h')|\le |h^2-h'^2|.
\]

The earlier sign and the upper sign give a root by continuity. The positive derivative of the squared field gives strict monotonicity on the whole outer bracket and the quantitative root separation by the mean-value theorem. A nonnegative field magnitude is the square root of its square, so the closed-cell derivative certificates give continuity at the joins as well. The two-sided derivative at an interior row boundary comes from the single joined physical ODE solution. The continuation past the last cap supplies the ordinary derivative at that endpoint for the closed-cell argument. [Generic height branch](../../PlasmaLean/Theory/Kinetic/MirrorHeightBand.lean) · [Signed physical attachment](../../PlasmaLean/Design/DommaschkEndpointMirrorBranch.lean)

The lower-height specialization already narrows the first crossing to $(317/64,318/64)$, with checked package `DommaschkQ0R478MirrorBranch318.of_signed_chain` and key `b1111cc635513e7bfacf50605a56bdf75f0e3addf70e379868df6c4c9406cca7`. Both implications explicitly take the physical propagation to the bracket as a premise. The independent signed propagation campaign supplies this premise when it reaches the appropriate row. [Endpoint trace campaign](../../scripts/dommaschk_kam/verify_endpoint_trace_campaign.py)

At every interior height the ordinary derivative exists. Writing $f(t)$ for the physical field magnitude on the outward branch gives

\[
\tau'(h)=1/f'(\tau(h)), \qquad 0<\tau'(h)<800h.
\]

The inverse is already continuous and satisfies $f(\tau(h))=h$ locally, while the physical derivative at the root is strictly positive. The one-dimensional inverse-derivative theorem therefore applies at each interior height. The first-mirror times are continuous at the two boundary heights. [Inverse response theorem](../../PlasmaLean/Theory/Kinetic/MirrorBranchCaps.lean)

The two additional observed caps identify a change in the root position across the height band. On either signed branch,

\[
  \frac{317}{64}<\tau(h_L)<\frac{318}{64},\qquad
  \frac{325}{64}<\tau(h_U)<\frac{327}{64},\qquad
  \frac{7}{64}<\tau(h_U)-\tau(h_L)<\frac{10}{64}.
\]

At $318/64$ the true field lies strictly above $h_L$. At $325/64$ it lies strictly below $h_U$. The branch's strict before- and after-root bounds place each cap on the corresponding side of its root. [Order lemmas for caps on a first-mirror branch](../../PlasmaLean/Theory/Kinetic/MirrorBranchCaps.lean)

## Verified packages

The ten closed slabs have forty Lean theorems for the outward squared-strength and the level derivative, in each physical direction. They use archive SHA-256 `07763b1926fb24bb93889e651ced079f4871c59c72f443f6b7f2392fc5eb6f83`.

| Closed slab index | Physical derivative proof key |
| --- | --- |
| 317 | `5a056410325d250fbd7c409530e4ecf53fe4553a692bb28f53751f3610d8f621` |
| 318 | `d9d8d318085dc42471a9eab3fc1a4a8f430119c0f33c57920ce882f474931e08` |
| 319 | `a25afb758736215efaf30a75bbccbdea7335505fda112e4d42f86033668c0e02` |
| 320 | `ca9fa35f97eaa41fd5e87febadfe1d7b9ee022ba728b0ff205bc4a7bafe2f2fa` |
| 321 | `cc0c0c804c7bf1d7ba2327f9be90fe3172f34e28fcfd383577ae92399e853039` |
| 322 | `916d7c9b5bb7ce4a643bce1b1b7dd27539e847b31cc8b87a8357936897904058` |
| 323 | `84ce0fae5d280ab91fcdf74183d55ea8d8035249951567e4c07c665662ab65f2` |
| 324 | `71f919960f2045c225f661b28e6f9967a74a6f918657fc9f8c72a406bcded3f6` |
| 325 | `3379594a7536b88227d4a8a41756153f41cdb5cf87c88fdddf4d7c0acf492fef` |
| 326 | `681cc7df49c537fd137288fd0e817edfcc339297051b4c5e1b414a832819409b` |

The all-height branch package `DommaschkQ0R478MirrorBranch327` has key `bec36192acda0d342472eb57eb4ddf98f027a3c3f631371c6c7c983558e957f3`. Its three audited declarations are `fwd_branch`, `back_branch` and `of_signed_chain`. The localization and inverse-derivative package `DommaschkQ0R478MirrorTimeSeparation` has key `4b08eec6f48533982cfa1b7aba98cc7259d65de3da047014b2aa70dc69e898b1`. Its four audited declarations are `fwd_root_separation`, `back_root_separation`, `fwd_time_derivative` and `back_time_derivative`. All declarations use only `propext`, `Classical.choice` and `Quot.sound`. Lean rejected a negative control that tried to use the actual forward displacement theorem to assert a displacement of at most $7/64$.

At verification the independent signed physical path had reached 64 slabs in each direction. The complete branch theorem quantifies over a matching physical continuation through the outer cap. The earlier unconditional submirror conclusion on the verified through-birth interval follows from N-121.

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkEndpointMirrorBranch PlasmaLean.Theory.Kinetic.MirrorBranchCaps
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_slopes.py --rows 317 318 319 320 321 322 323 324 325 326 --workers 2 --output /tmp/plasma-q0r478-common-band-slopes.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_band.py --caps /tmp/plasma-q0r478-mirror-caps.json --exclusion /tmp/plasma-q0r478-grouped-exclusion.json --slopes /tmp/plasma-q0r478-common-band-slopes.json --output /tmp/plasma-q0r478-all-height-branches.json
```

N-115 and N-121 give the replay commands for the two parent manifests. Add `--signed .lake/secondary-trace-campaign/q0r478/prefixes/328.json` to bind the actual long birth path when that receipt exists. The attachment checks the exact archived row lists against both branches, keeping the same section state and actual physical approach for both mirror times. [Full-height verifier](../../scripts/dommaschk_kam/verify_secondary_mirror_band.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-127 |
| Kind | Common height band for two signed first-mirror branches |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-115, N-121 |
| Dependency requirement | Actual physical signed output tubes and derivative at the physical ODE, earlier closed submirror prefix, exterior superlevel cap and the same joined trajectory through the complete interval |
| Produces | Uniqueness, transversality, monotonicity and quantitative continuity of both first-mirror times at every height of the archived band |
| Status | Implemented for both signed physical tubes, conditional on one joined propagation beyond the outer mirror cap |
| Lean evidence | `MirrorBranchCaps`, ten physical slope packages, `DommaschkQ0R478MirrorBranch327` and `DommaschkQ0R478MirrorTimeSeparation` |
| Audit evidence | Forty physical slope declarations, three branch declarations, four timing declarations, a kernel-rejected reversed inequality and the receipt keys above |
| Last updated | 25 November 2026 |
