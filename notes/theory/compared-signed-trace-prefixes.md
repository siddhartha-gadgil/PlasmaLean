# Comparing two physical birth lines over a shared interval

For every QA2R launch angle $|\phi|\le 2^{-19}$, let $y$ and $z$ be the two signed field lines born at $u=0.470$ and $u=0.478$ on the same pair of nested embedded invariant tori. Lean constructs these lines so that the pilot $y$ has its previously certified first-well action, flight time and height calibration, and the following bounds hold at **every** azimuth $-5/16\le t\le5/16$.

\[
 |B(z(t),t)|\le |B(y(t),t)|-1/18000,\qquad
 w_z(t)\ge (3999/4000)w_y(t).
\]

Here $w$ is the physical arclength density per azimuthal radian. Both field strengths are at most $17/16$. The equality of the constructed trajectories with the original interpolated births holds at $t=\phi$, including when the launch is slightly off the section. The second trajectory solves the physical field-line equation through $[-2,2]$, and the pilot through $[-391/64,391/64]$. [Physical comparison and identification at birth](../../PlasmaLean/Design/DommaschkComparedTracePrefixes.lean) · [Pilot observables](common-torus-pilot-action.md)

## Joining the signed comparisons

The initial positions, shapes and error bounds of the two tubes are independent. Their azimuthal clocks agree. A row certificate therefore quantifies over every pair of points, one from each tube, at one common time. The theorem `OnPairedTubes.on_nonempty_prefix` transfers these relations to two actual enclosed paths. It includes shared endpoints and allows either path to continue after the last certified comparison. The negative-time proof uses the two original backward rows in the correct chronological order. [Generic Lean lemma](../../PlasmaLean/Certificates/PairedPositionFrameObservables.lean)

The concrete proof uses twenty contiguous rows on each signed branch. Smaller proof terms handle up to eight pairs of rows at once. The assembly checks the radius labels, directions, archive hashes and common torus parameters, then Lean matches every row definition against the two actual trajectories. The hardest single-row comparison at index 324 has a separate signed proof. [Paired arclength and field receipts](paired-physical-arclength.md)

The application to the full well has a fixed stopping condition. `increment_of_compared` proves that comparison through $[-325/64,325/64]$ suffices. For $h$ and $h+1/18000$ in the certified band, the second first well at $h$ contains the pilot first well at the raised height, and its action at $h$ exceeds the calibrated pilot action at $h$ by more than $1/375$. The theorem takes the paired bounds on that whole interval, the second first mirrors, and continuity and nonnegativity for the second-line integrand. At publication the actual joined comparison covers twenty of the required 325 rows each way. [Finite action comparison](finite-radial-action-comparison.md) · [Second first-mirror brackets](secondary-first-mirror-height-band.md)

## Reproduction

The calibrated family used here covers 1,238 signed slabs. Its lengths each way are $(391,128,48,5)$ at section zero and $(32,5,5,5)$ at the opposite section. Its key is `20cf8aafa70760dce3003406173cb8b03e08ddac8cc77586cd81ed6c993b5e8e`. Reproduce that family using N-120 and N-130, and generate the individual native signed comparisons using N-132. Set `rows` to the directory containing the per-index receipts. [Eight-sector assembly](eight-signed-traces-on-common-tori.md)

```bash
lake build PlasmaLean.Design.DommaschkComparedTracePrefixes
.venv-ws/bin/python scripts/dommaschk_kam/verify_compared_trace_prefix.py \
  --calibrated /tmp/plasma-calibrated-eight1238.json \
  --launch-profile /tmp/plasma-paired-action-profile000.json \
  --rows "$rows"/{000..019}.json --output /tmp/compared-births020.json
```

The combined theorem is `DommaschkComparedBirths020On391_128_48_5_32_5_5_5.from_common_tori`. Its proof key is `37ea0ad3caaf93ad976af2e46c04ef04c9947fc940998e727141acb64ec329b6`. [Proof builder](../../scripts/dommaschk_kam/verify_compared_trace_prefix.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-136 |
| Kind | Reusable paired trajectory lemma and physical action comparison |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-110, N-126, N-128, N-129, N-130, N-132 |
| Dependency requirement | Synchronized physical rows, true through-birth traces, and the calibrated pilot on the same embedded surfaces |
| Status | Twenty signed pairs each way joined on the two physical lines; the full 325-pair application remains conditional |
| Lean evidence | `OnPairedTubes.on_nonempty_prefix`, `compare_birth`, `increment_of_compared` and the generated `from_common_tori` |
| Audit evidence | The two ground declarations use only `propext`, `Classical.choice` and `Quot.sound` |
| Last updated | 25 November 2026 |
