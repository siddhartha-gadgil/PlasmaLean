# Quantitative height clearance on signed QA2R tubes

A negative upper bound for the physical mirror polynomial measures how far the field is below a given height. The local cylindrical radius matters. If $0<R\le r$ and

\[
  G_H=R^{16}(|B|^2-H^2)\le e<0,
\]

then every nonnegative test height $K\le H$ with $e+r^{16}(H^2-K^2)<0$ satisfies $|B|<K$. The identity $G_K=G_H+R^{16}(H^2-K^2)$ is exact. This retains the radial factor at the outer launch parameters, where it is considerably smaller than one near the mirror. A clearance $|B|<h_L-\delta$ implies that the dimensionless parallel speed $\sqrt{2(h-|B|)}$ exceeds $\sqrt{2\delta}$ at every archived height $h\ge h_L$. [Radius comparison theorem](../../PlasmaLean/Design/DommaschkGroupGapRadius.lean)

Dropping the radial factor without a bound on $R$ can reverse the conclusion. Lean checks the scalar example $R=2,D=192,n_R=n_Z=0$, with $H=2$ and $K=1$. It gives $G_H=-114688$ and $G_K=81920$, although $G_H+(H^2-K^2)<0$.

## Three physical birth families

On a single pair of nested, embedded QA2R KAM tori, every admissible birth angle $|\phi|\le 2^{-19}$ has the following three physical passages. At each launch parameter the actual approach to section zero supplies the common state for one forward and backward field line. At every point of the indicated signed interval the field satisfies $|B|<h_L-\delta$.

| Launch parameter | Signed azimuth interval | $\delta$ | Actual birth proof key |
| --- | --- | --- | --- |
| $478/1000$ | $[-2,2]$ | $1/270000$ | `5458f502dc953c3a67af63a7edfd1c285d823126980dba193557f589f3ec7e99` |
| $523/1000$ | $[-3/4,3/4]$ | $1/100000$ | `24049f6034009abc67056ca439deab712860e1356dc6b77b3fbcb500d83528c6` |
| $531/1000$ | $[-5/64,5/64]$ | $1/50000$ | `f17d99192fedb8951027b692e2850921fece231ef31b4dd40cf2c1a13f5b2d2b` |

The joint theorem `DommaschkCommonSubmirrorQ0R478Drop1Over270000N128Q0R523Drop1Over100000N048Q0R531Drop1Over50000N005.from_common_tori` has proof key `752c6715d91cabb833c7290bcefc4412969a72a91b8a1a93bc861042e20fb428`. At a fixed launch parameter the bound applies to the same field line for every time in its closed interval and every $h\ge h_L$. [Common-surface verifier](../../scripts/dommaschk_kam/verify_common_submirror_births.py)

## Complete incoming tube clearance at 478/1000

At $u=478/1000$ all 317 original incoming slabs in **both** outward directions satisfy the stronger inequality

\[
 |B| < h_L - 1/270000
 = 143044464714279097/135000000000000000 .
\]

This includes every point on 634 directed closed physical tubes out to $317/64$. The proof projects 22 field-model margins in 21 groups, with the final row covered by the union of two radial halves. Both halves use the actual radial cap $57/64$. The ordered declarations `DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.fwd_below` and `.back_below` have proof key `073471cfdf5da3891484ecdebfb9ed1927dde4092c20e6c55b6df1f2f90606b6`. The through-birth interval in the table uses the separately verified physical propagation. [Signed tube projection](../../scripts/dommaschk_kam/verify_grouped_field_clearance.py)

## A second enclosure of the final six slabs

At launch parameter $u=523/1000$, one signed Taylor calculation proves $|B|<h_L-1/50000$ on all twelve original physical output tubes for rows 316 through 321, including both ends of every slab. The approach applies to every point in each tube. A path uses the whole result once the signed propagated chain reaches $322/64$. The normalized incoming height is $h_L=5297961656084411/5000000000000000$.

The envelope of the six rows has cylindrical radius at most $115/128$. Its computed squared-gap upper bound is $-10132415663889716165/2^{80}$. The six forward and six backward declarations in `DommaschkQ0R523HarmonicSubmirror316To322Rows` have key `ee8f418152cc89b5b201245d696b5de8aa8a909f4da5d499637d0d669aff2fcb`. They depend only on `propext`, `Classical.choice` and `Quot.sound`.

The field has seven harmonics in the doubled physical azimuth. The first sine and cosine on the common group clock determine the higher harmonics by the double- and triple-angle formulae. The verifier evaluates the radial and vertical coefficients by Horner's rule and forms $D-h_LR^7$ before bounding the squared gap. It checks every rounded product and the error discarded above degree seven. This keeps the leading radial terms from widening the estimate near the mirror. [Harmonic model and gap identities](../../PlasmaLean/Design/DommaschkGroupedHarmonicGap.lean) · [Field and physical row verifier](../../scripts/dommaschk_kam/verify_harmonic_group_exclusion.py)

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkGroupedHarmonicGap PlasmaLean.Design.DommaschkGroupGapRadius
.venv-ws/bin/python scripts/dommaschk_kam/verify_harmonic_group_exclusion.py \
  --launch 523 --start 316 --stop 322 --drop 1/50000 --output /tmp/q0r523-harmonic-final-six.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_harmonic_group_exclusion.py \
  --launch 531 --all --drop 1/50000 --screen --output /tmp/q0r531-harmonic-screen.json
```

The exact external screen covers all 322 incoming rows at $523/1000$ and all 323 at $531/1000$ with sixteen groups each at the tighter test height. The second command reports proposed groups. Removing `--screen` checks and audits all of their signed Lean certificates.

An independent path begins with the original grouped sparse field proof. The scalar projection recovers its original rational upper margin and computes the radial correction on each group, including both spatial halves where the original row needed a split. [Original grouped method](secondary-qa2r-submirror-exclusion.md) · [Scalar projection verifier](../../scripts/dommaschk_kam/verify_grouped_field_clearance.py)

The scalar projection accepts the output of the original ordered exclusion verifier and reuses the authenticated dense field products. With `--signed`, it selects the matching prefix and attaches the actual birth-to-section path and a single two-sided physical trajectory. For example, the following checks use the N-121 and N-131 input receipts.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_field_clearance.py \
  --launch 478 --drop 1/270000 --exclusion /tmp/plasma-q0r478-grouped-exclusion.json \
  --output /tmp/full-incoming-clearance-478.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_field_clearance.py \
  --launch 478 --drop 1/270000 --exclusion /tmp/plasma-q0r478-grouped-exclusion.json \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/128.json --output /tmp/clearance-478.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_field_clearance.py \
  --launch 523 --drop 1/100000 --exclusion /tmp/plasma-n131-q0r523-early048.json \
  --signed .lake/secondary-trace-campaign/q0r523/prefixes/048.json --output /tmp/clearance-523.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_field_clearance.py \
  --launch 531 --drop 1/50000 --exclusion /tmp/plasma-n131-q0r531-early005.json \
  --signed /tmp/plasma-horner-signed-q0r531-5.json --output /tmp/clearance-531.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_common_submirror_births.py \
  --births /tmp/clearance-478.json /tmp/clearance-523.json /tmp/clearance-531.json \
  --output /tmp/common-physical-clearances.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-135 |
| Kind | Quantitative submirror signs at the phase-zero radii |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-121, N-131, exact compensated field coefficients and actual signed moving tubes |
| Dependency requirement | The group covers each original spatial and angular row on the same clock. A through-birth conclusion also requires an actual signed propagation of that length |
| Status | Implemented on the three physical birth intervals, all 634 incoming physical tubes at 478/1000 and twelve near-mirror physical tubes at 523/1000 |
| Lean evidence | `DommaschkGroupGapRadius.at_lower`, `DommaschkGroupedHarmonicGap.harmonic_mem`, `estimate_mem` and the individual and combined physical packages |
| Audit evidence | The runs audit the exact field identities, rounded model arithmetic, original row attachments and three standard axioms. The scalar counterexample verifies the necessity of the radial factor |
| Last updated | 25 November 2026 |
