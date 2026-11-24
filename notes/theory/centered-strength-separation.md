# Squared-strength separation near the upper pilot mirror

The first 325 slabs at the QA2R launch labels \(u=0.470\) and \(u=0.478\) share a toroidal clock. Near the pilot's upper mirror, the variation of field strength across a single slab exceeds its change across labels. Evaluating the two reference strengths on the same clock and using spatial derivatives to bound each tube's deviation from its reference retains the small difference needed for the action comparison. [Shared-clock feasibility screen](../../scripts/dommaschk_kam/screen_paired_action_profiles.py) · [Spatial mean-value theorem](../../PlasmaLean/Design/DommaschkCenteredStrength.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-129 |
| Title | Centered mean-value enclosure for the finite two-launch field comparison |
| Kind | Analytic proof and numerical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-120, N-128, the two signed outgoing trajectory archives, the physical squared-strength identity and the certified harmonic clock |
| Dependency requirement | Both labels must use the same physical angle and each measured point must lie in its original signed outgoing tube. |
| Produces | A centered estimate of the true squared strength and a same-clock field comparison on either signed branch of row 324. |
| Difficulty | Current field ranges vary strongly with angle while the inter-label strength drop is much smaller. The two tube radii enclose independent errors. |
| Status | Row 324 verified on both signed physical tubes. All 325 rows passed the external exact arithmetic screen. |
| Lean evidence | DommaschkCenteredStrength.mean_value, physical_derivative, centered and compare. |
| Audit evidence | DommaschkCenteredStrengthPair324.fwd_squared_drop and back_squared_drop use propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |

## From a reference curve to the whole tube

Fix the physical angle \(\phi\) and write \(S_\phi(R,Z)=\lVert B(R,\phi,Z)\rVert^2\). Let \(a,b\) be the radial and vertical coordinates of the reference point and suppose \(|R-a|,|Z-b|\le e\). If the two partial derivatives are bounded in magnitude by \(K_R,K_Z\) throughout that rectangle, then

\[
  |S_\phi(R,Z)-S_\phi(a,b)|\le e(K_R+K_Z).
\]

Lean differentiates the straight segment from \((a,b)\) to \((R,Z)\) and applies the one-dimensional mean-value inequality. In the candidate-specific theorem the derivatives come from the six spatial partials of the checked QA2R field polynomials. Positivity of \(R\) and of \(D=R^7B_\phi\) holds on the full rectangle. The chosen reference \(h_0\) in the compensated derivative \(D-h_0R^7\) is algebraically arbitrary. [Physical derivative and rectangle estimate](../../PlasmaLean/Design/DommaschkCenteredStrength.lean)

## Row 324

At \(t\in[324/64,325/64]\), reflection maps both negative-clock output tubes to the positive clock. Each label uses the larger of its two signed output radii. The certified spatial bounds on this slab are

| Launch label | \(K_R\) | \(K_Z\) | Approximate upper bound on \(\lvert S-S_{\rm ref}\rvert\) |
| --- | ---: | ---: | ---: |
| 0.470 | 5190847/2500000 | 8179801/10000000 | \(8.137\times10^{-6}\) |
| 0.478 | 20766341/10000000 | 4088053/5000000 | \(8.150\times10^{-6}\) |

For the two references, let \(P_i=R_i^{16}>0\) and \(U_i=P_iS_i\), with subscript \(i\) for the inner label and \(o\) for the outer label. The checker evaluates \(U_iP_o-U_oP_i-(17/144000+e_i+e_o)P_iP_o\) on the common normalized clock, with \(e_i,e_o\) the two squared-strength error bounds above. Its lower bound is \(74020574463578579/604462909807314587353088>0\). The center values are evaluated from the three exact field polynomials using the seven-harmonic representation and zero spatial radius. Each angle model retains its certified remainder. [Centered certificate producer](../../scripts/dommaschk_kam/verify_centered_strength.py) · [Physical tube and pair assembly](../../scripts/dommaschk_kam/centered_strength_pair.py)

At a common time on either signed branch this yields \(S_i-S_o\ge 17/144000=2(17/16)(1/18000)\), for every pair of points in their respective original outgoing tubes. If both field magnitudes are bounded by \(17/16\), the identity \(S_i-S_o=(\lVert B_i\rVert-\lVert B_o\rVert)(\lVert B_i\rVert+\lVert B_o\rVert)\) gives the requested field-strength drop of \(1/18000\).

The exact external screening program checked this same arithmetic over all 325 indices. Its smallest lower margin occurred on row 324. Kernel replay on additional rows and the arclength comparison are the remaining inputs to the all-row paired action argument. [All-row arithmetic screen](../../scripts/dommaschk_kam/screen_centered_strength_values.py)

## Replay

~~~bash
LEAN_NUM_THREADS=1 lake build PlasmaLean.Design.DommaschkCenteredStrength \
  PlasmaLean.Design.DommaschkPairedActionProfiles
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/screen_centered_strength_values.py --rows 0 324 \
  --output /tmp/plasma-centered-strength-screen325.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/verify_centered_strength.py --row 324 \
  --output /tmp/plasma-centered-strength324.json
~~~

The accepted row-324 receipt key is `c3dccc142c0d6a1a38fc5b7dcd08e54649c71e1eb42b3569e6914fe493a1aff2`.
