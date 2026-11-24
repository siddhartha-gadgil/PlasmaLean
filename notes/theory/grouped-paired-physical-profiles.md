# Comparing two QA2R field profiles over groups of signed slabs

On one interval of toroidal angle, the field strength and the arclength density of two nearby field lines vary together. A common time coordinate preserves this variation when comparing every point of the two physical tubes. The independent spatial errors still enter the proof at both radii. [Two-tube comparison](../../PlasmaLean/Design/DommaschkGroupedProfileCompare.lean)

## Statement

Write \(f_\ell(\phi,x)\) for physical QA2R field strength and \(w_\ell(\phi,x)\) for arclength per radian, where \(x\) is a point of the archived tube at launch label \(\ell\). For each certified index \(j\), every \(j/64\le t\le(j+1)/64\), and either sign of \(\phi=\pm t\), the signed theorem quantifies over every pair of points \(x_i,x_o\) of the original outgoing tubes at \(u_i=0.470\) and \(u_o=0.478\). It gives

\[
 f_o(\phi,x_o)\le f_i(\phi,x_i)-1/18000,\qquad
 (3999/4000) w_i(\phi,x_i)\le w_o(\phi,x_o),\qquad
 f_i(\phi,x_i),f_o(\phi,x_o)\le17/16 .
\]

The predecessor ellipses of the two original rows can be chosen independently. Every physical path enclosed in those rows therefore satisfies the same bounds. Applying the result to the original interpolated births uses the separate signed-path and common-torus assembly of N-136. [Paths on the two embedded tori](compared-signed-trace-prefixes.md)

## Why a group works

For the contiguous range \([a,b)\) of row indices, the local clock \(v\in[-1,1]\) of row \(j\) enters the group at \(s=(2j+1-a-b+v)/(b-a)\). Lean checks the coefficient and remainder inequalities for \(R,z,\cos(2t),\sin(2t)\) under this substitution for each original row. Backward rows use their own stored coefficients and outgoing error radii. Reflection in \(z\) and the QA2R field identity then transfer both physical observables to angle \(-t\). [Affine change of clock](../../PlasmaLean/Design/DommaschkGroupedMirrorModels.lean) · [Signed transfer](../../PlasmaLean/Design/DommaschkGroupedProfileCompare.lean)

At each label, the reference position at \(s\) is the centre of its own group rectangle. A common larger spatial box encloses both rectangles, including their connecting segments to their respective centres. On this box Lean bounds the two partial derivatives of \(S=\|B\|^2\) by \(K_R,K_z\). The mean-value theorem gives an error of at most \(e_\ell(K_R+K_z)\) from the reference squared strength, where \(e_\ell\) is the spatial radius at that label. The centre comparison uses the exact physical identity \(R^{16}S=(RD)^2+n_R^2+n_z^2\). The lower bound on its cleared difference pays both spatial errors before claiming \(2(17/16)(1/18000)\le S_i-S_o\). The two strength ceilings and the arclength inequality use the actual field on the full tubes. [Spatial mean-value bound](../../PlasmaLean/Design/DommaschkCenteredStrength.lean) · [Physical arclength identity](../../PlasmaLean/Design/DommaschkPairedArcRatio.lean)

The nine shared value and partial-derivative models can be computed by seven-harmonic Horner evaluation. Each harmonic is obtained from the same certified sine and cosine. A kernel-checked polynomial identity identifies the physical field or partial derivative. A second coefficient check encloses the resulting native model inside the model used in the mean-value and arclength arithmetic. The same argument applies to the three field values on each of the four reference and full boxes. [Harmonic proof builder](../../scripts/dommaschk_kam/grouped_profile_harmonics.py) · [Comparison arithmetic](../../scripts/dommaschk_kam/grouped_profile_arithmetic.py)

## Coverage and replay

At the first checkpoint, Lean checked all 44 signed comparisons for indices 236–251 and 319–324. Their receipts are listed below. The final group has the smallest cleared strength margin in the full suffix, \(5228969443943143/302231454903657293676544>0\). Its common spatial derivative bounds are \(24785667/10000000\) radially and \(1927611/2000000\) vertically. Every signed row declaration has the standard axiom audit `propext`, `Classical.choice` and `Quot.sound`.

| Original row indices | Checked row module | Receipt key |
| --- | --- | --- |
| 236–246 | `DommaschkGroupedProfile236To247Rows` | `523a4bdb3ce24287c627fccb9804e547ff25a03be07a951915bcd1bb836ca9db` |
| 247–251 | `DommaschkGroupedProfile247To252Rows` | `ede757524a039bc193a41e7c8d5c02144f536d02bbd702926f48d882b07f12df` |
| 319–324 | `DommaschkGroupedProfile319To325Rows` | `5be96dba67eafba6ecbae8782eac92f59acf524f869ef6fbe47004e2ff136468` |

The exact arithmetic screen covers all 89 indices from 236 through 324 with 13 groups, both signs at each index. The remaining 236 indices of the complete physical-comparison target admit N-132's direct native check. The driver records the signed Lean receipt for each additional group as it completes. A physical radial action increment also requires the second launch's actual first-well trajectory through both contacts. [Profile screen and proof driver](../../scripts/dommaschk_kam/verify_grouped_profile_suffix.py) · [Action increment criterion](finite-radial-action-comparison.md)

~~~bash
lake build PlasmaLean.Design.DommaschkGroupedProfileCompare PlasmaLean.Design.DommaschkGroupedHarmonicGap
py=.venv-ws/bin/python
proof=scripts/dommaschk_kam/verify_grouped_profile_suffix.py
$py "$proof" --screen --output /tmp/paired-group-exact.json
$py "$proof" --group 236 --backend sparse --output /tmp/paired-group236.json
$py "$proof" --group 247 --output /tmp/paired-group247.json
$py "$proof" --group 319 --backend hybrid --output /tmp/paired-group319.json
$py "$proof" --all --workers 2 --output /tmp/paired-group-all.json
~~~

An independent ordered block for indices 319–324 combines the grouped proof through row 323 with the individually verified row 324. Its two signed declarations have key `239ea2381129c5f9dbcf783138e224f300ea1b5fb6257386cca8e027056c015f`. The ordered-prefix producer accepts both kinds of receipts in chronological order. [Paired path assembly](../../scripts/dommaschk_kam/verify_compared_trace_prefix.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-137 |
| Title | Comparing two QA2R field profiles over groups of signed slabs |
| Kind | Physical observable bound and exact certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-126, N-129, N-132, N-135, N-136 |
| Dependency requirement | Signed outgoing tubes, QA2R field reflection, the spatial mean-value theorem, common-clock harmonic bounds and the physical arclength identity |
| Produces | A grouped proof of the common-angle field drop and arclength comparison against the original signed rows of the two radial launches |
| Status | Signed ground results at the three groups tabulated above, including the smallest proposed strength margin. The external arithmetic succeeds for the complete suffix. |
| Lean evidence | `DommaschkGroupedProfileCompare.row_inputs`, `DommaschkGroupedProfileCompare.compare_rows` and the signed declarations identified by the generated receipts |
| Last updated | 25 November 2026 |
