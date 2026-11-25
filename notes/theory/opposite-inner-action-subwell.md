# A positive action core at the original opposite-section inner birth

At \(u=0.470\), the signed clock interval of length ten centred on the opposite section already carries enough action to exclude \(j_*=6799610938322487/5000000000000000\) at \(h_U=5300546391395933/5000000000000000\). Lean checks the exact panel sum and proves how it applies to the first well around the actual birth. The complete physical identification of the panels on a single field line is still open. [Physical-clock theorem generator](../../scripts/dommaschk_kam/verify_opposite_inner_birth_obstruction.py)

| Field | Value |
| --- | --- |
| ID | N-195 |
| Kind | Certificate and reduction of a physical action obstruction |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-190 opposite-section physical screen, Q-16 embedded torus witnesses, the signed physical launch collar, and the native lower action quadrature |
| Produces | A common original launch seed, an accessible-core theorem, a rounded positive mass on 640 signed rows, and four complete physical row bounds |
| Status | Lean-verified physical launch, reduction and four observable rows. Full physical cell coverage remains open |
| Lean evidence | `DommaschkOppositeInnerSeed.from_nested_tori`, `PositiveSubwell.floor_in_first_well`, `DommaschkShiftedActionSubwell.shifted`, `DommaschkOppositeInnerSubwell.original_clock` |
| Audit evidence | The physical-clock and first-well action theorems use `propext`, `Classical.choice`, `Quot.sound`. All four actual row bounds passed the same audit |
| Updated | 2026-11-25 |

## Core and well

Write \(s=\pi/2\). For any absolute-time field line \(Y\) enclosed in the regular physical region throughout its first well \((l,r)\) around \(|\phi-s|\le 2^{-19}\), assume the stated physical speed and arclength-density lower bounds on the signed core \([s-5,s+5]\). Then \(l\le s-5\), \(s+5\le r\), and the first-well action exceeds \(j_*+3/10000\). The theorem compares the translated pointwise density with the derivative norm of the Cartesian field line. The local ODE and the displayed strict lower speed decide which accessible well contains the core. No outward derivative or predicted root location is an input. [Positive-core theorem](../../PlasmaLean/Certificates/PositiveSubwell.lean) · [Physical clock translation](../../PlasmaLean/Design/DommaschkShiftedActionSubwell.lean)

There are 320 pairs of signed rows of length \(1/64\). Each signed row contributes 24 distinct directed panel bounds. The archive format repeats each panel on its two half-panels, giving 15,360 distinct physical panel models and 30,720 stored half-panel inequalities. Lean checks that each stored lower squared speed is strictly positive and that their lower action rectangles sum to \(287167485626455/211106232532992\). This exceeds the target by approximately \(0.00037628\). The rounded 319-pair floor computed externally is \(23909305127139/17592186044416\), below the target. The larger N-190 floor for 330 pairs includes ten further pairs near the mirrors. [Core certificate generator](../../scripts/dommaschk_kam/verify_opposite_action_subwell.py) · [Original opposite-section strip](opposite-section-excludes-pilot-action-strip.md)

## Original packets and physical coverage

For the same pair of embedded invariant tori, every original birth at \(u=47/100\) and \(|\phi-s|\le 2^{-27}\) follows the actual field ODE to the stored seed. The centre is \((1081317837092435255099392,0)/2^{80}\), with Euclidean radius \(7471231115882077/2^{80}\). This is the common radius before the two distinct polynomial recentering jumps. N-190's external launch enclosure covers \(2^{-19}\). The physical-clock implication applies on the wider interval whenever its input bounds are given. [Original launch proof](../../PlasmaLean/Design/DommaschkOppositeInnerSeed.lean)

For both directions, signed rows 0 and 319 have separate kernel proofs of the 24 physical field and arclength-density panel bounds, uniform over the recorded moving-frame tubes. The proof checks the opposite-section trigonometric clock and genuine QA2R spatial polynomials. The endpoints test both the birth region and the weakest incoming core row. The other 636 observable rows and the two actual continuous trajectories from the common seed through row 319 are pending. The existing \(u=0.464\) opposite-section trajectory covers a different original seed. [Physical row builder](../../scripts/dommaschk_kam/verify_opposite_inner_action_rows.py)

## Standalone replay

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
src=scripts/dommaschk_kam
lake build PlasmaLean.Certificates.PositiveSubwell PlasmaLean.Design.DommaschkOppositeInnerSeed PlasmaLean.Design.DommaschkShiftedActionSubwell
"$py" "$src/screen_opposite_action_prefix.py" --packet /tmp/plasma-n195-q1r470.json.gz --output /tmp/plasma-n195-prefix.json
"$py" "$src/verify_opposite_action_subwell.py" --packet /tmp/plasma-n195-q1r470.json.gz --output /tmp/plasma-n195-subwell.json
"$py" "$src/verify_opposite_inner_action_rows.py" --packet /tmp/plasma-n195-q1r470.json.gz --core /tmp/plasma-n195-subwell.json --rows 319 0 --output /tmp/plasma-n195-rows.json
"$py" "$src/verify_opposite_inner_birth_obstruction.py" --packet /tmp/plasma-n195-q1r470.json.gz --core /tmp/plasma-n195-subwell.json --output /tmp/plasma-n195-join.json
```

| Artifact | SHA-256 or proof key |
| --- | --- |
| Opposite-section packet | `97906e2444eae3e25f072f411b91f8799c1adf2044da9b05469475dec029c13d` |
| Complete positive core | `76eed225c6fd548fceda4fea966928d8dc424d6170c35bd26772139dc9214662` |
| Physical clock and original seed audit | `235a3c8492df440d7e7a194871d12809b454dd201fa07dc35e40130dda750002` |
| Backward row 0 | `30e27295621669691ea07a03e4fda2e07888850de88a7c51e7a9711c459c2d25` |
| Forward row 0 | `49f883931440c5e0e4fa4057e9d208a0b21412bb6832d404406711e0f493cd70` |
| Backward row 319 | `e0315ff6aeaccc89062653009bb258e285683ca1fe2385c574ed9d90e9c714b7` |
| Forward row 319 | `4f349889e317f3b302b776cd2e348c0b67de8fc68236436c1f43919ce54dfffe` |
