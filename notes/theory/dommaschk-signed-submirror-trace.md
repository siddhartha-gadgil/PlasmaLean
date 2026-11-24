# Strict field-strength bounds before the first Dommaschk mirror

For every section-zero Q-16 birth at $u=0.470$ with $|φ|≤2^{-19}$, the field-line ODE admits one signed trajectory $y$ through the transferred birth with

$$
  |B(t,y(t))| < 5297961656084411/5000000000000000
  \qquad(-3/2≤ t ≤3/2).
$$

This rules out a contact with either archived mirror height anywhere in this three-radian interval, including the internal joins. The same trajectory has the radius and position estimates of N-76. Separately, a paired trace of 128 slabs per direction now covers $[-2,2]$ with the same maximum position-error numerator 2678772121456213228 over $2^{80}$. Its forward and backward certificates add projected Jacobians on rows 118 and 119 to the N-76 replay. Lean attaches the strict signs of 96 time-dependent spatial tubes per direction to the trajectory supplied by the nested-torus launch theorem. [Signed path and observable](../../PlasmaLean/Design/DommaschkSignedObservable.lean) · [Exact prefix assembly](../../scripts/dommaschk_kam/verify_signed_submirror_prefix.py)

At the proposed mirror slabs, a second result now evaluates both signs of the clock on the same curve. For an enclosed signed Q-16 trajectory long enough to contain row 316 or 324, the corresponding level is reached in both directions. If its strength on the closed signed interval through the left endpoints stays below that level, the earliest contact on each side belongs to the stated open bracket. The proof uses continuity only on the terminal brackets. Reaching those brackets from birth and excluding earlier encounters outside the three-radian interval remain separate numerical obligations. [Bracket implications and birth composition](../../scripts/dommaschk_kam/verify_signed_mirror_passage.py)

## Reproduce

Build the static modules, prepare the signed 96-slab proof as in N-76, and use its manifest below. The row verifier bounds the actual field throughout each forward and reflected tube. The final verifier rejects missing rows, mismatched archive hashes, and conflicting proof inputs.

```sh
lake build PlasmaLean.Design.DommaschkPreMirrorSigns PlasmaLean.Design.DommaschkSignedObservable
.venv-ws/bin/python scripts/dommaschk_kam/verify_pre_mirror_signs.py --range 0 95 --output /tmp/qa2r-first96-signs.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_submirror_prefix.py --paired /tmp/paired96.json --signs /tmp/qa2r-first96-signs.json --length 96 --output /tmp/qa2r-below96.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_mirror_passage.py --brackets /tmp/qa2r-brackets.json
```

The bracket manifest in the last command comes from N-77. The three-radian conclusion uses only the first 96 pairs of signs. Rows 314 and 315 also have separate local sign proofs. On row 315 a single radial bisection suffices.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-79 |
| Kind | Physical trajectory observable |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-66, N-75, N-76, N-77 |
| Dependency requirement | Same launched path throughout, 96 ordered spatial sign certificates in each direction, and a positive cylindrical radius at each field evaluation. |
| Produces | A strict physical bound on the closed signed interval, plus conditional two-sided first-contact statements at both heights. |
| Difficulty | Extending the signed path and the sublevel certificates to the two mirror brackets. |
| Status | Compiled and audited for the stated launch family. |
| Lean evidence | On demand, `DommaschkSubmirror096Of096.below_from_birth` and `DommaschkSignedMirrorBrackets.first316`, `first324`. |
| Audit evidence | Signed below-height proof `1d26acc92eb6`, 96-slab paired trajectory `e9b226612cdf`, 128-slab paired trajectory `0c91cdb3e65b`, bracket implications `47ca6eb9bedc`. All use standard axioms only. |
| Last updated | 24 November 2026 |
