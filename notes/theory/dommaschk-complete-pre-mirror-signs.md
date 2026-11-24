# Strict physical field-strength signs before both mirror brackets

For the phase-zero launch at radius 0.470, Lean proves the following for **every point of each archived spatial tube**, at every angle of its closed slab. The outward clock is measured from the launch section in either direction. [Ordered-tube verifier](../../scripts/dommaschk_kam/verify_signed_submirror_prefix.py)

| Height | Slabs in each direction | Outward interval | Proved inequality |
| --- | --- | --- | --- |
| $h_L=5297961656084411/5000000000000000$ | 0 through 315 | $[0,316/64]$ | $|B|<h_L$ |
| $h_U=5300546391395933/5000000000000000$ | 0 through 323 | $[0,324/64]$ | $|B|<h_U$ |

The archive contains 648 directed strict signs. For the upper interval, strict ordering $h_L<h_U$ supplies the first 316 rows. Eight further row pairs directly prove the upper inequality. Two ordered list proofs then match the actual evolving frames, including the exact previous state at every join. The lower list has key `9d2973b8d2ef` and the upper list `7f923456144b`. [Physical sign generator](../../scripts/dommaschk_kam/verify_uniform_pre_mirror_signs.py)

Most rows admit a shared rational estimate for the spatial change in each of the three field polynomials. It compares the polynomial on the central curve and on the tube at the same angle. On the reference box $|R-R_0|\le3/32$, $|Z|\le5/64$, each spatial coordinate can change by at most $2^{-18}$. Rows near the levels can instead use direct interval bounds. Row 315 required two radial pieces and row 323 required four. [Polynomial perturbation lemma](../../PlasmaLean/Design/DommaschkPhysicalPolynomialError.lean) · [Exact field constants](../../PlasmaLean/Design/DommaschkUniformFieldError.lean)

The local crossing theorem of N-81 and the ordered signs now apply to **the same trajectory** whenever its physical propagation from birth reaches the end of the relevant bracket. They give a first contact in $(316/64,317/64)$ or $(324/64,325/64)$ on each outward branch, uniqueness on the closed bracket, and a derivative greater than $1/(256h_L)$ or $1/(800h_U)$ at contact. The outstanding premise is propagation from the launch to the bracket. As of this proof the audited single trajectory from the actual Q-16 birth reaches two radians each way. [Signed regularity theorem](../../PlasmaLean/Design/DommaschkSignedMirrorSlope.lean) · [Birth-to-contact composition](../../scripts/dommaschk_kam/verify_signed_mirror_passage.py)

## Reproduce

```sh
lake build PlasmaLean.Design.DommaschkPerturbedFieldModel PlasmaLean.Design.DommaschkUniformFieldError PlasmaLean.Design.DommaschkSignedMirrorSlope
.venv-ws/bin/python scripts/dommaschk_kam/emit_uniform_field_error.py --check
.venv-ws/bin/python scripts/dommaschk_kam/verify_uniform_pre_mirror_signs.py --range 0 315 --output /tmp/pre-lower.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_uniform_pre_mirror_signs.py --range 316 323 --output /tmp/pre-upper.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_submirror_prefix.py --rows-only --signs /tmp/pre-lower.json --length 316
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_submirror_prefix.py --rows-only --signs /tmp/pre-lower.json /tmp/pre-upper.json --upper --length 324
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-84 |
| Kind | Complete ordered tube estimates and signed trajectory composition |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-66, N-77, N-79, N-81 |
| Dependency requirement | Archived spatial tubes with physical angle and matched previous states. Birth application also requires the enclosed ODE chain to the end of the crossing slab. |
| Produces | Strict field strength before the two mirror brackets at all 648 directed rows and first transverse contacts on a sufficiently long enclosed birth path. |
| Difficulty | Checked physical propagation through rows 316 and 324. |
| Status | Both lists and four ordered bounds are proved. The signed regularity and first-contact composition compile with the propagation premise. |
| Lean evidence | `DommaschkSubmirrorRows316` and `DommaschkUpperSubmirrorRows324`, each with `fwd_checked` and `back_checked`; `DommaschkSignedMirrorSlope.first_transverse`. |
| Audit evidence | Every row and both complete aggregates passed the standard axiom checks. |
| Last updated | 24 November 2026 |
