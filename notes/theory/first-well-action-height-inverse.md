# Quantitative recovery of mirror height from first-well action

At every admitted phase-zero QA2R pilot birth, two heights $h_1<h_2$ in the certified band have first-well actions satisfying

$$
14(h_2-h_1)<J(h_2)-J(h_1)<264(h_2-h_1).
$$

Conversely, every action between the two endpoint actions determines a unique height. For two distinct attainable actions $a_1<a_2$, the height difference lies strictly between $(a_2-a_1)/264$ and $(a_2-a_1)/14$. Both actions refer to the same field line through the same birth. [Physical calibration](../../PlasmaLean/Design/DommaschkActionHeightInverse.lean) · [General interval inverse theorem](../../PlasmaLean/Theory/Kinetic/MirrorActionInverseBounds.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-113 |
| Title | Quantitative recovery of mirror height from first-well action |
| Kind | Theorem and physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-104, N-109 |
| Dependency requirement | The true action derivative equals the first-well one-way time, and the same physical well has $14<T<264$ for every closed-band height. |
| Produces | Strict action increments, the full closed attainable action interval, a two-sided calibrated inverse with modulus $1/14$, and exact rational bounds on total band action width. |
| Difficulty | Independently chosen birth or mirror witnesses need not coincide. The application attaches both inputs to the same path and identifies both endpoints. |
| Status | Verified |
| Lean evidence | MirrorActionInverseBounds.secants_of_derivatives, inverse_of_secants, range_eq_interval, DommaschkActionHeightInverse.of_identity, endpoint_width and the ground DommaschkActionHeightInverse325.from_birth. |
| Audit evidence | All five local theorems and the physical birth theorem use only propext, Classical.choice and Quot.sound. An affine calibration checks the strict-bound hypothesis. |
| Last updated | 25 November 2026 |

## Physical action and derivative

Use the nested-torus birth at radial interpolation parameter $47/100$ and original geometric angle $|\varphi|\le2^{-19}$. Fix the physical trajectory selected for that angle. At each $h\in[h_L,h_U]$, integrate the true Cartesian arclength density times parallel speed between its negative and positive first mirrors to obtain $J(h)$. N-104 identifies this moving action with the clipped action on $[-325/64,325/64]$, whose derivative is the one-way flight time. N-109 gives $14<T(h)<264$ at the exact same contact pair. The proof identifies the positive contact by uniqueness on the positive outward branch and the negative contact by uniqueness on the reflected branch. [Action derivative](mirror-action-flight-identity.md) · [Uniform one-way time budget](rowwise-first-mirror-flight-budget.md)

For any two distinct ordered heights, the ordinary mean value theorem gives their action secant as the flight time at an intermediate height. This yields the two strict inequalities without a continuity assumption on the flight time. The derivative used at a band endpoint is that of the ambient clipped action. The finite-increment estimates include both endpoint heights.

## Inverse and error bound

The attainable actions fill precisely $[J(h_L),J(h_U)]$ by continuity and strict monotonicity. The certified inverse $H$ gives $J(H(a))=a$ for every attained action and $H(J(h))=h$ for every band height. Its symmetric error inequality

$$
|H(a_2)-H(a_1)|\le\frac{|a_2-a_1|}{14}
$$

also applies to equal observations. For example, two attainable normalized actions on this same birth trajectory differing by at most $10^{-3}$ imply heights differing by at most $1/14000$. The inverse uses the action interval for the selected trajectory. [Two-sided inverse and error estimate](../../PlasmaLean/Theory/Kinetic/MirrorActionInverseBounds.lean)

The archived height difference is exactly $1292367655761/2500000000000000$. At the endpoints the physical action width therefore satisfies

$$
\frac{9046573590327}{1250000000000000}
< J(h_U)-J(h_L) <
\frac{42648132640113}{312500000000000}.
$$

The lower and upper endpoints of this estimate are respectively $0.0072372588722616$ and $0.1364740244483616$. As a sanity check, the affine action $J(h)=20h$ satisfies the generic secant bounds. Replacing its slope by 14 gives equality at the proposed strict lower bound, which Lean rejects. [Endpoint calculation](../../PlasmaLean/Design/DommaschkActionHeightInverse.lean)

## Replay

The replay takes the signed N-109 receipt and its content-addressed imports. The action derivative and the rowwise flight estimate are both applied to the path through the actual interpolated birth.

~~~bash
lake build PlasmaLean.Design.DommaschkActionHeightInverse
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_action_height_inverse.py \
  --row-flight /tmp/plasma-row-flight-budget-325.json --output /tmp/plasma-action-height-inverse-325.json
~~~

The parent N-109 key is c4ac967fe45011cc979a5ed6f869d7ae636ebb70a6448e6d249bc823957bc75a. The calibrated physical theorem has key f6ca80f6182f43861043b68b1dc3f9db084b69d9b66f014f50cd909dadfda551. [Replay driver](../../scripts/dommaschk_kam/verify_action_height_inverse.py)
