# A uniform one-way flight time below 264 throughout the pilot height band

For every N-99 birth at the phase-zero QA2R pilot with radial interpolation parameter $47/100$, the signed field line through that birth has **$14<T(h)<264$ for every height** $h_L\le h\le h_U$. Here $T$ is the normalized one-way flight integral between the two first mirrors. Computing a separate speed bound for each elapsed-angle row puts the two-sided central contribution below 224. The previously checked two outer collars add less than 40. [Physical common-path statement](../../PlasmaLean/Design/DommaschkRowFlightBudget.lean) · [N-108 collar decomposition](full-band-first-mirror-flight-times.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-109 |
| Title | Rowwise core speed bounds give a whole-band one-way flight time below 264 |
| Kind | Proof and numerical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-84, N-99, N-106, N-108 |
| Dependency requirement | Signed original field/tube gap models for rows 0–315, the all-angle arclength ceiling on the physical envelope, and the full-band first-well collar estimate. |
| Produces | A finite exact core integral budget and a uniform $14<T<264$ on the physical first wells throughout the closed pilot height interval. |
| Difficulty | Local speed varies sharply near the final core row. Each bound must refer to the actual two-sided tube on the same trajectory. |
| Status | Verified |
| Lean evidence | DommaschkRowTimeClearance.of_gap, reciprocal_le, DommaschkRowFlightBudget.from_row, Budget.append, complete, and DommaschkRowFlightBudget325.central and from_birth. |
| Audit evidence | The ground result, all twenty integral blocks and all row packages checked against the standard axioms. The exact first-row inequality rejects a smaller ceiling. |
| Last updated | 25 November 2026 |

## Rowwise estimate

On row $i$, let $\delta_i>0$ be the negative of the upper endpoint of the original enclosed polynomial $R^{16}(f^2-h_L^2)$, where $f$ is field strength. For the split last row the two archived panels give one common margin by taking their minimum. From the rational ratio $h_U/\delta_i$, choose

$$
q_i=1+\left\lfloor\sqrt{h_U/\delta_i}\right\rfloor,\qquad
H_i=h_L-\frac{1}{2q_i^2}.
$$

On the physical tube, $0<R\le1$. The exact inequality $h_L^2-H_i^2<\delta_i$ preserves the strict negative sign of $R^{16}(f^2-H_i^2)$. Both signed branches of the tube therefore have $f<H_i$. At any admitted $h\ge h_L$ their reciprocal parallel speed satisfies $1/\sqrt{2(h-f)}\le q_i$. All input polynomial products, clock bindings, exact radius comparisons, and height shifts are checked by Lean. [Threshold implication](../../PlasmaLean/Design/DommaschkRowTimeClearance.lean) · [Per-row proof construction](../../scripts/dommaschk_kam/verify_row_time_clearance.py)

The 316 integers range from 6 to 362 and sum to 5,916. At the split last row the certified common polynomial margin is exactly $9805062521428029113/2^{80}$, giving $q_{315}=362$. On row zero the certified value is 6. A replay with 5 failed at the required strict signed-gap inequality.

## Two directions on the actual birth trajectory

The Cartesian arclength density is at most $W=(8/7)h_U$. On each interval $[i/64,(i+1)/64]$ the sum of the reflected and forward time integrands is at most $2Wq_i$. Adjacent integral bounds add on their shared endpoints. Applying them to the same signed path gives

$$
\int_{-316/64}^{316/64}\!\frac{w(t)}{\sqrt{2(h-f(t))}}\,dt
\ \le\ 2W\,\frac{5916}{64}
=\frac{7839508112874584907}{35000000000000000}
=223.985946082130997\ldots .
$$

N-108 bounds the two outer collars together by 40, yielding $T<263.985946082130997\ldots<264$. The N-106 lower bound $T>14$ applies at the same height and on the same well. The birth angle satisfies $|\varphi|\le2^{-19}$. The height band contains both original rational endpoints, and the bound uses the archive's dimensionless time. [Signed integral and final combination](../../PlasmaLean/Design/DommaschkRowFlightBudget.lean) · [Uniform spatial density bound](toroidal-field-and-flight-bounds.md)

## Replay

Start with the original N-84 signed-row archives and the N-108 full-band flight receipt and its content-addressed imports. The row verifier reuses accepted artifacts when the content keys agree. The twenty integral blocks may be prebuilt independently with the block selector.

~~~bash
lake build PlasmaLean.Design.DommaschkRowTimeClearance PlasmaLean.Design.DommaschkRowFlightBudget
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_row_time_clearance.py \
  --range 0 315 --workers 3 --output /tmp/plasma-row-time-clearance-316.json
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_row_flight_budget.py \
  --flight /tmp/plasma-full-band-flight-325.json --output /tmp/plasma-row-flight-budget-325.json
~~~

There are 317 archived gap replays, 316 two-direction physical row certificates, 20 integrated blocks and one final two-theorem audit. The final module key is c4ac967fe45011cc979a5ed6f869d7ae636ebb70a6448e6d249bc823957bc75a. Its parent N-108 key is 93a23b4d823e85e24ac31cf4f814679888c11eda4acbc22c41ef80d947a5bfb2. [Assembly and receipt producer](../../scripts/dommaschk_kam/verify_row_flight_budget.py)
