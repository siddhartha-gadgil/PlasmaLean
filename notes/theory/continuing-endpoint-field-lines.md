# Continuing signed field lines at the other QA2R birth labels

The phase-zero QA2R endpoint $u=239/500$ has a physical field line on $[-1/32,1/32]$ after its approach to the canonical section. The theorem holds for every admitted birth angle in that endpoint's sector. Both directions use the state reached by the physical approach. A second theorem places these births and the $u=47/100$ pilot births on one common pair of nested Q-16 tori. The opposite-section family at $u=57/125$ near $\pi/2$ also has two signed slabs in each direction and a common-torus comparison with the pilot. This supplies two independent checks of the continuation theorem across different launch geometries. The second label still needs its own first mirror contacts and action estimates. [Signed-trace interface](../../PlasmaLean/Design/DommaschkEndpointSignedTrace.lean) · [Continuation theorems](../../PlasmaLean/Design/DommaschkEndpointContinuation.lean)

## Mathematical statement

Let $e$ denote an archived endpoint, $\alpha$ its section angle, and $n$ the number of accepted consecutive rows on each side. For every $\phi$ with $|\phi-\alpha|\leq e.\mathrm{width}$, the physical approach takes the interpolated birth on the two certified tori to a state $x$ at the section. There is a single function $y$ with $y(0)=x$ that satisfies the physical real-angle field-line ODE throughout $[-n/64,n/64]$, including derivatives within the interval at the joins. For each $i<n$ and $i/64\leq t\leq(i+1)/64$, the forward tube contains $y(t)$ and the backward tube contains $y(-t)$. At both terminal times the solution belongs to the corresponding archived exit ellipsoid. All angles and position coordinates are in the normalized model units. [Physical chain and birth definitions](../../PlasmaLean/Design/DommaschkEndpointSignedTrace.lean)

The forward proof covers the trial ellipsoid by a rectangle whose coordinate widths are the largest needed by either signed partner. For the backward partner, the coefficientwise discrepancy between the reflected reference and the forward centre is charged to each rectangle width before evaluating the field. The same analytic Jacobian bound must satisfy both signed logarithmic-norm budgets. Each direction retains its own reference, physical central defect, outgoing radius and frame. The determinant, denominator and ODE estimates hold on the entire row. Consecutive rows must have exactly matching exit and entrance states. [Projected trial geometry](../../PlasmaLean/Design/DommaschkProjectedTrial.lean) · [Shifted reflected trial](../../PlasmaLean/Design/DommaschkShiftedTrial.lean) · [Endpoint verification](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## Checked endpoints

| Section and label | Slabs each way | Signed angular extent | Kernel content key |
| --- | ---: | --- | --- |
| $0$, $239/500$ | 2 | $[-1/32,1/32]$ | `2efeb26ab2bdf325fe3e42ed043febb703e332f669e41f6820cf6693ffa4f5e6` |
| $\pi/2$, $57/125$ | 2 | $[-1/32,1/32]$ relative to the section | `10bbd86bffe54449f70a2aac6af15d5406d0e2e4f5c43d30638ab5c222ecf568` |

At the opposite section, all $|\phi-\pi/2|\leq 2^{-20}$ are admitted. In the second slab at $u=57/125$, the coefficientwise reflected vertical-centre discrepancy is $766427026/2^{80}$. The paired rectangle includes this displacement and the backward trial ellipsoid. [Opposite-section witness](../../scripts/dommaschk_kam/results/bounce_frame_q1_u456.json.gz)

The second q0r478 slab has different entrance frames in the two directions, with off-diagonal entries $-1594010719$ and $1594010719$ in units of $2^{-40}$. The first entrance also differs from the second in its scalar frame radius. Both distinctions were checked in Lean. Exchanging the direction, packet digest or endpoint label of an imported residual is rejected by the verifier. The maximum physical outgoing radius on these four signed rows is $1490825445979619184/2^{80}$, about $1.234\times10^{-6}$. [Original witness](../../scripts/dommaschk_kam/results/bounce_frame_q0_u478.json.gz)

## Reproduction

Generate the two first-row physical launch reports as in N-91. The following commands independently produce the next two signed residuals and their joint spatial Jacobian, then compose them with those launches.

```sh
lake build PlasmaLean.Design.DommaschkEndpointContinuation
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
$py "$dir/verify_endpoint_reference_slabs.py" --endpoints q0r478 --range 1 1 --workers 1 --shared --output /tmp/endpoint-residual1.json
$py "$dir/verify_endpoint_forward_jacobians.py" --endpoints q0r478 --range 1 1 --workers 1 --paired-trials --output /tmp/endpoint-jacobian1.json
$py "$dir/verify_endpoint_signed_prefix.py" --endpoint q0r478 --length 2 --forward-launches /tmp/plasma-all-eight-physical-launches.json --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json --references /tmp/endpoint-residual1.json --jacobians /tmp/endpoint-jacobian1.json --output /tmp/plasma-signed-q0r478-2.json
```

The generated `from_entry` theorem can be instantiated on any certified section entry for this endpoint. The `from_birth` and `common_with_pilot` theorems supply actual Q-16 tori and all admitted births. The existing N-91 launch modules serve as the first steps in their original forms. [First-slab proof](../../PlasmaLean/Design/DommaschkEndpointFirstSlab.lean) · [Consumer](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-102 |
| Title | Continuing signed field lines at the other QA2R birth labels |
| Kind | Reusable theorem and physical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-91 |
| Dependency requirement | Archived position and moving-frame steps, the physically realized Q-16 section entries, signed central defects and whole-tube Jacobian proofs. |
| Target | Multi-slab signed physical trajectories at a second radial label and a reusable comparison on the same nested surfaces. |
| Difficulty | Each side has its own reference, growth allowance and predecessor. Reflected references at the opposite section can differ. |
| Status | Verified on two slabs in each direction at q0r478 and q1r456. |
| Lean evidence | `DommaschkEndpointContinuation.forward_rectangle`, `cons_step`, `with_pilot_of_entry` and the generated `DommaschkSignedPrefixQ0R478002.common_with_pilot` and `DommaschkSignedPrefixQ1R456002.common_with_pilot`. |
| Audit evidence | All five concrete declarations use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
