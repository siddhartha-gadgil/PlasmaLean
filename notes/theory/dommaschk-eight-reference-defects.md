# First-slab ODE defects at eight physical launches

At each of the eight endpoints of the Dommaschk action archive, Lean checks the error in the central reference curve against the physical field-line ODE throughout the first slab in both directions. The four radii on the section `φ = 0` are 0.470, 0.478, 0.523 and 0.531. The four on `φ = π/2` are 0.456, 0.464, 0.509 and 0.517. The signed physical angle is the section angle plus or minus the outward parameter $t$, with $0\le t\le 1/64$. [Endpoint verifier](../../scripts/dommaschk_kam/verify_endpoint_reference_slabs.py)

Write $x(t)$ for the archived polynomial curve in physical coordinates, $F$ for the directed field-line vector field, and $M(t)$ for the archived moving frame. The certified inequality at every such $t$ is

$$
\left\|M(t)^{-1}\bigl(F(t,x(t))-x'(t)\bigr)\right\|_2\le d,
$$

where $d$ is the exact defect budget from the corresponding source slab. At the opposite section, shifting the physical angle by $\pi/2$ reverses both first-harmonic models, including their polynomial centres, and preserves the error radii. This lets the same generator check all eight launches in their own coordinates. The two proofs at radius 0.470 were already available. The fourteen additional proofs have been generated, compiled and individually audited. A physical trajectory enclosure at a new launch additionally needs the Jacobian on the entire trial tube, entry and transfer in the same frame. [Physical harmonic shift](../../PlasmaLean/Design/DommaschkOppositeHarmonic.lean) · [Proof generator](../../scripts/dommaschk_kam/emit_sparse_trace_defect_samples.py)

## Can nearby launches share a derivative estimate?

For an upper growth estimate $\mu_c$ on a central trajectory and a spatial Hessian bound $H$, the test allows growth up to $\mu_c+\kappa_2(M)H\rho$, where $\rho$ covers the distance from the chosen centre to the trial tube. All 176 samples with the launch's own centre met their archived budgets. These cover 11 selected slab indices in both directions at each endpoint and used 50 distinct boxes. Hessian upper bounds ranged from 37.46 to 172.24 after outward rounding to two decimals. Sharing a centre with a neighbouring launch passed only 32 of 88 samples even with a finer spatial grid and four time panels. These counts come from external rational interval arithmetic. Continue the projected Jacobian proof on each launch's own tube. A same-centre Hessian proof remains an alternative for difficult slabs. [Reproducible screen](../../scripts/dommaschk_kam/screen_hessian_transfer.py)

## Reproduce

Build the physical field and harmonic prerequisites once. The residual verifier checks their freshness and stores each generated proof and axiom audit under its content hash.

```sh
lake build PlasmaLean.Design.DommaschkBounceTaylor PlasmaLean.Design.DommaschkFramedTaylorResidual PlasmaLean.Design.DommaschkOppositeHarmonic PlasmaLean.Design.DommaschkHarmonicBlock00
.venv-ws/bin/python scripts/dommaschk_kam/verify_sparse_reference_slabs.py --range 0 0 --workers 1
.venv-ws/bin/python scripts/dommaschk_kam/verify_endpoint_reference_slabs.py --endpoints q0r478 q0r523 q0r531 q1r456 q1r464 q1r509 q1r517 --range 0 0 --workers 2
.venv-ws/bin/python scripts/dommaschk_kam/screen_hessian_transfer.py --expect 176 176
.venv-ws/bin/python scripts/dommaschk_kam/screen_hessian_transfer.py --neighbor --grid 1024 --time-panels 4 --expect 32 88
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-83 |
| Kind | Physical central-reference residuals and method assessment |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-64, N-66, N-68 |
| Dependency requirement | Matching signed field, phase, central polynomial, affine frame, defect budget and harmonic packet. |
| Produces | Sixteen first-slab defect bounds, two per endpoint, plus a comparative external screen of Jacobian transfer. |
| Difficulty | Uniform derivative bounds and directed entry are needed to propagate physical trajectories at the other seven launches. |
| Status | The sixteen concrete residual bounds have passed Lean. The Hessian transfer comparison has passed the stated external replay. |
| Lean evidence | `DommaschkOppositeHarmonic.first` and generated `.physical_defect` declarations for each launch and direction. |
| Audit evidence | The sixteen residual theorems use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 24 November 2026 |
