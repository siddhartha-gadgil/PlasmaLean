# A physical field line through three projected Jacobian boxes

For the Dommaschk QA2R birth family at section zero and $u=0.470$, one physical field-line trajectory now follows 72 consecutive forward slabs, including every join. The forward toroidal angle reaches $72/64=9/8$ radians. For every admitted birth phase $|\varphi|\le 2^{-19}$, the uniform Euclidean position error in dimensionless $(R,z)$ is at most $2676379663306118010/2^{80}<2.214\times10^{-6}$. The separate signed theorem of N-71 reaches $[-1,1]$ radians from one transferred birth. [Forward proof generator](../../scripts/dommaschk_kam/verify_physical_trace_prefix.py) · [Signed proof](dommaschk-one-radian-and-signed-trace.md)

## New Jacobian bounds

Row 68 required eight time panels on the original spatial square. For rows 69–71, projecting the actual trial ellipsoid onto its two coordinate axes gives a narrower radial and vertical box. The rectangle contains the forward trial and the reflected backward trial, and the spatial rate satisfies the stricter of the two allowances. Lean checks the containment using the four endpoint row norms. The bounded field polynomial, its derivatives, and the moving-frame quadratic form are all evaluated on these same boxes. Lean also checks the positive denominator and growth inequality in the physical step. [Rectangle membership](../../PlasmaLean/Design/DommaschkProjectedTrial.lean) · [Rectangular Jacobian certificates](../../scripts/dommaschk_kam/emit_rectangular_jacobian.py)

The first lower-height mirror is bracketed by the archived trace in row 316 and the higher-height mirror in row 324. The connected physical path reported here ends at row 71. The interval certificates apply to the magnetic field-line ODE. A thermal guiding-centre result requires the additional bounce-action and drift estimates in the contract.

## Reproduce

Start with the on-demand dependencies and certificates in N-71. Build the harmonic block for rows 64–71 (`PlasmaLean.Design.DommaschkHarmonicBlock08`) and the `DommaschkJacobianPanels` and `DommaschkProjectedTrial` modules. The central residuals through row 71 and the ordinary shared-power Jacobians through row 67 must be present. From the repository root run:

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_explicit_jacobians.py --range 68 68 --square-panels
.venv-ws/bin/python scripts/dommaschk_kam/verify_explicit_jacobians.py --range 69 71 --workers 3
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_prefix.py --length 72 --shared-from 16 --square-panels 68 --projected 69 70 71
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-74 |
| Title | A physical field line through three projected Jacobian boxes |
| Kind | Physical trajectory certificate |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-66, N-70, N-71 |
| Dependency requirement | Each physical row uses its actual inherited ellipsoid, an authenticated reference defect, a positive field denominator and a Jacobian bound on that trial region. |
| Produces | A connected, 72-slab forward trajectory and an independent explicit-Jacobian verifier. |
| Difficulty | Extending the continuous trajectory to the first mirror and matching the field-strength signs on that trajectory. |
| Status | Compiled Lean theorem with a uniform physical tube estimate for the stated launch family. |
| Lean evidence | On-demand `DommaschkPhysicalPrefix072.exists_nested_prefix`, `DommaschkPhysicalPrefix072.uniform_tube_error`, and the row declarations `physical_step`. |
| Audit evidence | All four prefix declarations passed the standard-axiom audit. Prefix key `5b2044da4579`. |
| Last updated | 24 November 2026 |
