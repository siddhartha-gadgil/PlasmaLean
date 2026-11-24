# Field-strength margins on four physical births of one phase-zero torus family

For a single pair of embedded nested QA2R tori and every original launch angle $|φ_0|≤2^{-19}$, Lean certifies four actual phase-zero field lines. The pilot at radius $0.470$ carries its calibrated first-mirror action and flight-time observables. Each of the other three lines passes through its own original torus-interpolated birth at the same $φ_0$, solves the signed angular ODE, and obeys a strict field-strength margin on the interval in this table. [Original-birth margin proof](../../PlasmaLean/Design/DommaschkOriginalBirthMargin.lean) · [Calibrated pilot and ordered tubes](compared-physical-birth-arcs.md)

| Interpolation label | Certified interval of absolute azimuth | Strict field bound | Signed tubes observed |
| --- | --- | --- | ---: |
| $0.478$ | $[-4,4]$ | $\lVert B\rVert<h_L-1/270000$ | 512 |
| $0.523$ | $[-3/4,3/4]$ | $\lVert B\rVert<h_L-1/100000$ | 96 |
| $0.531$ | $[-1/4,1/4]$ | $\lVert B\rVert<h_L-1/50000$ | 32 |

Here $h_L=5297961656084411/5000000000000000$. The full ordered enclosures at the three labels respectively cover 317, 322 and 323 slab pairs. The displayed physical bounds use the signed physical trajectory as far as both signs have been verified. Each applies pointwise, including both ends of the interval.

## Which line carries the observable?

At each secondary label $e$ the proof returns a function $y_e(t)$ satisfying $y_e(φ_0)=\mathrm{birth}(u_C,z_C,u_A,z_A,e,φ_0)$ in the physical radial and vertical coordinates. The signed ODE, the chronological enclosures in both directions and the strength bound all apply to this one function. The underlying phase-zero section entry allows a short approach from $φ_0$ to zero. The proof identifies its initial point with $y_e(φ_0)$ by ODE uniqueness. It obtains the required smoothness from the verified radial and vertical enclosure on the actual signed tubes. The three secondary witnesses can be chosen after the common tori and the launch phase, before any observation time. The same tori also retain the original passages at the four opposite-section labels. [Original-position uniqueness](../../PlasmaLean/Design/DommaschkPhaseZeroRegularBirth.lean) · [Physical-family replay](../../scripts/dommaschk_kam/verify_common_original_margins.py)

There are 640 signed secondary slabs in the three displayed intervals. The four phase-zero physical trajectories are sampled at discrete radial interpolation labels. A claim about a continuum of radial labels needs information between those values. The strict field inequalities alone give no first-mirror crossing at the end of an observed interval.

The stronger two-line comparison now holds over this same eight-radian interval at matching azimuth. Its key is `1247519f9f35193ff52d2a6485ae00d7b62d4564fb7c0d468868515daa19f048`. In the near-upper height range the true outer action between −4 and 4 is at least 397357225604069861/1055531162664960000, strictly greater than 47/125. Its key is `60d0d5a3323ce344987c69fb3c6b684c16b017746429daf8a73dc1527bb7250d`. [Compared profiles](compared-physical-birth-arcs.md) · [Near-upper height interval](secondary-near-upper-first-wells.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-158 |
| Title | Field-strength margins on four physical births of one phase-zero torus family |
| Kind | Theorem and physical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-135, N-141, N-147, N-149 |
| Dependency requirement | Authenticated ordered field margins, the two signed physical tube lists at each radius, regular vacuum geometry and a common torus-pair witness. |
| Produces | Strength inequalities on the original physical field lines at three secondary radii on the same tori as the calibrated pilot and the full eight-sector family. |
| Status | Kernel verified for 256, 48 and 16 consecutive pairs respectively. |
| Lean evidence | `DommaschkOriginalBirthMargin.from_passage` and `DommaschkOriginalBirthMargins391_256_48_16_48_16_5_5.from_common_tori`. |
| Audit evidence | The generic theorem, the three endpoint applications and the common family have only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Reproduction

Use the unchanged complete ordered N-135 receipts and the N-149 calibrated physical-family receipt. The length at each radius is the minimum of its own physical prefix and its own ordered field certificate.

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkOriginalBirthMargin
.venv-ws/bin/python scripts/dommaschk_kam/verify_common_original_margins.py \
  --calibrated /tmp/plasma-calibrated-at-256.json \
  --clearances /tmp/plasma-n135-q0r478-317.json /tmp/plasma-n135-q0r523-322.json \
    /tmp/plasma-n135-q0r531-323.json \
  --output /tmp/plasma-common-original-margins256.json
```

| Checked input or conclusion | Proof key |
| --- | --- |
| Calibrated family with 256 pairs at $0.478$ | `4db9869150013a8c18346bdccb5889d86de73456db711f18f1e5ce80aa7d091f` |
| Ordered margin at $0.478$ | `073471cfdf5da3891484ecdebfb9ed1927dde4092c20e6c55b6df1f2f90606b6` |
| Ordered margin at $0.523$ | `b1218efa39d5837caa6fda7c14790019ffb308f50b87e96339b25433ad261c84` |
| Ordered margin at $0.531$ | `dae817183e57226d55e1118fbae7814a865e73441d2a84347fe464476594daca` |
| Four original births on the common tori | `9b2bd8ddd94cf017b3b5a3fcd15ae2ba008ba62d77eb6ab09b6ae6b1f96abd44` |

On the workstation the final physical proof and its declaration audit took 37.59 seconds on one worker with a peak resident size of 23.02 GiB.

The preceding 224/48/12 common-family replay also passed under proof key `562efb7835f4ac377ef81f644baee315cc068f12ee9171bd6a8e7c70eff96199`.
