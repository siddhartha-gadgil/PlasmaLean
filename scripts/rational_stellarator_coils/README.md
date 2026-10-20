# UNTRUSTED: coil design and certificate search for the rational stellarator

These scripts only *propose* candidates. Nothing in this directory is trusted. Every claim used in
Lean is checked by the kernel in

- `PlasmaLean/Design/RationalStellaratorCoilsGrad.lean`: kernel-checked bounds on `∂P`.
- `PlasmaLean/Design/RationalStellaratorCoils.lean`: gradient bound and confinement of perturbed fields.
- `PlasmaLean/Design/RationalStellaratorCoilsTF.lean`: the closed TF filament, with error `ζ = 2.5e-6`.
- `PlasmaLean/Design/RationalStellaratorCoilsTransfer.lean`: maximum-principle transfer and the
  final theorems.

The numbers below are floating-point observations (Python and numpy, in `/tmp/plvenv`). They are
**not** certified.

## Files

| File | Purpose |
| --- | --- |
| `grad_cert.py` | Generates the data and checks of `RationalStellaratorCoilsGrad.lean`. It applies the circle reduction `S² → 1 - C²` and searches cover plans with the oracle `Searcher` (`../rational_stellarator_oracle`). |
| `common.py` | The helical target `hel = (1/16)∇H` (exact formulas), sample points on the faces of `{abs(s), abs(z) ≤ a}`, and exact polygon Biot–Savart (`μ₀ = 1`). |
| `current_potential.py` | REGCOIL-type fit of a current potential `Φ(θ, φ)` on a winding torus (`R₀ = 1`, minor radius `a_w`) to `hel` on the frontier of `Ωa` (`a = 0.105`). |
| `trace_coils.py` | Traces closed filaments along the contours of `Φ` (RK4 with Newton projection, at mid-levels), then evaluates the filament field on the frontier. |
| `test_biot_savart.py` | Sanity checks for the Biot–Savart routine and for `hel`. |
| `lines*.py`, `base.py` | Straight-line (rational-field) coil experiments, kept as a negative result. |

## Results (numerical observations)

**Gradient bound.** The circle reduction plus covers gives these bounds on the cube (in units of
`2⁴⁰`):

| Quantity | Certified bound | Sampled true maximum |
| --- | --- | --- |
| `abs(∂ₛP)` | ≤ 0.405 | ≈ 0.307 |
| `abs(∂_zP)` | ≤ 0.340 | ≈ 0.252 |
| `abs(∂_CP)` | ≤ 0.0115 | — |
| `abs(∂_SP)` | ≤ 0.0070 | — |

The eight covers have 1–60 leaves each and take about 20 s in the kernel. From these,
`‖DÎ‖ ≤ 0.562` is certified; the sampled maximum on `T` is 0.311. An earlier attempt with the
`t`-chart and the weight `(1 + t²)⁵` needed about 2×10⁴ cells, because the weight varies by a
factor of 32 across the chart.

**Field-error budget** (certified, `RationalStellaratorCoils`). For `N` toroidal transits, `η` must
satisfy `(δ + η Gc)·8N < I_b - I_a`:

| Transits | Total `η` allowed | Winding error `η_h` allowed (after `ζ = 2.5e-6`) |
| --- | --- | --- |
| 10 | 5.97e-5 | 5.6e-5 |
| 1 | 6.6e-4 | 6.5e-4 |

With the sampled `‖DÎ‖ = 0.31`, these thresholds would be about 1.8 times larger.

**Continuum winding surface.** On a winding torus with `a_w = 0.3`, the current potential is
`Φ = Σ c_mn cos(mθ − nφ)` (`n = ±2`; `m ≤ 6` was enough). It reproduces `hel` on the frontier of
`Ωa` to 2.9e-6 (maximum over 2304 points). Checked at independent points with finer quadrature
(144×288 and 288×576), the error is 2.3e-6. The dominant term is the l = 2 helical mode
`cos(2θ − 2φ)`.

**Closed filaments** (contours of `Φ` at mid-levels, current `ΔΦ` each). The maximum error on
17408 frontier points is:

| Levels `N_c` | Closed filaments | Max frontier error |
| --- | --- | --- |
| 8 | 24 | 4.8e-3 |
| 16 | 52 | 1.8e-3 |
| 32 | 96 | 8.9e-4 |
| 40 | 120 | 2.4e-4 |
| 64 | 192 | 1.2e-4 |
| 96 | 288 | 1.2e-4 |

The error is largest at the outboard corners of `Ωa`, closest to the winding surface. It
stagnates at about 1.2e-4 between `N_c = 64` and `N_c = 96`. Tracing the polygons 2.7 times
finer gives the same value, so the cause is not polygonisation. The likely cause is the
mid-level contour discretization near the ridges and saddles of the multi-mode `Φ`, where the
contours are sparse. Two variants did not fix it:

- Chebyshev-type levels made the error worse for the multi-mode `Φ` (they do help for a pure
  `cos(2θ − 2φ)` mode);
- refitting the currents to the contour shapes reaches 1.5e-4 with 96 filaments, but only with
  huge cancelling currents.

So, numerically:

- about 120 closed filaments meet the one-transit threshold `η_h ≤ 6.5e-4`;
- the 10-transit threshold `5.6e-5` was **not** reached with up to 288 filaments. It needs a
  better discretization of the current sheet (the continuum sheet itself is at 3e-6).

**Straight infinite lines** (rational fields, which polynomial covers could handle) are very
inefficient:

| Lines | Max error on `T` |
| --- | --- |
| 12 (3 symmetric groups, nonlinear fit) | 1.8e-2 |
| 80 (OMP from a dictionary) | 3e-2 |
| 1056 (full dictionary) | 2e-5 |

## The certification gap (what is *not* done)

The Lean chain is complete except for one hypothesis: a frontier bound
`‖Bh − hel‖ ≤ η_h` on `∂Ωa` for a concrete finite set of winding filaments.

- **A first-order (Lipschitz) surface cover is hopeless.** With `L ≈ 2–4` for `Bh − hel` and
  `η_h ≈ 6e-4`, the grid spacing must be about `2e-4` over a frontier area of about 5 (1.3 with
  symmetry). That is 10⁷–10⁸ exact Biot–Savart evaluations, each over about 10⁵ polygon segments
  with square roots.
- **Viable routes need high-order local models of the coil field.** Two options:
  - Taylor models of Biot–Savart with Cauchy-type remainder bounds, on cells of size comparable
    to the coil distance (about 0.15).
  - An exact harmonic surrogate, followed by polynomial covers as in `RationalStellaratorCover`.

  Either needs new Lean infrastructure for enclosures of segment fields, which contain square
  roots.
- **Cheaper improvements to the budget:**
  - a sharper `Gc`: the true value 0.31 gives a factor of 1.8;
  - a smaller start tube, which lowers `I_a`;
  - certifying `‖Bh − hel‖` only on `T ∩ {I ≤ I_b}`, which still needs the frontier route.
