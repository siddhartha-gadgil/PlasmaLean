# Magnetic flux and a two-sided field-line enclosure for the deep launch strip

[N-57](dommaschk-regular-mirror-cell.md) continues a smaller cell to both mirrors and encloses its action.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-56 |
| Kind | Method and computation for N-54 |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-33, N-52 for the certified Fourier profiles, N-53 for the band acceptance test, N-54 for the mirror-height screen |
| Dependency requirement | A positive cylindrical radius and toroidal field component, bounded spatial derivatives on each tube, and enclosures for the true launch profiles and field. |
| Produces | A nonvanishing launch flux density and a field-line segment strictly inside the proposed mirror well for every launch phase and radius in the strip. |
| Difficulty | Moderate for a short segment. Over a full bounce, rectangular propagation loses correlations between coordinates and launch parameters. |
| Status | Flux identity, flux lower-bound theorem and ODE enclosure theorem verified in the default build. Candidate numerical inequalities externally checked with outward rounding. |
| Lean evidence | `Forms.interpolated_launch_flux`, `Forms.launch_flux_lower_bound`, `Fields.RectangularODEStep.exists_step`, `tube_of_endpoints`. |
| Audit evidence | Exact polynomial comparison with the identified field, checks against known solutions and two time subdivisions, full-strip rerun. |
| Alternatives | N-57 uses a centred trajectory and signed spatial growth bound. |
| Last updated | 23 November 2026 |

## Launch and clock

At θ=0, interpolate the cylindrical coordinates of C and A with u in [11/25,27/50]. The toroidal launch angle α runs through a full field period of π. The calculation includes the KAM error of each true torus relative to its packed Fourier seed, including the geometric-azimuth derivative. Between launches, the field line follows (R′,z′) = (nR/D,nZ/D), with τ = φ − α in geometric radians. These ratios use physical cylindrical components through R Bᵣ/Bφ and R Bz/Bφ. [Launch construction](../../scripts/dommaschk_kam/bounce_launch_box.py) · [Field identification](../../PlasmaLean/Design/DommaschkKamFieldData.lean)

## What holds on the continuous strip

| Domain | Externally checked bound in candidate units |
| --- | --- |
| All launches, 32,768 boxes | ‖B‖ ≤ 1.048, Bφ ≥ 1.03, and B·(Xᵤ × Xα) ≤ −17 × 10⁻⁶ |
| All intermediate angles −1/8 ≤ τ ≤ 1/8, 131,072 tubes | ‖B‖ ≤ 1.057107, Bφ ≥ 1.026436, and each absolute coordinate speed is ≤ 0.141692 |

The first row gives a lower bound of 17π/10⁷ for the magnetic flux through the parametrized rectangle over one field period, with the positive orientation chosen by reversing the displayed normal. The geometric flux identity and integration bound are Lean theorems. A trapped-birth probability requires a distribution and a treatment of possible repeat representations of one physical well. [Magnetic two-form and integral](../../PlasmaLean/Theory/Fields/CylindricalLaunchFlux.lean)

The second row clears 1.0595 throughout the segment. Both proposed mirror heights, 1.05959233 and 1.06010928, exceed this test value. Each field line exists through the segment in both directions and its arclength increases with geometric toroidal angle. Beyond this interval the location and simplicity of the two mirror crossings still need a continuum enclosure. [Field-line verification](../../scripts/dommaschk_kam/bounce_collar.py)

## Soundness of a step

On a compact spacetime tube enclose each component of the field-line velocity in an interval. For each incoming position x and intermediate time t, verify that x + tV lies in the state tube. Lean proves existence through the step for a time-continuous field, uniformly Lipschitz in space there, and proves the sharper enclosure x(T) ∈ x + TV. Its proof first clips spatial coordinates to the tube, solves the extended equation, and applies the scalar mean-value theorem in each coordinate. The computed tube inclusion then makes the clipped solution an exact solution of the original equation. The rational field is smooth in each checked tube because R and D are strictly positive. Backward integration uses the reversed clock and velocity. The transfer of the actual numeric tube bounds is currently checked in Python. [Rectangular step theorem](../../PlasmaLean/Theory/Fields/RectangularODEStep.lean)

## Reproduction and next calculation

Run the following from the repository root.

```sh
python3 scripts/dommaschk_kam/bounce_launch_box.py
python3 scripts/dommaschk_kam/bounce_collar.py
python3 scripts/dommaschk_kam/bounce_collar.py --step 1/192 --steps 24
```

The default collar uses 32 steps of length 1/256 in each direction. Its exact upper strength and lower Bφ numerators over 2⁵² are 4760782819015032 and 4622658070064464. The independently subdivided run with 24 steps also clears 1.0595. A finer run with 384 cells per quarter circle and 40 steps of length 1/320 checked 245,760 tubes. It gives the strength and Bφ numerators 4748179136332464 and 4630120678144070 over the same denominator. The source checks the harmonic recombination against exact rational polynomials and reproduces a constant-velocity field line in both directions.

Box widening already loses the 1.0595 test at τ=39/256 in one forward cell (second quarter-circle chart, cell 128/256, u in [0.44,0.49]). The enclosure there allows ‖B‖ as large as 1.059729. A physical crossing cannot be inferred from that upper bound. For extending toward the turning points, test an enclosure that transports deviations from a central trajectory using its derivative. It must keep track of the two independent launch parameters and the distance to other mirror wells. Once both crossings are certified, the next obligations are the action derivative, graph separation and the error between the reduced and particle dynamics. Length scale, field scale and thermal acceptance targets remain open by user decision. [Full bounce-screen data](../../scripts/dommaschk_kam/results/bounce_screen_20261123.json) · [Acceptance criteria](hamiltonian-bounce-band-test.md)
