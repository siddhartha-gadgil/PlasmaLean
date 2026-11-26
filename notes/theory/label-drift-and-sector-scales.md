# Label drift of guiding centres and the scales of the QA2R first-well sector

**26 November 2026.** Along a Littlejohn guiding centre, a function that is constant on field lines changes only through the cross-field drift. Lean now proves the exact rate and a direct first-order bound for it. A numerical screen of that rate on the certified QA2R sector shows that the sector is far too small, in phase and in radius, to carry a band-form C2 claim for thermal particles: at 10 keV the guiding centre leaves the certified phase window after about 5·10⁻¹⁰ s. C2 remains open. The note states what a usable certificate needs instead.

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-214` |
| Title | Label drift of guiding centres and the scales of the QA2R first-well sector |
| Kind | Proof (general theorem), computation (untrusted screen) and obstruction study; method note for N-53 |
| Addresses | G-10, G-8, Q-35, Q-1; RG.5 item 2 (C2 on the actual field) |
| Depends on | N-53, N-122, N-199, N-205, N-206, N-210, N-213; `VacuumLittlejohnLocal.parallel_eq_norm`, `DommaschkHeightBandActionExit.stays_inside` |
| Dependency requirement | The Littlejohn equations as a supplied model; the vacuum identity `B*_∥ = ‖B‖`; the statement of the first-exit theorem with its hypotheses `Observes` and `drift`; the certified sector (labels 0.470–0.478, phases within 2⁻¹⁹, height band at `level`). |
| Produces | Compiled label-rate identity and direct drift bound; normalized drift coefficients of the sector (untrusted); thresholds on ε = ρ/R₀; requirements for a thermal band certificate. |
| Difficulty | The theorem is routine. The certificate it points to is research: full-period wells, moving faces, and an averaged drift estimate with a corrector. |
| Status | General theorem verified (default build). Sector scales: numerical observation (untrusted). Use of the present sector for a thermal `BandContract`: obstructed at the stated scales. |
| Lean evidence | `PlasmaLean/Theory/Kinetic/LabelDrift.lean` (default build): `LabelDrift.rate`, `label_hasDerivAt`, `rate_vacuum`, `abs_rate_vacuum_le`, `label_displacement_le`, `rate_const`. Standard axioms only. |
| Audit evidence | Not audited. Numerics: `scripts/dommaschk_kam/screen_label_drift.py`, results `scripts/dommaschk_kam/results/label_drift_20261126.json`. |
| Last updated | 26 November 2026 (created) |

## Purpose and scope

The first-exit theorem of N-206 keeps a path inside the radial strip 0.470 < u < 0.478 as long as its initial action mismatch plus its action drift is at most 249/250000, provided that at every possible exit the path is observed with phase within 2⁻¹⁹ of zero and height in the top band. N-210 names the drift estimate for physical guiding centres as the missing step. This note supplies the first quantitative statement about that drift and tests whether the present sector can meet the hypotheses for a thermal population.

Model: the static Littlejohn guiding-centre equations (`GCBirthOrbitOn`, a supplied model; no collisions, no electric field). Field: the QA2R vacuum field in its model normalization. Outside scope: the derivation of the model from the Lorentz force, averaging over the bounce motion, and any population fraction.

## The general theorem (compiled Lean, default build)

Call L a **label** if ∇L·B = 0. For a state (X, v∥) and moment μ define

$$
\mathrm{rate}(X,v_\parallel)=\frac{1}{B^*_\parallel}\Bigl(\frac{m v_\parallel^2}{q}\,\nabla L\cdot(\nabla\times b)+\frac{\mu}{q}\,\nabla L\cdot(b\times\nabla|B|)\Bigr).
$$

- **`label_hasDerivAt`.** If z solves the Littlejohn equation at time s, L is differentiable at the position and ∇L·B = 0 there, then d/dt L(X(t)) = rate at s. The parallel motion drops out; no vacuum hypothesis is used.
- **`rate_vacuum`.** If B is nonzero, differentiable and curl-free at x, then rate = (m v∥² + μ|B|)/(q|B|²) · ∇L·(b × ∇|B|). The curvature and gradient drifts combine, as in the textbook vacuum drift.
- **`abs_rate_vacuum_le`.** With m ≥ 0 and μ ≥ 0, |rate| ≤ 2H/(|q||B|²) · ‖∇L‖ ‖∇|B|‖, where H = m v∥²/2 + μ|B| is the Hamiltonian.
- **`label_displacement_le`.** For an orbit on [0, T] from the birth b, if L is a differentiable label along it and |rate| ≤ ρ at the states visited, then |L(X(t)) − L(b.1)| ≤ ρ t for 0 ≤ t ≤ T.
- **`rate_const`** (sanity). In a uniform field every rate is zero.

Hypotheses to keep in view: the orbit is supplied; the label and its gradient are inputs. For the QA2R sector a label is not yet constructed in Lean (the natural ones are the section coordinates of the field line, below). The bound has no bounce averaging, so it is a statement on the scale of one bounce.

## Sector scales (numerical observation, untrusted)

Units: lengths in the model unit R₀ (the births lie at R ≈ 0.9955), field in the model unit B₀ (|B| = 1.0440 at the births), time in R₀/v with v the particle speed, and ε = m v/(|q| B₀ R₀) = ρ/R₀. Labels: the coordinates (R, z) at which the field line through the guiding centre crosses the section φ = 0 inside the same well. The script traces the field line through the first well at the certified height, transports the vacuum drift velocity to the section with the inverse of the variational matrix, and integrates over a half bounce.

| Quantity at the certified height 1.060109 | u = 0.470 | u = 0.474 | u = 0.478 |
| --- | --- | --- | --- |
| First well (toroidal angle, radians) | ±5.072 | ±5.083 | ±5.095 |
| Action J (target 1.359922) | 1.356134 | 1.359604 | 1.363101 |
| Half-bounce time (R₀/v) | 129.1 | 130.2 | 131.4 |
| Largest radial label excursion in a half bounce | 24.6 ε | 24.9 ε | 25.3 ε |
| Net radial label change per half bounce | 0 | 0 | 0 |
| Net transverse label change per half bounce (precession) | 54.5 ε | 54.9 ε | 55.4 ε |

Further numbers: the radial strip 0.470–0.478 is 8.37·10⁻⁵ wide; the distance between tori C and A on the launch line is 0.01046; the action slope across the strip is 83.3 per unit length; the certified phase window |φ| ≤ 2⁻¹⁹ corresponds to a transverse label half-width of 9.2·10⁻⁹.

Checks on the screen. The actions agree with the certified face inequalities of N-206 (inner face below the target minus 0.000996, outer face above the target plus 0.0019). The net radial change vanishes, as stellarator symmetry requires on the launch line. The precession agrees with the bounce-averaged Hamiltonian relation Δz = ε (∂J/∂R)/(√(2h) B_φ) per half bounce: 83.3/(1.456·1.044) = 54.8. This last agreement is an independent check of the drift computation.

The well is shallow: |B| at the birth is 1.5 % below the mirror height, so v∥/v ≤ 0.12, the half bounce takes about 20 toroidal transits, and the banana excursion per unit ε is large. Lower heights give somewhat narrower bananas (21 ε at height 1.058, 14.6 ε at 1.05) with a similar precession.

## Consequences for a band-form claim on this sector

**Conditional inference from the numerical observation.**

1. **Phase window.** The precession moves the guiding centre's field line across the certified window in a fraction 9.2·10⁻⁹/(54.9 ε) of a half bounce. Staying inside for one half bounce needs ε ≤ 1.7·10⁻¹⁰.
2. **Radial strip.** The banana excursion exceeds the half-width of the strip unless ε ≤ 1.7·10⁻⁶. Read as an instantaneous action change, it uses the whole budget 0.000996 unless ε ≤ 4.9·10⁻⁷.
3. **Illustrative thermal scales** (10 keV, B₀ = 5 T, R₀ = 10 m; the project has not fixed a device scale): deuterons have ε = 4.1·10⁻⁴ and electrons ε = 6.7·10⁻⁶. The drift speed ε v depends on the energy and charge only, so both species leave the phase window after about 5.5·10⁻¹⁰ s. The deuteron banana excursion, about 0.010, is as large as the whole gap between tori C and A; the electron excursion, 1.7·10⁻⁴, is twice the strip width and 1.6 % of the gap.

So a `BandContract` proved through the present sector would have a horizon near 10⁻⁹ s for thermal particles, which is no better than the ballistic bound. **The local sector certificate cannot be the basis of a thermal C2 band.** This is a limit of the certificate's size, not evidence against confinement in the field.

## What a usable certificate needs

1. **Labels as section coordinates** with certified gradient bounds along the well, so that `label_displacement_le` applies. The variational matrices of the signed traces are already enclosed by the campaign.
2. **Radial windows wider than the banana excursion**: at least 2·25 ε, about 3.4·10⁻⁴ for the illustrative electrons (four times the present strip). For the illustrative deuterons the window would have to span the nested region, so a deuteron band needs wells certified over the whole region inside torus A, or a larger device scale.
3. **Every precession phase.** The transverse label moves by about 55 ε per half bounce, so a particle visits all phases. This needs the global well family and moving faces of N-212. N-190 and N-195 show that the target action level leaves the strip 0.470–0.478 at other phases; the radial motion of that level over a period is then the physical excursion, and it is the quantity to bound.
4. **An averaged drift estimate.** The banana oscillation of the action must be removed by a corrector (the form `stays_inside_of_correction` of N-206), with the precession governed by ∂J/∂R as checked above. The direct bound of this note supplies the first-order term only.
5. **Fixed inputs first** (N-213): species, energy and pitch windows, birth law, horizon, excursion and fraction, stated before the proof.

## Reproduction

```bash
lake build PlasmaLean.Theory.Kinetic.LabelDrift
cd scripts/dommaschk_kam
../../.venv-ws/bin/python screen_label_drift.py --output results/label_drift_20261126.json
../../.venv-ws/bin/python screen_label_drift.py --labels 0.470 0.478 --height 1.05
```

The screen is double-precision and unvalidated. The gradient of |B| and the variational matrix use central differences.

## Open questions

- A certified enclosure of the label gradients on the signed traces (routine with the existing Jacobian certificates).
- Whether the precession relation Δz ∝ ∂J/∂R can be proved for the Littlejohn model on a regular well family (it would turn the action slope bounds of N-161 and N-162 into precession bounds).
- The choice of height class: deeper wells have narrower bananas; the campaign used the top band.
