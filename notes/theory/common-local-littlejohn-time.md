# A common Littlejohn time and displacement cap for both QA2R velocity signs

For any prescribed displacement cap $d>0$, the two velocity signs at an original QA2R pilot birth have open neighborhoods of trapped births and a **single time $T>0$** on which every birth in either neighborhood moves less than $d$ from its own starting position. Each birth has a solution of the actual Littlejohn equation on $[0,T]$. Every solution defined on any initial subinterval $[0,t]$ obeys the displacement cap at $t$, has nonzero magnetic field there, and satisfies $B^*_\parallel=\|B\|>0$. [Ground declarations](../../scripts/dommaschk_kam/verify_common_littlejohn_time.py) · [Five-dimensional local flow](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnWindow.lean)

## Quantifiers and physical meaning

Fix a pilot birth with $|\varphi|\le 2^{-19}$ at the phase-zero, radius-0.470 launch, a mass $m>0$, a charge $q\ne0$, an energy $e>0$, and a height $h$ between the two archived heights, inclusive. In the QA2R field normalization the exact endpoints are $5297961656084411/(5\cdot10^{15})$ and $5300546391395933/(5\cdot10^{15})$. At the original interpolated position $x$, the two lifts have $\mu=e/h$ and $v_\parallel=\pm\sqrt{2(e-\mu\|B(x)\|)/m}$. The strict birth-strength bound places one lift in each strict velocity sign. The energy and pitch cuts can be supplied in advance provided their interiors contain $e$ and $1/h$. Each sign can also use a support cut whose interior contains its lift. [Coordinate lifts](../../PlasmaLean/Theory/Contract/TrappedBirthCoordinates.lean) · [Closed height band](../../PlasmaLean/Design/DommaschkFirstMirrorLaunchSign.lean)

The duration and neighborhood sizes may depend on the inputs, including the displacement cap and the central birth. For any birth law $\nu$ that charges every nonempty open set, each neighborhood has positive mass. This applies in particular to five-dimensional Lebesgue volume. To obtain the project's full field-level radial-band contract, choose a common support, a nonempty compact axis, and suppose the resulting trapped reference $R$ is measurable and has finite $\nu$-mass. The union $W$ of the two neighborhoods satisfies `GuidingCentreBand` for this same $T$ and $d$, with exact fraction $f=\nu(W)/\nu(R)>0$. The theorem also proves that $W$ has positive mass in each velocity sign. The prescribed reference may be larger than $W$. [Candidate theorem](../../PlasmaLean/Design/DommaschkCommonLittlejohnTime.lean) · [Definition of the band contract](../../PlasmaLean/Theory/Contract/TrappedBirthBand.lean)

This local ODE argument works at every regular vacuum seed. It gives no computable lower bound on $T$ or $f$. The confinement question at a specified thermal horizon and coverage fraction remains open, as do the field and length scales, particle distribution, and operating point needed to report a time in seconds or an excursion in metres.

## Proof

1. Append $\dot\mu=0$ to the contracted Littlejohn equation for $(x,v_\parallel)$. Its right-hand side is affine in $\mu$. Evaluating the fixed-moment vector field at $\mu=0,1$ gives joint $C^1$ regularity of the actual five-dimensional equation on the nonzero vacuum domain. [Augmented right-hand side](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnWindow.lean) · [Vacuum denominator identity, N-122](vacuum-local-littlejohn-births.md)
2. The local Picard–Lindelöf flow is jointly continuous in initial condition and time. At time zero it fixes the central seed. A product neighborhood of that seed and time zero lies in the open conditions that the field is regular and displacement is less than $d$. Restricting it gives one positive closed time window for all nearby births. The moment coordinate is constant, so projection gives a solution at the birth's own magnetic moment. [Local flow and uniqueness](../../PlasmaLean/Theory/Fields/LocalFlowDisplacement.lean)
3. Along the known solution the contracted velocity is locally $C^1$. Closed-interval uniqueness identifies every other partial solution with it up to that solution's endpoint. Taking the smaller of the two signed horizons supplies one time for both signs. The distance to an arbitrary axis set is 1-Lipschitz in Cartesian position, so the same $d$ bounds radial excursion. [All-partial-solution control and radial estimate](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnWindow.lean)

## Reproduction

Use the N-99 ground height-band passage with key `9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809`.

```bash
lake build PlasmaLean.Design.DommaschkCommonLittlejohnTime
.venv-ws/bin/python scripts/dommaschk_kam/verify_common_littlejohn_time.py \
  --passage /tmp/plasma-mirror-height-passage-325.json \
  --output /tmp/plasma-common-littlejohn-time325.json
```

Two independent ground builds produced content key `fc830215eaf15b2cf2c1c42ceaf4d7ffce1be9f7ceb1869fa88aae5fed04ccce` and byte-identical Lean object files with SHA-256 `9a9893df0103a4b83ca3871659586cdc04e0b8dbf0d86782b6eedddc6256d59e`. The first ground assembly took 5.746 seconds and used 7,843,012 KiB peak resident memory. Both theorem audits reported `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-125 |
| Title | A common Littlejohn time and displacement cap for both QA2R velocity signs |
| Kind | Local flow theorem and physical ground certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-114, N-117, N-122 |
| Dependency requirement | The original torus-interpolated birth reaches the transverse mirror-height band. Its two strict velocity lifts are interior trapped-reference births. The actual Littlejohn velocity is locally smooth on the nonzero vacuum domain. |
| Produces | One common positive time for two open sign populations under any positive position cap, all-partial-trajectory radial control and a conditional positive-fraction field-level band. |
| Difficulty | Joint regularity in the physical moment, uniform time across an open neighborhood and uniqueness for every competing partial trajectory. |
| Status | Verified and independently replayed ground theorem. |
| Lean evidence | `LocalFlowDisplacement.common_window`, `.agree_from_start`, `VacuumLittlejohnWindow.exists_control`, `.Control.radial`, `.guidingCentreBand`, `DommaschkCommonLittlejohnTime.UniformAt.band`, `DommaschkCommonLittlejohn325.from_birth`, `.common_positive_mass`. |
| Last updated | 25 November 2026 (28 November 2026: pointer row added below; the note is otherwise unchanged) |
| Patched by / Alternatives | [N-213](band-form-fixed-inputs.md): `BandContract` is the band form of C2 (adopted 28 November 2026); the `GuidingCentreBand` conclusion of this note has an existential horizon and is a lemma, not an instance of the clause. [N-216](wide-tube-label-campaign.md): an orbit theorem with explicit constants on a wider QA2R tube. |
