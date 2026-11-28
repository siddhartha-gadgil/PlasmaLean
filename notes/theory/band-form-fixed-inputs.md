# The band form of C2 with fixed inputs

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-213` |
| Title | The band form of C2 with fixed inputs: specification, admissibility and claim |
| Kind | patch |
| Addresses | G-10, G-8, Q-35; audit findings AW-H3, AW-M3, AW-M4 (25 November 2026); AV-M7 |
| Depends on | N-53 (`GuidingCentreBand`, `GuidingCentreBand.radial_loss_le`); `Kernel/Vacuum.fieldDiv` |
| Dependency requirement | The compiled single-species Littlejohn predicate `GuidingCentreBand` and its loss bound, unchanged. |
| Produces | `BandSpec`, `BandSpec.Admissible`, `MeetsBand`, `BandContract` and their consequences; regressions for the audit findings |
| Difficulty | routine (the definitions and regressions); research (any positive instance) |
| Status | verified (definitions, consequences and regressions). Adopted as the band form of C2 (user decision, 28 November 2026). One formal instance exists (N-216) and does not meet the acceptance rule; an accepted instance is open. |
| Lean evidence | default build: `Theory/Contract/BandSpec` (`BandSpec`, `BandSpec.Admissible`, `Admissible.axis_compact`, `MeetsBand`, `BandContract`, `MeetsBand.radial_loss_le`, `MeetsBand.exists_birth`, `MeetsBand.mono_horizon`, `MeetsBand.mono_tolerance`, `not_meetsBand_const`); `Sanity/BandSpec` (`dirac_not_admissible`, `quadratic_fixture_not_admissible`, `mirror_not_meetsBand`) |
| Audit evidence | addresses the refresh audit of 25 November 2026 (`0bec221`), AW-H3, AW-M3, AW-M4; not itself audited |
| Last updated | 28 November 2026: adoption and acceptance rule |
| Patches | N-53 (the band-form acceptance predicate) and the C2 band-form clause of `notes/formalization/00-model-contracts.md` |

## Purpose and scope

The approved band form of clause C2 (user decision, 23 November 2026) asks for a certified bound
that keeps a stated trapped population within a stated radial range through a stated time.
N-53 implemented it as `GuidingCentreBand B m q axis ν support covered energy pitch fraction
excursion horizon`. Every one of these arguments is chosen by whoever proves the statement. The
refresh audit of 25 November 2026 found that this admits instances without confinement content:

- a point-mass birth law with fraction one (`quadratic_guidingCentreBand` proves this instance);
- an existential horizon: for each excursion cap some `T > 0` works by local ODE existence
  (`DommaschkCommonLittlejohnTime.BandAt`, `VacuumLittlejohnCompact.compact_guidingCentreBand`),
  at every regular vacuum mirror birth;
- any field, including one that violates Gauss's law, with drift terms silently zero where the
  field is not differentiable (Lean's `fderiv` is 0 there);
- any nonempty compact "axis", for example a large ball.

This patch keeps every number symbolic. It does not choose physical scales, populations or
times; it only stops the prover from choosing them. The status of C2 is unchanged: open.

## The patch

Split the clause into a specification fixed before any proof and a claim about the field
(`Theory/Contract/BandSpec`):

- **`BandSpec`**: species `m`, `q`; birth law `ν`; birth support; energy and pitch windows; a
  reference axis `ℝ → Space`; the required horizon; the allowed excursion; the required fraction
  `minFraction`.
- **`BandSpec.Admissible`** (a property of the specification alone): `0 < m`, `q ≠ 0`,
  `0 < horizon`, `0 ≤ excursion`, `0 < minFraction ≤ 1`, `ν ≪ volume` on position × parallel
  velocity × magnetic moment, the support has nonempty interior, the axis is `C¹` and periodic
  with period one (so its range is a compact closed curve).
- **`MeetsBand s B`** (the claim): there are an open region `Ω`, covered births and an attained
  fraction such that `B` is `C²` on `Ω` with `fieldDiv B = 0` there, the attained fraction is at
  least `s.minFraction`, `GuidingCentreBand` holds with the axis, horizon, excursion and birth data
  of `s`, and every partial orbit from a covered birth up to the horizon stays in `Ω`.
- **`BandContract s B := s.Admissible ∧ MeetsBand s B`** is the band form of C2.

The prover chooses only `Ω`, the covered births and the attained fraction. A family of the form
"for each excursion there is some horizon" gives `MeetsBand` only for specifications whose horizon
is at most the horizon produced, so it cannot meet a specification fixed in advance unless it
supplies a lower bound for that horizon.

The axis requirement is weaker than "the magnetic axis": any closed `C¹` curve is allowed. Tying
it to the C1 reference curve, or measuring excursion by a flux label, is left to the composition
of clauses (G-8). `MeetsBand` asks for Gauss's law only, so it allows plasma currents; a vacuum
application adds `curl B = 0` through the field's own contract.

## Consequences (compiled)

- `MeetsBand.radial_loss_le`: births whose excursion exceeds the specified tolerance before the
  specified horizon have measure at most `(1 − minFraction)` times the trapped reference mass.
  With fixed inputs this is a statement about the specification, not about a chosen fraction.
- `MeetsBand.exists_birth`: there is a covered trapped birth with an open neighbourhood on which
  `fieldDiv B = 0`.
- `MeetsBand.mono_horizon`, `MeetsBand.mono_tolerance`: a shorter horizon, a larger excursion or
  a smaller required fraction is easier (the specification order is the expected one).
- `not_meetsBand_const`: a uniform field has no trapped births and meets no specification.

## Regressions (compiled, `Sanity/BandSpec`)

- `dirac_not_admissible`: a point-mass birth law is never admissible (volume has no atoms on
  position × parallel velocity × moment).
- `quadratic_fixture_not_admissible`: the data of the N-53 fixture `quadratic_guidingCentreBand`
  is not an admissible specification, for any axis, horizon, excursion and fraction.
- `mirror_not_meetsBand`: the quadratic-mirror field of that fixture, with divergence `2x₀`,
  meets no specification, although it satisfies the unrestricted `GuidingCentreBand`.

## Adoption and acceptance rule (user decision, 28 November 2026)

`BandContract` is the band form of clause C2. `GuidingCentreBand` on its own, and results with an existential horizon, are lemmas and not instances of the clause.

The Lean definition is not strengthened for now. It leaves three things to the specification: how the support is described, the length of the horizon and the size of the excursion. A `BandContract` instance counts as progress on C2 only when all of the following hold; this is checked at review, not in Lean.

1. **Horizon against a physical scale.** The specification or its note states the horizon in units of the bounce time of the population (and, where a device scale is fixed, in seconds). A horizon below one bounce is recorded as such and is not confinement of trapped particles.
2. **Excursion against a physical scale.** The excursion is compared with the orbit (banana) width and the minor radius. An excursion of the size of the region in which the orbits are known to exist carries no information.
3. **Support fixed independently.** The support is given in elementary terms (coordinates and inequalities), not through the trapped reference population itself, so that the fraction is a result and not a construction.
4. **Inputs before proof.** Species, energy and pitch windows, birth law and device scale are stated before the proof, as N-213 already requires.

The definition will be revisited (for example a horizon floor tied to the bounce time, or an elementary-support condition) once the horizon work of N-216 shows what a realistic instance looks like.

**Current instance.** `DommaschkWideTubeRows000Band.band_contract` (N-216, stage 5) is a `BandContract` for the QA2R field. It fails items 1 to 3: the horizon is about a tenth of a half bounce, the excursion 1/8 is the envelope size, and the support is the interior of the reference population of good births. It is a formal instance and a regression target, not C2 progress in the sense above.

## What is not done

- **No accepted instance.** One formal instance exists (above). No admissible specification meeting the acceptance rule is shown to be met by any field. This is the open content of C2 in band form (it sharpens AV-M7). For the Dommaschk QA2R field it needs a horizon of at least a bounce, which the direct drift bound of N-216 cannot give; beyond one bounce it needs the averaged estimate of N-210.
- `GuidingCentreBand` and the theorems that produce it are unchanged and remain true. Results
  that conclude `GuidingCentreBand` with an existential horizon (N-125 and its uses) are lemmas,
  not band-form instances.
- The numbers (horizon, excursion, fraction, population) stay symbolic by user decision.

## Barriers

- An admissible birth law needs a guiding-centre reduction with errors controlled on a
  positive-volume set of births, not along one orbit.
- A horizon fixed in advance needs global (in time) control of the Littlejohn flow on the covered
  set: existence through the horizon and a drift bound, both uniform over the covered births.
