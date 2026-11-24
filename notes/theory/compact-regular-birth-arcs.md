# An open Cartesian tube of regular births about a complete central field-line arc

On the actual QA2R pilot at radial label 0.470, the compact set consisting of the entire Cartesian arc \(|t|\le316/64\) and the entire closed archive height band lies inside the interior of the regular mirror-birth set. More strongly, a closed neighborhood of some **single positive radius** around that compact set still lies in the interior. The neighborhood uses the product metric on Cartesian position and height. The radius may depend on the physical field line. [Ground proof](../../scripts/dommaschk_kam/verify_regular_birth_arcs.py) · [Pilot trajectory and first mirrors](dommaschk-native-first-well-action-enclosure.md)

For each admitted birth angle \(|\phi|\le2^{-19}\), the chosen pilot still passes through the original interpolated birth at that angle on the same two embedded tori. Every position on the arc, including the endpoints, has both signs of accessible parallel velocity. For each positive mass and energy, and each allowed height, the lifted births lie inside the five-dimensional trapped reference whenever the specified support, energy and pitch cuts contain them in their interiors. For nonzero charge and a positive displacement cap, both signs have open neighborhoods and a common positive local guiding-centre time. The time and the neighborhoods can depend on the chosen position and physical parameters. For a measurable finite reference, an open-positive law and a nonempty compact axis, the covered set has positive reference fraction. [Local orbit theorem](../../PlasmaLean/Design/DommaschkCommonLittlejohnTime.lean)

## Mathematical statement

Let \(f(t)\) denote the field strength on one signed field line. Suppose each outward clock has a transverse first-contact branch in \((a,b)\) at every height \(h\) in a closed interval \([L,U]\). Assume the outward derivative at the root exceeds \(k/(2h)>0\), the profile is below \(h\) before the first root and above \(h\) afterwards through \(b\). Then every \(c\in[-a,a]\) is a strict sublevel point with a transverse bracket \([-b,c,b]\). At any level contact to its left the signed derivative is negative, and to its right it is positive. This statement uses only the profile on a real interval. [Two-sided branch theorem](../../PlasmaLean/Theory/Kinetic/MirrorBranchBracket.lean)

In the regular Cartesian region of QA2R, the signed field-line ODE gives a smooth angular velocity aligned positively with the nonzero field. The magnetic mirror predicate uses arclength. Local flow persistence converts the transverse bracket into an open position-height neighborhood for the arclength problem. The map \(t\mapsto x(t)\) is continuous on the closed central arc, so \(K=x([-a,a])\times[L,U]\) is compact. Since \(K\) lies in an open set of regular births, its closed metric thickening by some \(\delta>0\) stays in that set. No injectivity or chosen tubular coordinates are necessary. [Physical birth, compactness and the signed approach](../../PlasmaLean/Design/DommaschkPhaseZeroRegularBirth.lean)

## Second-radius application

For \(u=239/500\), the corresponding central arc is \(|t|\le317/64\). Lean has checked that this entire conclusion follows from its signed physical passage beyond \(327/64\) and its regular spatial enclosures. It uses the 327 actual branch rows on the same path as the original interpolated birth, on both clocks, and requires no quadrature input. On the common calibrated family used below the second trajectory has reached 192 slabs in each direction. The second-radius compact-tube statement still awaits its through-mirror continuation. The pilot theorem already has that continuation. [Secondary physical branch](secondary-first-mirror-height-band.md) · [Second-path attachment](../../scripts/dommaschk_kam/templates/secondary_regular_birth.lean.tpl)

The pilot theorem is `DommaschkRegularBirthArcs391_192_48_5_48_8_5_5.pilot`, key `01beaeb882865dda4a68b774808970dfdf44160ae51fee471d2475c28f968dec`. The secondary implication `DommaschkQ0R478RegularBirths.from_passage` has key `439bb8c98a8824927ec3d6de41b4c07cd323d0126cc89c29766c80474bc74ffd`. Both use only propext, Classical.choice and Quot.sound. Physical time in seconds and a selected thermal population fraction remain open.

~~~bash
lake build PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
.venv-ws/bin/python scripts/dommaschk_kam/verify_regular_birth_arcs.py \
  --well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --calibrated /tmp/plasma-calibrated-at-192.json \
  --output /tmp/plasma-regular-birth-arcs.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-147 |
| Kind | Two-sided first-contact theorem, geometric stability of the regular-birth set and physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-117, N-122, N-125, N-127, N-130, N-138 |
| Dependency requirement | Signed physical path on an interval strictly larger than the bracket, positive magnetic angular velocity and two outward transverse branches |
| Produces | Open position-height tubes along a compact arc, strict accessibility, both signs of lifted trapped births and local orbit control |
| Status | Actual complete pilot arc and conditional second arc kernel-verified |
| Lean evidence | `MirrorHeightBand.Branch.bracket`, `DommaschkPhaseZeroRegularBirth.population`, `.tube_of_centers`, `.at_original_birth`, `DommaschkCommonLittlejohnTime.uniform_of_lifted` |
| Last updated | 25 November 2026 |
