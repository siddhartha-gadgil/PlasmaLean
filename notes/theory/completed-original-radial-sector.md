# Connected first-well action levels on one actual QA2R radial sector

**The four long physical trajectories have been verified.** On one common pair of nested embedded invariant QA2R tori, there is a family of genuine signed field lines through every original interpolated birth
\[
(\phi,u)\in[-2^{-19},2^{-19}]\times[47/100,239/500].
\]
All four original radial tiles have 332 signed ODE slabs on each clock, a total of **2,656**. Each ordinary ODE holds on the closed interval \([-331/64,331/64]\). The former through-trajectory hypothesis has been discharged in Lean. [Final kernel records](../../scripts/dommaschk_kam/results/completed_radial_sector_20261125.json) · [Common-torus theorem producer](../../scripts/dommaschk_kam/verify_completed_radial_sector.py)

## First mirrors, action and radial sampling

- Throughout the height interval \([h_U-1/50000,h_U+1/30000]\), the true first mirrors on both sides enclose the **original birth**. Each mirror is transverse. The endpoints and Cartesian first-well action are jointly continuous in phase, radial label and height. Their one-way normalized flight time satisfies \(14<T<10000\), and \(dJ/dh=T\). Here \(h_U=5300546391395933/5000000000000000\). [Physical mirror and flight proofs](radial-ribbon-mirror-height-band.md) · [Derivative and continuity](height-action-rectangle.md)
- At height \(h_U\), choose any continuous phase-dependent target in \([J_*-21/10000,J_*+19/10000]\), where \(J_*=6799610938322487/5000000000000000\). One compact connected set of exact first-well births projects onto the **whole phase sector**. Its radii stay a positive distance from both radial faces. In particular a constant target \(J_*\) is realized at every phase on one such connected set. [Quantitative face bounds](radial-sector-prescribed-action-band.md) · [Connected continuation](connected-original-birth-action-level.md)
- More generally, let both \(H(\phi)\) and \(j(\phi)\) be continuous, with \(|H-h_U|\le10^{-7}\) and \(J_*-11/10000\le j\le J_*+9/10000\). A compact connected interior set of original births attains these two prescriptions across the entire sector. At any angular phase, any admissible height and target, and any tolerance \(\varepsilon>0\), a radial interval of length at least \(\ell(\varepsilon)>0\) has action within that tolerance. One length works uniformly for all three parameters. The proof gives a positive uniform sampling fraction \(\ell/(1/125)\) in the radial launch label. Its numerical value for this field remains open. [Radial measure theorem](uniform-radial-action-windows.md)

A connected level can have several radii at the same phase. The independent conclusions on exact levels and approximate radial measure apply on the same torus pair; the final declaration selects the three-parameter physical family before quantifying the prescriptions. This settles the local first-well target on the original sector. Full-period action bracketing, cross-field guiding-centre drift, and a thermal birth population with a specified confinement time remain open. The full-period birth-field result applies to the wider interval \([0.44,0.54]\). [Physical first-exit budget](physical-face-action-exit.md) · [Full-period launch chart](periodic-original-birth-strength.md)

## Verification and replay

The public manifest records the checked Lean declarations and SHA-256 hashes of the generated Lean sources and compiled modules. The 332-row physical join, fixed target, connected prescription band, height–action rectangle, sampling statement and final combined theorem were all independently audited with only `propext`, `Classical.choice` and `Quot.sound`.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_ribbon_through_chains.py \
  --packets /tmp/plasma-n169-packets.json --count 332 --output /tmp/plasma-n175-through332.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_height_action_crossings.py \
  --band /tmp/plasma-n186-height-band.json --faces /tmp/plasma-n188-faces.json \
  --through /tmp/plasma-n175-through332.json --output /tmp/plasma-n192-unconditional.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_completed_radial_sector.py \
  --through /tmp/plasma-n175-through332.json --rectangle /tmp/plasma-n192-unconditional.json \
  --faces /tmp/plasma-n188-faces.json --output /tmp/plasma-n205-joint.json
```

The physical join has key `7c006f93f184c56d80da9bc887072adf86ef57a3fb6f49b0e56dcf64dd07f974`. The joint unconditional declaration `DommaschkCertifiedRadialSector.on_nested_tori` has key `9d134c57b876eef02d439f54ee1e52faf6f7d101dcce7ef27fc32c8deec4613d`. [Prerequisite packet and sign construction](radial-sector-through-trajectory-criterion.md) · [Workstation continuation](balanced-ribbon-defect-campaign.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-205 |
| Kind | Completed physical first-well action family with connected levels and uniform radial sampling |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-169, N-175, N-181, N-183, N-184, N-186, N-188, N-192, N-197, N-201 |
| Dependency requirement | The four complete through-going ODE chains, original birth entries, signed field and derivative bounds, exact physical endpoint actions and the topological continuation theorem. |
| Produces | A connected original first-well action level across the small phase sector and a uniform radial sampling interval for each positive action tolerance on one original torus pair. |
| Status | Unconditional kernel-verified proof on the stated sector. Full-period first-well action and thermal confinement remain open. |
| Last updated | 25 November 2026 |
