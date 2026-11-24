# Sixteen-panel physical action bounds at the second phase-zero launch

For the QA2R field at $u=478/1000$, Lean checks the lower action columns on both sides of the actual transferred birth. One set of sixteen directed enclosures applies to both signed trajectories. It gives 96 chronological storage cells on $[-1/64,1/64]$. The physical proof uses the upper mirror height $h_U=5300546391395933/5000000000000000$. [Shared-model verifier](../../scripts/dommaschk_kam/verify_coarse_secondary_lower.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-148 |
| Title | Sixteen-panel physical action bounds at the second phase-zero launch |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-120, N-134, N-138, N-139, N-140 |
| Dependency requirement | The signed position tubes for this endpoint, their checked phase-zero reflection, the physical density and clipped-speed identities, and its directed 16-panel packet. |
| Produces | A signed birth with the 16-panel physical action cover, and a sound way to reuse any previously checked finer lower block. |
| Difficulty | Each negative-time digit must be paired with the correct positive-time digit, and every enclosure must apply on its full three-cell interval. |
| Status | Both launch blocks, the native transfer at row 1, the two signed outermost interior blocks (row 324), and the conditional first-well action theorem passed the Lean kernel. The full physical interior cover is in progress. |
| Lean evidence | `DommaschkCoarseBirthQ0R478N16Of005.from_nested_tori`, `MirrorActionQuadrature.cells_of_lowerColumnsLE`, `DommaschkCoarseSecondaryCore325.floor_on_enclosing_interval`, and `DommaschkQ0R478CoarseLowerFirstWell.from_passage`. |
| Audit evidence | The physical theorems use `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Why the two clocks can share a proof

For each outward row the model uses the larger of the two archived physical radii. Its separate forward and backward theorems supply the actual five quantities on the two true position tubes. Reflection at the zero section transports the signed negative-clock field into the same enclosure. Exact integer comparison of both expanded words checks all three digits after reversing the chronological indices. Across the complete arithmetic packet this comparison matches all 327 pairs. Each coarse digit also occurs in three successive expanded cells. [Local physical model](../../scripts/dommaschk_kam/verify_paired_action_profiles.py) · [Reversal and copy checks](../../scripts/dommaschk_kam/verify_coarse_secondary_lower.py)

For row zero the direct interval and rounding proofs took 16.1 seconds. The applications to the two individual signed clocks took 3.8 seconds each. On the same row the earlier 48-panel arithmetic took 39.5 seconds, with 4.4 seconds for its combined physical application. These times exclude the shared magnetic field model. The birth receipt is `9dc21327246f682824582d9550c0c114a51a22f6c64bc99eb2792e3d71cd689c`. It includes the physical ODE on $[-5/64,5/64]$ and the two central coarse blocks on that same trajectory.

An existing fine lower bound can also supply the coarse block. For each chronological cell Lean checks two natural-number inequalities between the stored density and squared-speed digits. Dividing by the positive column scales and applying transitivity gives both physical lower bounds on the identical time interval. The block certificate separately validates its rounded speed. On row 1 this transfer took 4.0 and 4.2 seconds for the two signs. [Transfer theorem](../../PlasmaLean/Certificates/WeakenLowerActionCells.lean) · [Concrete transfer checker](../../scripts/dommaschk_kam/verify_coarse_lower_transfer.py)

## Interior needed for the action target

The dimensionless target is $J_*=6799610938322487/5000000000000000$. The 16-panel archive first crosses it at 325 outward rows on each side. The mass on the central 650 chronological slabs is $765697177987387/562949953421312$, exceeding $J_*$ by about $0.00022923136$. Removing the outer pair gives $382763957575491/281474976710656$, below $J_*$ by about $0.00007143983$. Thus the fully coarse route uses three more pairs than the original 48-panel route. The N-138 timing result places both first upper-height mirrors strictly beyond $325/64$ on their respective outward clocks.

Lean checked the 325-pair mass implication with receipt `5d686c0b3c04daa988819abaada48ef7b210a52552d8ffa1d5f16903f2e313f8`. The first-well theorem, receipt `00fdeaa1c0b24d09220bff33b032701656ff80c8862491b9635f75dd7e00f172`, takes a sufficiently long signed passage and physical coverage of those 650 blocks. On that trajectory it places the two first mirrors in the open brackets, identifies physical arclength density and bounds the action between the mirrors below by the certified mass. The direct checks on the outermost required pair use both actual signed row-324 tubes. Their receipt keys start with `a58817c1579c` and `e120d4df79f9`. [Interior mass theorem](../../scripts/dommaschk_kam/verify_coarse_secondary_core.py) · [First-well implication](../../scripts/dommaschk_kam/verify_coarse_secondary_well.py)

## Reproduction

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
lake build PlasmaLean.Certificates.WeakenLowerActionCells
PACKET=/tmp/plasma-n139-packets/q0r478.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_secondary_lower.py \
  --packet "$PACKET" --rows 0 --output /tmp/plasma-n148-q0r478-cells.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_action_birth.py \
  --packet "$PACKET" --cells /tmp/plasma-n148-q0r478-cells.json \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/005.json \
  --output /tmp/plasma-n148-q0r478-birth.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_lower_transfer.py \
  --packet "$PACKET" --rows 1 --output /tmp/plasma-n148-transfer001.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_secondary_core.py \
  --packet "$PACKET" --output /tmp/plasma-n148-inner325.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_secondary_well.py \
  --core /tmp/plasma-n148-inner325.json --band /tmp/plasma-q0r478-all-height-branches.json \
  --output /tmp/plasma-n148-well325.json
.venv-ws/bin/python scripts/dommaschk_kam/run_coarse_secondary_campaign.py \
  --packet "$PACKET" --output /tmp/plasma-n148-coarse-interior.json
```

The campaign works from outward index 324 inward on a single worker. Where a native signed row has already been checked, it transfers its two lower digit bounds. Otherwise it constructs the shared 16-panel enclosure and applies it separately to the two real clocks. The native 48-panel producer can keep working independently. [Campaign driver](../../scripts/dommaschk_kam/run_coarse_secondary_campaign.py)
