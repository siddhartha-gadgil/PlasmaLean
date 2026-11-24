"""Check the quantitative inverse for the true physical action on each admitted pilot birth."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


NAME = 'DommaschkActionHeightInverse325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkActionHeightInverse
public import RowFlightBudgetCache.DommaschkRowFlightBudget325

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkActionHeightInverse325
open DommaschkSignedBirthApproach DommaschkMirrorBandPassage DommaschkFullBandFlightBounds
open DommaschkActionHeightInverse DommaschkRowFlightBudget
set_option maxRecDepth 16384

/-- The first-well action of the field line through each admitted birth has the
calibrated height inverse and the exact endpoint action-width bounds. -/
theorem from_birth : ThroughBirth (fun φ y => Passage φ y ∧ Calibration y ∧
    9046573590327 / 1250000000000000 <
      ambient y (DommaschkFirstMirrorLaunchSign.height true) -
        ambient y (DommaschkFirstMirrorLaunchSign.height false) ∧
    ambient y (DommaschkFirstMirrorLaunchSign.height true) -
      ambient y (DommaschkFirstMirrorLaunchSign.height false) <
        42648132640113 / 312500000000000) := by
  obtain ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, each⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, passage⟩ := each φ small
  have region : ∀ t ∈ Set.Icc (-b) b, DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [b, Nat.cast_ofNat, neg_div] using DommaschkSignedTraceDomain.on_path path
      (by norm_num) (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have prior := DommaschkFullBandFlightBounds.on_path path passage region
    (DommaschkMirrorHeightBand325.all_slopes path) (by
      simpa only [a, Nat.cast_ofNat, neg_div] using path.below_on (k := 316)
        (by norm_num) rfl rfl DommaschkCoreSubmirror316Of325.fwd_checked
        DommaschkCoreSubmirror316Of325.back_checked)
  have result := of_identity (DommaschkMirrorBandFlightIdentity.on_path path region passage.2.1)
    (complete prior region (DommaschkRowFlightBudget325.central path))
  exact ⟨y, start, passage, result, endpoint_width result⟩

end PlasmaLean.Design.DommaschkActionHeightInverse325
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--row-flight', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/action-height-inverse')
    args = parser.parse_args()

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    parent = json.loads(args.row_flight.read_text())
    roots = list(map(Path, parent['import_paths']))
    admitted(roots[0], 'DommaschkRowFlightBudget325', parent['key'])
    packet, version = digest(RECORD), lake('lean', '--version')
    if (parent['packet_sha256'], parent['lean_version']) != (packet, version):
        parser.error('the row budget must match the current packet and Lean version')
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    keys = [packet, version, parent['key'], digest(DESIGN/'DommaschkActionHeightInverse.trace')]
    base, result = compile_modules(args.cache/NAME, [(NAME, SOURCE, ['from_birth'])], roots, keys,
                                   env, 'ActionHeightInverseCache')
    report = {k: v for k, v in result.items() if k != 'artifacts'}
    report.update(row_flight_key=parent['key'], packet_sha256=packet, lean_version=version,
                  import_paths=[str(p) for p in [base, *roots]])
    save(args.output, report)
    print(f'{NAME}: {report["key"]}', flush=True)


if __name__ == '__main__':
    main()
