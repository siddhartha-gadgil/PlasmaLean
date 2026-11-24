"""Check the first-well action/flight identity for every height and birth angle of the pilot."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


NAME = 'DommaschkMirrorActionFlight325'
PASSAGE = 'DommaschkRegularMirrorHeightBand325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkMirrorBandFlightIdentity
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

/-! # Height derivative and exact increments on the original signed first-well trajectory -/
@[expose] public section
namespace PlasmaLean.Design.DommaschkMirrorActionFlight325
open DommaschkSignedBirthApproach DommaschkMirrorBandPassage DommaschkMirrorBandFlightIdentity
set_option maxRecDepth 16384

/-- The same field line through each actual interpolated Q-16 birth supports the regular
first wells and the action/flight identity throughout the closed height band. -/
theorem from_birth : ThroughBirth (fun φ y => Passage φ y ∧ Identity y) := by
  obtain ⟨uC, zC, uA, zA, rr, zz, tc, ta, ic, ia, nested, each⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, rr, zz, tc, ta, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, birth, x, path, passage⟩ := each φ small
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have reg : ∀ t ∈ Set.Icc (-bound) bound, DommaschkSignedTraceDomain.Region (y t) := by
    norm_num [bound] at region ⊢
    exact region
  exact ⟨y, birth, passage, DommaschkMirrorBandFlightIdentity.on_path path reg passage.2.1⟩

end PlasmaLean.Design.DommaschkMirrorActionFlight325
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--passage', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/mirror-action-flight')
    args = parser.parse_args()

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    parent = json.loads(args.passage.read_text())
    roots = [Path(path) for path in parent['import_paths']]
    version, packet = lake('lean', '--version'), digest(RECORD)
    if parent['packet_sha256'] != packet or parent['lean_version'] != version:
        parser.error('passage receipt must match the current archive and Lean version')
    admitted(roots[0], PASSAGE, parent['key'])
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    keys = [version, packet, parent['key'], digest(DESIGN / 'DommaschkMirrorBandFlightIdentity.trace')]
    root, result = compile_modules(args.cache / NAME, [(NAME, SOURCE, ['from_birth'])],
                                   roots, keys, env, 'MirrorActionFlightCache')
    report = {key: value for key, value in result.items() if key != 'artifacts'}
    report.update(passage_key=parent['key'], packet_sha256=packet,
                  import_paths=[str(path) for path in [root, *roots]], lean_version=version)
    save(args.output, report)
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
