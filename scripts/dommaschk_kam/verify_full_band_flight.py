"""Attach the verified 316-row core clearance to the actual regular mirror birth family."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


NAME = 'DommaschkFullBandFlight325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkFullBandFlightBounds
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325
public import SubmirrorPrefixCache.DommaschkCoreSubmirror316Of325

@[expose] public section
namespace PlasmaLean.Design.DommaschkFullBandFlight325
open DommaschkSignedBirthApproach DommaschkMirrorBandPassage DommaschkFullBandFlightBounds
set_option maxRecDepth 16384

/-- The actual one-way time, on the actual common path, has a numerical interval at each height. -/
theorem from_birth : ThroughBirth (fun φ y => Passage φ y ∧ BoundedFlight φ y) := by
  obtain ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, each⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, passage⟩ := each φ small
  refine ⟨y, start, passage, on_path path passage ?_ (DommaschkMirrorHeightBand325.all_slopes path) ?_⟩
  · simpa only [b, Nat.cast_ofNat, neg_div] using DommaschkSignedTraceDomain.on_path path (by norm_num)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  · simpa only [a, Nat.cast_ofNat, neg_div] using path.below_on (k := 316) (by norm_num) rfl rfl
      DommaschkCoreSubmirror316Of325.fwd_checked DommaschkCoreSubmirror316Of325.back_checked

end PlasmaLean.Design.DommaschkFullBandFlight325
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--passage', type=Path, required=True)
    parser.add_argument('--core', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/full-band-flight')
    args = parser.parse_args()

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    packet, version = digest(RECORD), lake('lean', '--version')
    keys = [version, packet, digest(DESIGN / 'DommaschkFullBandFlightBounds.trace')]
    roots = []
    parents = {}
    for label, file, name in [('passage', args.passage, 'DommaschkRegularMirrorHeightBand325'),
                              ('core', args.core, 'DommaschkCoreSubmirror316Of325')]:
        report = json.loads(file.read_text())
        if report['packet_sha256'] != packet or report['module'] != name:
            parser.error(f'wrong signed trajectory or proof for {label}')
        if label == 'core' and (report['slabs'] != 316 or not report.get('core_height')):
            parser.error('the core receipt must cover all 316 slabs at the clearance height')
        if label == 'passage' and report['lean_version'] != version:
            parser.error('the passage receipt must use the current Lean version')
        paths = list(map(Path, report['import_paths']))
        admitted(paths[0], name, report['key'])
        keys.append(report['key'])
        parents[label + '_key'] = report['key']
        roots.extend(paths)
    overlay = merge_import_roots(args.cache, roots, keys)
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    root, proof = compile_modules(args.cache / NAME, [(NAME, SOURCE, ['from_birth'])],
                                  [overlay], keys, env, 'FullBandFlightCache')
    result = {k: v for k, v in proof.items() if k != 'artifacts'}
    result.update(parents, packet_sha256=packet, lean_version=version,
                  import_paths=[str(root), str(overlay)])
    save(args.output, result)
    print(NAME, result['key'], flush=True)


if __name__ == '__main__':
    main()
