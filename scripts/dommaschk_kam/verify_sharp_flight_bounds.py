"""Attach the full-envelope toroidal field and flight bounds to the N-99 through-birth theorem."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


NAME = 'DommaschkSharpFlightBounds325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkSharpFlightBounds
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

@[expose] public section
namespace PlasmaLean.Design.DommaschkSharpFlightBounds325
open DommaschkSignedBirthApproach DommaschkMirrorBandPassage DommaschkSharpFlightBounds
set_option maxRecDepth 16384

/-- For each admitted Q-16 birth angle the same true first wells satisfy the improved
lower time bound over the closed band and the improved upper bound over its upper half. -/
theorem from_birth : ThroughBirth (fun φ y => Passage φ y ∧ SharpTime φ y) := by
  obtain ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, each⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, passage⟩ := each φ small
  refine ⟨y, start, passage, of_passage passage ?_⟩
  simpa only [Nat.cast_ofNat, neg_div] using DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl

end PlasmaLean.Design.DommaschkSharpFlightBounds325
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--passage', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/sharp-flight-bounds')
    args = parser.parse_args()
    parent = json.loads(args.passage.read_text())
    roots = [Path(p) for p in parent['import_paths']]
    admitted(roots[0], 'DommaschkRegularMirrorHeightBand325', parent['key'])

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    packet, version = digest(RECORD), lake('lean', '--version')
    if (packet, version) != (parent['packet_sha256'], parent['lean_version']):
        parser.error('passage receipt does not match the current physical packet and Lean version')
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    keys = [version, packet, parent['key'], digest(DESIGN / 'DommaschkSharpFlightBounds.trace')]
    root, proof = compile_modules(args.cache / NAME, [(NAME, SOURCE, ['from_birth'])], roots,
                                  keys, env, 'SharpFlightBoundsCache')
    result = {k: v for k, v in proof.items() if k != 'artifacts'}
    result.update(passage_key=parent['key'], packet_sha256=packet, lean_version=version,
                  import_paths=[str(p) for p in [root, *roots]])
    save(args.output, result)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
