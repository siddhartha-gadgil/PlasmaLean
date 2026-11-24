"""Check finite positive one-way flight time for both first wells of every admitted Q0R470 birth."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def source(n):
    name = f'DommaschkFirstBounceTimes{n:03}'
    contacts = f'DommaschkTransverseMirrorBirth{n:03}'
    fwd, back = f'DommaschkPhysicalPrefix{n:03}', f'DommaschkBackwardPrefix{n:03}'
    src = f'''module
public import PlasmaLean.Design.DommaschkFirstMirrorBounceTime
public import SignedMirrorBirthCache.{contacts}

/-! # Both first mirror-to-mirror flight times are finite and positive at the actual birth. -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkFirstMirrorBounceTime DommaschkSignedBirthApproach DommaschkSignedObservable
open DommaschkFirstMirrorLaunchSign
set_option linter.style.longLine false
set_option maxRecDepth 8192

theorem from_birth : ThroughBirth (fun φ y =>
    ∃ x, Path {n} {fwd}.exitState {back}.exitState {fwd}.rows {back}.rows x y ∧
    Flight (316 / 64) (317 / 64) (height false) φ y ∧
    Flight (324 / 64) (325 / 64) (height true) φ y) := by
  apply from_birthWith {contacts}.contacts_from_birth (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
  rintro φ small x y path ⟨low,high⟩
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
  refine ⟨x,path,?_,?_⟩
  · exact of_contacts path (small.trans (by norm_num)) (by norm_num) (by norm_num [height])
      (by norm_num) region low
  · exact of_contacts path (small.trans (by norm_num)) (by norm_num) (by norm_num [height])
      (by norm_num) region high

end PlasmaLean.Design.{name}
'''
    return name, src


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--paired', required=True, type=Path)
    p.add_argument('--contacts', required=True, type=Path)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/physical-bounce-times')
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    pair, contacts = [json.loads(path.read_text()) for path in (args.paired, args.contacts)]
    n = pair['slabs_per_direction']
    packet = digest(RECORD)
    if not 325 <= n <= 391 or pair['packet_sha256'] != packet or contacts['packet_sha256'] != packet:
        p.error('expected the original Q0R470 archive and a trace reaching both mirror heights')
    bases = []
    for report, name in ((pair, f'DommaschkPairedPrefix{n:03}'),
                         (contacts, f'DommaschkTransverseMirrorBirth{n:03}')):
        if report['module'] != name:
            p.error(f'expected {name}')
        paths = list(map(Path, report['import_paths']))
        admitted(paths[0], name, report['key'])
        bases.extend(paths)
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    args.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    keys = [lake('lean', '--version'), packet, digest(DESIGN/'DommaschkFirstMirrorBounceTime.trace'),
            pair['key'], contacts['key']]
    overlay = merge_import_roots(args.cache, bases, keys)
    name, body = source(n)
    out, result = compile_modules(args.cache/name, [(name, body, ['from_birth'])],
                                  [overlay], keys, args, 'FirstBounceTimeCache')
    save(args.output, {**{k:v for k,v in result.items() if k != 'artifacts'},
                       'signed_archive': packet, 'paired_key': pair['key'], 'contacts_key': contacts['key'],
                       'import_paths': [str(out), str(overlay)]})
    print(name, result['key'], flush=True)


if __name__ == '__main__':
    main()
