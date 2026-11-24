"""Identify the accessible components and regular arclength births on a signed Q16 trajectory."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def declaration(n):
    name = f'DommaschkFirstWells{n:03}'
    contacts = f'DommaschkTransverseMirrorBirth{n:03}'
    fw, bw = f'DommaschkPhysicalPrefix{n:03}', f'DommaschkBackwardPrefix{n:03}'
    brackets = [316] + ([324] if n >= 325 else [])
    props = [f'Identified ({i}/64) ({i + 1}/64) (DommaschkFirstMirrorLaunchSign.height '
             f'{"true" if i == 324 else "false"}) y' for i in brackets]
    regular = [f'Contract.RegularMirrorBirth (DommaschkQA2R.field DommaschkQA2R.candidate) '
               f'(point y φ) (DommaschkFirstMirrorLaunchSign.height {"true" if i == 324 else "false"})'
               for i in brackets]
    near = '(small.trans (by norm_num))'
    result = (f'⟨x, path, wells, wells.at_launch {near}⟩' if len(props) == 1 else
              f'⟨x, path, wells, wells.1.at_launch {near}, wells.2.at_launch {near}⟩')
    proof = []
    if len(props) == 2:
        proof += ['  obtain ⟨first, second⟩ := hits', '  constructor']
    for i, hit in zip(brackets, ['hits'] if len(props) == 1 else ['first', 'second'], strict=True):
        prefix = '  ' if len(props) == 1 else '  · '
        proof.append(prefix + 'exact identify path (by norm_num) (by norm_num) '
                     '(by norm_num [DommaschkFirstMirrorLaunchSign.height]) '
                     f'(by norm_num) region {hit}')
    src = f'''module
public import PlasmaLean.Design.DommaschkFirstMirrorWell
public import PlasmaLean.Design.DommaschkSignedBirthApproach
public import SignedMirrorBirthCache.{contacts}

/-! # Physical first wells and regular arclength births on both sides of the section -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkFirstMirrorWell DommaschkSignedObservable
set_option maxRecDepth 8192

theorem from_birth : BirthWith (fun x => ∃ y, Path {n} {fw}.exitState {bw}.exitState
    {fw}.rows {bw}.rows x y ∧ {' ∧ '.join(props)}) := by
  apply map_birth {contacts}.contacts_from_birth
  rintro x ⟨y, path, hits⟩
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
  refine ⟨y, path, ?_⟩
{chr(10).join(proof)}

/-- At the original interpolated birth, both the physical point and the chosen
field line are shared by all the certified mirror heights. -/
theorem regular_births : DommaschkSignedBirthApproach.ThroughBirth (fun φ y =>
    ∃ x, Path {n} {fw}.exitState {bw}.exitState {fw}.rows {bw}.rows x y ∧
    ({' ∧ '.join(props)}) ∧ {' ∧ '.join(regular)}) := by
  apply DommaschkSignedBirthApproach.from_birthWith from_birth (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
  intro φ small x y path wells
  exact {result}

end PlasmaLean.Design.{name}
'''
    return name, src


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--paired', type=Path, required=True)
    p.add_argument('--contacts', type=Path, required=True)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/first-physical-wells')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    pair, contacts = (json.loads(path.read_text()) for path in (args.paired, args.contacts))
    n = pair['slabs_per_direction']
    packet = digest(RECORD)
    if not 317 <= n <= 391 or pair['packet_sha256'] != packet or contacts['packet_sha256'] != packet:
        p.error('expected a pilot trajectory reaching the lower mirror and contacts in the same archive')
    roots = []
    for expected, report in [(f'DommaschkPairedPrefix{n:03}', pair),
                             (f'DommaschkTransverseMirrorBirth{n:03}', contacts)]:
        if report['module'] != expected:
            p.error(f'expected the authenticated {expected} certificate')
        paths = list(map(Path, report['import_paths']))
        admitted(paths[0], expected, report['key'])
        roots.extend(paths)
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    args.lean = str(Path(lake('lean', '--print-prefix')) / 'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    keys = [lake('lean', '--version'), packet, digest(DESIGN/'DommaschkFirstMirrorWell.trace'),
            digest(DESIGN/'DommaschkSignedBirthApproach.trace'),
            pair['key'], contacts['key']]
    overlay = merge_import_roots(args.cache, roots, keys)
    name, source = declaration(n)
    root, receipt = compile_modules(args.cache/name, [(name, source, ['from_birth', 'regular_births'])],
                                    [overlay], keys, args, 'FirstWellCache')
    result = {k:v for k,v in receipt.items() if k != 'artifacts'}
    result.update(packet_sha256=packet, paired_key=pair['key'], contacts_key=contacts['key'],
                  import_paths=list(map(str, [root, overlay])))
    save(args.output, result)
    print(name, result['key'], flush=True)


if __name__ == '__main__':
    main()
