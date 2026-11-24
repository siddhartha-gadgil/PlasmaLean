"""Attach the launch action blocks and, if reached, the first chronological cell
to the very same physical birth trajectory as an authenticated signed prefix."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, HERE, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def load_parent(report, expected, packet_hash):
    if report['module'] != expected or report['packet_sha256'] != packet_hash:
        raise ValueError(f'expected the physical {expected} certificate for this archive')
    dirs = list(map(Path, report['import_paths']))
    admitted(dirs[0], expected, report['key'])
    return dirs


def application(n, history=None):
    base = 'DommaschkSignedActionPrefix' if history is None else 'DommaschkSignedAction' + history['tag']
    name = f'{base}{n:03}'
    forward = f'DommaschkPhysicalPrefix{n:03}'
    back = f'DommaschkBackwardPrefix{n:03}'
    pair = f'DommaschkPairedPrefix{n:03}'
    cap = ' ∧ EarliestOn y' if n >= 325 else ''
    proof = ['  constructor'] if cap else []
    indent = '  · ' if cap else '  '
    length = f'(by change 0 < {n}; norm_num)'
    proof += [indent+f'apply launch path (by norm_num) {length} {length}',
              ('    ' if cap else '  ')+'all_goals with_unfolding_all rfl']
    if cap:
        proof += [f'  · apply earliest path (by norm_num) (by change 324 < {n}; norm_num)',
                  '    with_unfolding_all rfl']
    extra_import = history['import_line'] if history else ''
    prior = history['property'] + ' ∧ ' if history else ''
    if history and history['tag'] == 'Below':
        k = history['k']
        intro = f'''  apply birth_with {pair}.exists_nested_paired
  intro x y path
  constructor
  · have lower := path.below_on (k := {k}) (by norm_num) rfl rfl
        {history['module']}.fwd_checked {history['module']}.back_checked
    have higher : (DommaschkFirstMirrorLaunchSign.height false : ℝ) <
        DommaschkFirstMirrorLaunchSign.height true := by norm_num [DommaschkFirstMirrorLaunchSign.height]
    exact fun t ht => ⟨lower t ht, (lower t ht).trans higher⟩'''
        proof = ['  ·', *['  ' + step for step in proof]]
    elif history:
        intro = f"  apply keep {history['module']}.contacts_from_birth\n  intro x y path"
    else:
        intro = f'  apply birth_with {pair}.exists_nested_paired\n  intro x y path'
    src = f'''module
public import SignedActionBridgeCache.DommaschkSignedActionBounds
public import PairedPrefixCache.{pair}
{extra_import}

/-! # Original action cells realized on a physical signed prefix of {n} slabs each way -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkSignedActionBounds
set_option maxRecDepth 8192

theorem from_birth :
    BirthWith (fun x => ∃ y, Path {n} {forward}.exitState {back}.exitState
      {forward}.rows {back}.rows x y ∧ {prior}(BirthBlocksOn y{cap})) := by
{intro}
{chr(10).join(proof)}

end PlasmaLean.Design.{name}
'''
    return name, src


def observable(file, n, pair, checksum, below):
    report = json.loads(file.read_text())
    if below:
        k = report['slabs']
        if report['paired_key'] != pair['key'] or report['upper'] or not 0 < k <= min(n, 316):
            raise ValueError('the lower height history must belong to this exact signed trajectory')
        module = f'DommaschkSubmirror{k:03}Of{n:03}'
        package, tag = 'SubmirrorPrefixCache', 'Below'
        prop = (f'(∀ t ∈ Set.Icc (-({k} : ℝ)/64) ({k}/64), '
                'DommaschkMirrorTubeCrossing.strength t (y t) < DommaschkFirstMirrorLaunchSign.height false ∧ '
                'DommaschkMirrorTubeCrossing.strength t (y t) < DommaschkFirstMirrorLaunchSign.height true)')
    else:
        if n <= 316:
            raise ValueError('the signed trajectory must reach the first mirror bracket')
        k = None
        module = f'DommaschkTransverseMirrorBirth{n:03}'
        package, tag = 'SignedMirrorBirthCache', 'Contacts'
        clauses = [f'DommaschkSignedMirrorSlope.FirstTransverseBoth ({i}/64) ({i+1}/64) '
                   f'(DommaschkFirstMirrorLaunchSign.height {height}) (1/{rate}) y'
                   for i, height, rate in [(316, 'false', 128), (324, 'true', 400)] if i < n]
        prop = '(' + ' ∧ '.join(clauses) + ')'
    paths = load_parent(report, module, checksum)
    return dict(tag=tag, module=module, k=k, property=prop, key=report['key'],
                paths=paths, import_line=f'public import {package}.{module}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--blocks', required=True, type=Path)
    parser.add_argument('--first-cell', required=True, type=Path)
    parser.add_argument('--paired', type=Path, help='also instantiate the signed birth path')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--below', type=Path, help='retain both strict height bounds on this trajectory')
    group.add_argument('--contacts', type=Path, help='retain the first transverse contacts on this trajectory')
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/signed-action-prefix')
    args = parser.parse_args()
    if (args.below or args.contacts) and not args.paired:
        parser.error('a field-strength observable requires its signed trajectory')
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean', '--version')
    args.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    checksum = digest(RECORD)
    keys = [version, checksum, digest(DESIGN/'DommaschkSignedMirrorSlope.trace'),
            digest(DESIGN.parent/'Certificates/MirrorActionBlockBounds.trace')]
    paths = []
    for file, name in [(args.blocks, 'DommaschkPhysicalLaunchBlocks'),
                       (args.first_cell, 'DommaschkFirstPhysicalActionCell')]:
        report = json.loads(file.read_text())
        paths.extend(load_parent(report, name, checksum))
        keys.append(report['key'])
    overlay = merge_import_roots(args.cache, paths, keys)
    name = 'DommaschkSignedActionBounds'
    source = (HERE/'templates/signed_action_physical.lean.tpl').read_text()
    root, marker = compile_modules(args.cache/name, [(name, source, ['keep','launch','earliest'])],
                                   [overlay], keys, args, 'SignedActionBridgeCache')
    if args.paired:
        pair = json.loads(args.paired.read_text())
        n = pair['slabs_per_direction']
        if n < 2:
            parser.error('the two action block edges must lie in the interior of the signed path')
        deps = load_parent(pair, f'DommaschkPairedPrefix{n:03}', checksum)
        keys = [*keys, marker['key'], pair['key']]
        history = None
        if args.below or args.contacts:
            history = observable(args.below or args.contacts, n, pair, checksum, bool(args.below))
            deps.extend(history['paths'])
            keys.append(history['key'])
        overlay = merge_import_roots(args.cache, [root, overlay, *deps], keys)
        name, source = application(n, history)
        root, marker = compile_modules(args.cache/name, [(name, source, ['from_birth'])],
                                       [overlay], keys, args, 'SignedActionPrefixCache')
    result = {k:v for k,v in marker.items() if k != 'artifacts'}
    result.update(packet_sha256=checksum, import_paths=list(map(str, (root, overlay))))
    save(args.output, result)
    print(name, result['key'], flush=True)


if __name__ == '__main__':
    main()
