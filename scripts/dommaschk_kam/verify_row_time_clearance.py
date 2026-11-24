"""Prove the rowwise reciprocal-speed ceiling from every original signed pre-mirror gap."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


PACKAGE = 'RowTimeGapCache'
HIGH = Fraction(5300546391395933, 5000000000000000)
ORIGINAL = 'DommaschkFirstMirrorLaunchSign.height false'


def name(i):
    return f'DommaschkRowTimeGap{i:03}'


def read_gap(text, module):
    before, body = text.split('theorem sign_on_models', 1)
    statement, proof = body.split(':= by', 1)
    proof, tail = proof.split('  rw [g] at bound\n', 1)
    pattern = r'have bound := enclose \(c := ⟨\[\(([^)]+)\)\],\(([^)]+)\)⟩\)'
    entries = re.findall(pattern, proof)
    if len(entries) != 1 or statement.count(ORIGINAL) != 1 or 'linarith only [bound.1,bound.2]' not in tail:
        raise ValueError(f'{module}: unexpected archived gap conclusion')
    center, error = map(Fraction, entries[0])
    return before, statement, proof, -(center + error)


def row(i, args):
    original = json.loads((args.signs / 'rows' / f'{i:03}.json').read_text())
    old = f'DommaschkPreMirrorSign{i:03}'
    if (original['index'], original['module'], original['lean_version'], original['packet_sha256']) != (
            i, old, args.version, args.packet):
        raise ValueError(f'wrong authenticated signed row {i}')
    root, overlay = map(Path, original['import_paths'])
    admitted(root, old, original['key'])
    src = (root / 'PreMirrorSignCache' / (old+'.lean')).read_text()
    modules = re.findall(r'^public import PreMirrorGapCache\.(\w+)$', src, re.M)
    if not modules:
        raise ValueError(f'missing signed gap models for row {i}')
    sources, margins, upstream = [], [], []
    for mod in modules:
        obj = (overlay / 'PreMirrorGapCache' / (mod+'.olean')).resolve(strict=True)
        origin = obj.parent.parent
        upstream.append(admitted(origin, mod, origin.name)['key'])
        before, statement, proof, margin = read_gap(obj.with_suffix('.lean').read_text(), mod)
        sources.append((before, statement, proof))
        margins.append(margin)
    smallest = min(margins)
    if smallest <= 0:
        raise ValueError(f'row {i} lacks a positive signed gap margin')
    budget = HIGH / smallest
    q = 1 + isqrt(budget.numerator // budget.denominator)
    height = f'(DommaschkRowTimeClearance.testHeight {q})'
    decls = []
    for mod, (before, statement, proof) in zip(modules, sources, strict=True):
        new = mod.replace('DommaschkBeforeGap', 'DommaschkInverseSpeedGap', 1)
        base = 'public import PlasmaLean.Design.DommaschkPreMirrorSigns'
        before = before.replace(mod, new).replace(base, base+'\npublic import PlasmaLean.Design.DommaschkRowTimeClearance')
        proof = before+'theorem sign_on_models'+statement.replace(ORIGINAL, height)+':= by'+proof
        proof += f'''  rw [g] at bound
  have unit := enclose (c := ⟨[(1/2)], 1/2⟩) hw rad (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at unit bound
  apply DommaschkRowTimeClearance.of_gap (L := {ORIGINAL})
  · linarith only [unit.1]
  · linarith only [unit.2]
  · norm_num [DommaschkRowTimeClearance.testHeight, DommaschkFirstMirrorLaunchSign.height]
  · norm_num [DommaschkRowTimeClearance.testHeight, DommaschkFirstMirrorLaunchSign.height] at bound ⊢
    linarith only [bound.2]

end PlasmaLean.Design.{new}
'''
        decls.append((new, proof, ['sign_on_models']))
        src = src.replace(mod, new)
    top = name(i)
    src = src.replace(old, top).replace('PreMirrorGapCache.', PACKAGE+'.').replace(ORIGINAL, height)
    src = src.replace('[DommaschkFirstMirrorLaunchSign.height]',
                      '[DommaschkRowTimeClearance.testHeight, DommaschkFirstMirrorLaunchSign.height]')
    decls.append((top, src, ['fwd_tube_below', 'back_tube_below']))
    base, accepted = compile_modules(args.cache/top, decls, [overlay],
                                     [args.version, args.packet, args.bridge, original['key'], upstream],
                                     args, PACKAGE)
    result = {k: v for k, v in accepted.items() if k != 'artifacts'}
    result.update(index=i, q=q, margin=str(min(margins)), packet_sha256=args.packet,
                  lean_version=args.version, import_paths=[str(base), str(overlay)])
    save(args.cache/'rows'/f'{i:03}.json', result)
    print(f'{i:03}: q={q} {result["key"]}', flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subset = parser.add_mutually_exclusive_group(required=True)
    subset.add_argument('--range', nargs=2, type=int, metavar=('FIRST', 'LAST'))
    subset.add_argument('--rows', nargs='+', type=int)
    parser.add_argument('--workers', default=1, type=int)
    parser.add_argument('--signs', type=Path, default=ROOT/'.lake/pre-mirror-signs')
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/row-time-clearance')
    parser.add_argument('--output', type=Path)
    a = parser.parse_args()
    ids = a.rows or list(range(a.range[0], a.range[1]+1))
    if not ids or min(ids) < 0 or max(ids) >= 316 or len(set(ids)) != len(ids) or a.workers < 1:
        parser.error('expected distinct rows 0–315 and positive worker count')

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    (a.cache/'rows').mkdir(parents=True, exist_ok=True)
    args = SimpleNamespace(**vars(a), lean=str(Path(lake('lean', '--print-prefix'))/'bin/lean'),
                           lean_path=lake('printenv', 'LEAN_PATH'), version=lake('lean', '--version'),
                           packet=digest(RECORD), bridge=digest(DESIGN/'DommaschkRowTimeClearance.trace'))
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        reports = list(pool.map(lambda i: row(i, args), ids))
    if a.output:
        save(a.output, dict(packet_sha256=args.packet, lean_version=args.version, rows=reports,
                            q_sum=sum(r['q'] for r in reports)))


if __name__ == '__main__':
    main()
