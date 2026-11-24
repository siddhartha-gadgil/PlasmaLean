"""Prove a common clearance below the lower height using the accepted pre-mirror Taylor models."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import json
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


PACKAGE = 'CoreClearanceCache'
ORIGINAL = 'DommaschkFirstMirrorLaunchSign.height false'
HEIGHT = 'DommaschkCoreClearance.height'
BOUND = Fraction(1, 125000)


def gap_source(source, old_name):
    """Retain the original checked field models and their rational enclosure at the archived height."""
    name = old_name.replace('DommaschkBeforeGap', 'DommaschkCoreGap', 1)
    source = source.replace(old_name, name)
    source = source.replace('public import PlasmaLean.Design.DommaschkPreMirrorSigns',
                            'public import PlasmaLean.Design.DommaschkPreMirrorSigns\n'
                            'public import PlasmaLean.Design.DommaschkCoreClearance')
    before, body = source.split('theorem sign_on_models', 1)
    statement, proof = body.split(':= by', 1)
    if statement.count(ORIGINAL) != 1:
        raise ValueError(f'{name}: unexpected strength predicate')
    statement = statement.replace(ORIGINAL, HEIGHT)
    proof, tail = proof.split('  rw [g] at bound\n', 1)
    matches = re.findall(r'have bound := enclose \(c := ⟨\[\(([^)]+)\)\],\(([^)]+)\)⟩\)', proof)
    if len(matches) != 1 or 'linarith only [bound.1,bound.2]' not in tail:
        raise ValueError(f'{name}: missing exact Taylor enclosure')
    midpoint, radius = map(Fraction, matches[0])
    margin = -(midpoint + radius)
    if margin < BOUND:
        raise ValueError(f'{name}: the actual clearance {margin} is too small')
    proof += '''  rw [g] at bound
  have unit := enclose (c := ⟨[(1/2)], 1/2⟩) hw rad (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at unit bound
  apply DommaschkCoreClearance.of_gap
  · linarith only [unit.1]
  · linarith only [unit.2]
  · change gap R (DommaschkFirstMirrorLaunchSign.height false) D nr nz ≤ -(1 / 125000)
    linarith only [bound.2]
'''
    final = before + 'theorem sign_on_models' + statement + ':= by' + proof
    return (name, final + f'\nend PlasmaLean.Design.{name}\n', ['sign_on_models']), margin


def row(i, args):
    info = json.loads((args.signs / 'rows' / f'{i:03}.json').read_text())
    original_name = f'DommaschkPreMirrorSign{i:03}'
    if (info['index'], info['module'], info['packet_sha256'], info['lean_version']) != (
            i, original_name, args.packet, args.version):
        raise ValueError(f'wrong original signed row {i}')
    root, overlay = map(Path, info['import_paths'])
    admitted(root, original_name, info['key'])
    source = (root / 'PreMirrorSignCache' / f'{original_name}.lean').read_text()
    imports = re.findall(r'^public import PreMirrorGapCache\.(\w+)$', source, re.M)
    if not imports:
        raise ValueError(f'no gap enclosures in original row {i}')
    declarations, margins, keys = [], [], []
    for module in imports:
        obj = (overlay / 'PreMirrorGapCache' / f'{module}.olean').resolve(strict=True)
        origin = obj.parent.parent
        accepted = admitted(origin, module, origin.name)
        decl, margin = gap_source(obj.with_suffix('.lean').read_text(), module)
        declarations.append(decl)
        margins.append(margin)
        keys.append(accepted['key'])
        source = source.replace(module, decl[0])
    name = f'DommaschkCoreSign{i:03}'
    source = source.replace(original_name, name).replace('PreMirrorGapCache.', PACKAGE + '.')
    source = source.replace(ORIGINAL, HEIGHT)
    source = source.replace('[DommaschkFirstMirrorLaunchSign.height]',
                            '[DommaschkCoreClearance.height, DommaschkFirstMirrorLaunchSign.height]')
    declarations.append((name, source, ['fwd_tube_below', 'back_tube_below']))
    output, accepted = compile_modules(args.cache / name, declarations, [overlay],
                                       [args.version, args.packet, args.bridge, info['key'], keys],
                                       args, PACKAGE)
    report = {k: v for k, v in accepted.items() if k != 'artifacts'}
    report.update(index=i, margin=str(min(margins)), packet_sha256=args.packet, lean_version=args.version,
                  original_key=info['key'], import_paths=[str(output), str(overlay)])
    save(args.cache / 'rows' / f'{i:03}.json', report)
    print(f'{name}: {report["key"]} (clearance {report["margin"]})', flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    span = parser.add_mutually_exclusive_group(required=True)
    span.add_argument('--range', nargs=2, type=int, metavar=('FIRST', 'LAST'))
    span.add_argument('--rows', nargs='+', type=int)
    parser.add_argument('--workers', default=1, type=int)
    parser.add_argument('--signs', type=Path, default=ROOT / '.lake/pre-mirror-signs')
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/core-clearance')
    parser.add_argument('--output', type=Path)
    cli = parser.parse_args()
    indices = cli.rows or list(range(cli.range[0], cli.range[1] + 1))
    if not indices or min(indices) < 0 or max(indices) >= 316 or cli.workers < 1:
        parser.error('use rows in 0–315 and at least one worker')

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    (cli.cache / 'rows').mkdir(parents=True, exist_ok=True)
    args = SimpleNamespace(**vars(cli), lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                           lean_path=lake('printenv', 'LEAN_PATH'), version=lake('lean', '--version'),
                           packet=digest(RECORD), bridge=digest(DESIGN / 'DommaschkCoreClearance.trace'))
    with ThreadPoolExecutor(max_workers=cli.workers) as pool:
        reports = list(pool.map(lambda i: row(i, args), indices))
    if cli.output:
        save(cli.output, dict(packet_sha256=args.packet, lean_version=args.version, rows=reports))


if __name__ == '__main__':
    main()
