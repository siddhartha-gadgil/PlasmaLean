"""Prove a strict signed submirror interval on the actual field line of every Q-16 birth."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def sign_name(i, core=False):
    if core:
        return f'DommaschkCoreSign{i:03}'
    return ('DommaschkUpperPreMirrorSign' if i >= 316 else 'DommaschkPreMirrorSign') + f'{i:03}'


def generate(n,k,upper=False,core=False):
    stem = 'DommaschkUpperSubmirror' if upper else 'DommaschkSubmirror'
    if core:
        stem = 'DommaschkCoreSubmirror'
    name = stem + (f'{k:03}Of{n:03}' if n is not None else f'Rows{k:03}')
    height = 'DommaschkCoreClearance.height' if core else 'DommaschkFirstMirrorLaunchSign.height ' + str(upper).lower()
    sign_package = 'CoreClearanceCache' if core else 'PreMirrorSignCache'
    src = 'module\n'
    if n is not None:
        fw, bw = f'DommaschkPhysicalPrefix{n:03}', f'DommaschkBackwardPrefix{n:03}'
        src += f'public import PairedPrefixCache.DommaschkPairedPrefix{n:03}\n'
    src += 'public import PlasmaLean.Design.DommaschkSignedObservable\n'
    src += ''.join(f'public import {sign_package}.{sign_name(i, core)}\n' for i in range(k))
    src += f'''
/-! # Signed strict submirror interval along the same physical line from every Q-16 birth. -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkMirrorTubeCrossing
open DommaschkSignedObservable
set_option maxRecDepth 16384
set_option linter.style.longLine false
'''
    if k > 160:
        src += 'set_option maxHeartbeats 3000000\n'
    if upper:
        src += '''
private theorem higher : (DommaschkFirstMirrorLaunchSign.height false : ℝ) <
    DommaschkFirstMirrorLaunchSign.height true := by norm_num [DommaschkFirstMirrorLaunchSign.height]
'''
    for tag, direction, angle in (('fwd', 'Fwd', 't'), ('back', 'Back', '(-t)')):
        if n is None:
            rows = tag + 'Rows'
            ids = [f'DommaschkPositionFrames{direction}.block{i//16}[{i%16}]' for i in range(k)]
            src += f'\ndef {rows} : List Step := [\n  '+',\n  '.join(ids)+']\n'
        else:
            rows = f'({fw if tag == "fwd" else bw}.rows.take {k})'
        src += f'''
theorem {tag}_checked : OnTubes (fun t p => strength {angle} p < {height})
    (MirrorEndpoint.start .q0r470) 0 {rows} := by
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) / 64 by norm_num]
'''
        for i in range(k):
            sign = f'{sign_name(i, core)}.{tag}_tube_below ht hx'
            proof = f'({sign}).trans higher' if upper and i < 316 else sign
            src += f'''  refine OnTubes.cons_at {i} ?_ ?_
  · intro t ht x hx
    have start : (({i} : ℕ) : ℝ) / 64 = ({i} : ℝ) / 64 := by norm_num
    have stop : ((({i}+1 : ℕ) : ℝ)) / 64 = ({i+1} : ℝ) / 64 := by norm_num
    rw [start, stop] at ht
    rw [start] at hx
    with_unfolding_all exact {proof}
'''
        src += '  trivial\n'
    if n is None:
        return name,src+'\nend PlasmaLean.Design.'+name+'\n',['fwd_checked','back_checked']
    src += f'''
/-- One Q-16-launched field line satisfies the strict bound throughout the whole signed interval. -/
theorem below_from_birth :
    BirthWith (fun x => ∃ y, Path {n} {fw}.exitState {bw}.exitState {fw}.rows {bw}.rows x y ∧
      ∀ t ∈ Set.Icc (-({k} : ℝ) / 64) ({k}/64),
        strength t (y t) < {height}) := by
  apply birth_with DommaschkPairedPrefix{n:03}.exists_nested_paired
  intro x y path
  exact path.below_on (k := {k}) (by norm_num) rfl rfl fwd_checked back_checked

end PlasmaLean.Design.{name}
'''
    if core:
        src = src.replace('  exact path.below_on', '  simpa only [Nat.cast_one, Nat.cast_ofNat] using path.below_on')
    return name,src,['fwd_checked','back_checked','below_from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--paired', type=Path)
    mode.add_argument('--rows-only', action='store_true',
                      help='check coverage of the entire ordered spatial archive without assuming a trajectory')
    p.add_argument('--signs', type=Path, nargs='+', required=True)
    p.add_argument('--length', type=int, required=True)
    heights = p.add_mutually_exclusive_group()
    heights.add_argument('--upper', action='store_true', help='use the higher mirror height through row 323')
    heights.add_argument('--core', action='store_true', help='use the certified height below the first mirror band')
    p.add_argument('--output', type=Path)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/signed-mirrors')
    a = p.parse_args()
    k = a.length
    packet_hash = digest(RECORD)
    n, paired_key, deps = None, None, []
    if not 1 <= k <= (324 if a.upper else 316):
        p.error('the submirror prefix must fit the selected mirror bracket')
    if a.paired:
        paired = json.loads(a.paired.read_text())
        n,paired_key = paired['slabs_per_direction'],paired['key']
        if k > n or paired['packet_sha256'] != packet_hash:
            p.error('the submirror prefix must fit this archived birth trajectory')
        deps = list(map(Path, paired['import_paths']))
        admitted(deps[0], f'DommaschkPairedPrefix{n:03}', paired_key)
    records = {}
    for file in a.signs:
        data = json.loads(file.read_text())
        for row in (data['rows'] if a.core else data):
            i = row['index']
            if i in records and row['key'] != records[i]['key']:
                p.error(f'conflicting signs for row {i}')
            records[i] = row
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version = lake('lean','--version')
    keys = [version, paired_key, digest(DESIGN/'DommaschkSignedObservable.trace')]
    for i in range(k):
        if i not in records:
            p.error(f'missing sign proof for row {i}')
        row = records[i]
        if row['packet_sha256'] != packet_hash or row['lean_version'] != version:
            p.error(f'row {i} has a different witness or Lean version')
        roots = list(map(Path,row['import_paths']))
        admitted(roots[0], sign_name(i, a.core), row['key'])
        keys.append(row['key'])
        deps.extend(roots)
    overlay = merge_import_roots(a.cache, deps, keys)
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    decl = generate(n,k,a.upper,a.core)
    root, record = compile_modules(a.cache/decl[0], [decl], [overlay], keys, env, 'SubmirrorPrefixCache')
    out = {key:v for key,v in record.items() if key != 'artifacts'}
    out.update(packet_sha256=packet_hash, paired_key=paired_key, slabs=k, upper=a.upper,
               import_paths=[str(root),str(overlay)])
    if a.core:
        out['core_height'] = True
    if a.output:
        save(a.output,out)
    print(json.dumps(out),flush=True)


if __name__ == '__main__':
    main()
