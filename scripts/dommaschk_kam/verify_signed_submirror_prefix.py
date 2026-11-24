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


def generate(n,k):
    name = f'DommaschkSubmirror{k:03}Of{n:03}'
    fw, bw = f'DommaschkPhysicalPrefix{n:03}', f'DommaschkBackwardPrefix{n:03}'
    src = f'module\npublic import PairedPrefixCache.DommaschkPairedPrefix{n:03}\n'
    src += 'public import PlasmaLean.Design.DommaschkSignedObservable\n'
    src += ''.join(f'public import PreMirrorSignCache.DommaschkPreMirrorSign{i:03}\n' for i in range(k))
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
    for tag, prefix, angle in (('fwd', fw, 't'), ('back', bw, '(-t)')):
        src += f'''
theorem {tag}_checked : OnTubes (fun t p => strength {angle} p < DommaschkFirstMirrorLaunchSign.height false)
    (MirrorEndpoint.start .q0r470) 0 ({prefix}.rows.take {k}) := by
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) / 64 by norm_num]
'''
        for i in range(k):
            src += f'''  refine OnTubes.cons_at {i} ?_ ?_
  · intro t ht x hx
    have start : (({i} : ℕ) : ℝ) / 64 = ({i} : ℝ) / 64 := by norm_num
    have stop : ((({i}+1 : ℕ) : ℝ)) / 64 = ({i+1} : ℝ) / 64 := by norm_num
    rw [start, stop] at ht
    rw [start] at hx
    with_unfolding_all exact DommaschkPreMirrorSign{i:03}.{tag}_tube_below ht hx
'''
        src += '  trivial\n'
    src += f'''
/-- One Q-16-launched field line satisfies the strict bound throughout the whole signed interval. -/
theorem below_from_birth :
    BirthWith (fun x => ∃ y, Path {n} {fw}.exitState {bw}.exitState {fw}.rows {bw}.rows x y ∧
      ∀ t ∈ Set.Icc (-({k} : ℝ) / 64) ({k}/64),
        strength t (y t) < DommaschkFirstMirrorLaunchSign.height false) := by
  apply birth_with DommaschkPairedPrefix{n:03}.exists_nested_paired
  intro x y path
  exact path.below_on (k := {k}) (by norm_num) rfl rfl fwd_checked back_checked

end PlasmaLean.Design.{name}
'''
    return name,src,['fwd_checked','back_checked','below_from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--paired', type=Path, required=True)
    p.add_argument('--signs', type=Path, nargs='+', required=True)
    p.add_argument('--length', type=int, required=True)
    p.add_argument('--output', type=Path)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/signed-mirrors')
    a = p.parse_args()
    paired = json.loads(a.paired.read_text())
    n, k = paired['slabs_per_direction'], a.length
    if not 1 <= k <= min(n,316) or paired['packet_sha256'] != digest(RECORD):
        p.error('the submirror prefix must fit both the paired trajectory and the 316 preceding slabs')
    deps = list(map(Path, paired['import_paths']))
    admitted(deps[0], f'DommaschkPairedPrefix{n:03}', paired['key'])
    records = {}
    for file in a.signs:
        for row in json.loads(file.read_text()):
            i = row['index']
            if i in records and row['key'] != records[i]['key']:
                p.error(f'conflicting signs for row {i}')
            records[i] = row
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version = lake('lean','--version')
    keys = [version, paired['key'], digest(DESIGN/'DommaschkSignedObservable.trace')]
    for i in range(k):
        if i not in records:
            p.error(f'missing sign proof for row {i}')
        row = records[i]
        if row['packet_sha256'] != paired['packet_sha256'] or row['lean_version'] != version:
            p.error(f'row {i} has a different witness or Lean version')
        roots = list(map(Path,row['import_paths']))
        admitted(roots[0], f'DommaschkPreMirrorSign{i:03}', row['key'])
        keys.append(row['key'])
        deps.extend(roots)
    overlay = merge_import_roots(a.cache, deps, keys)
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    decl = generate(n,k)
    root, record = compile_modules(a.cache/decl[0], [decl], [overlay], keys, env, 'SubmirrorPrefixCache')
    out = {key:v for key,v in record.items() if key != 'artifacts'}
    out.update(packet_sha256=paired['packet_sha256'], paired_key=paired['key'], slabs=k,
               import_paths=[str(root),str(overlay)])
    if a.output:
        save(a.output,out)
    print(json.dumps(out),flush=True)


if __name__ == '__main__':
    main()
