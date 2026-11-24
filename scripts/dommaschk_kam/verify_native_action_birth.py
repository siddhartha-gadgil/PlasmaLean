"""Attach consecutive original quadrature blocks to one authenticated Q-16 birth trajectory."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from emit_sparse_taylor_slab import ROOT, RECORD
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_native_action_columns import header
from verify_native_path_cells import PACKAGE as CELL_PACKAGE
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'NativeActionBirthCache'


def geometry(i):
    name = f'DommaschkNativeArcCells{i:03d}'
    cell = f'DommaschkNativePathCellsPaired{i:03d}'
    model = f'DommaschkNativeActionPaired{i:03d}'
    tick = f'DommaschkNativeTicksPaired{i:03d}'
    cast = f'(({i}:ℕ):ℝ)' if i < 2 else f'({i}:ℝ)'
    cast_simp = ('Nat.cast_zero','Nat.cast_one')[i] if i < 2 else None
    tube_simp = f'  simp only [{cast_simp}] at tube\n' if cast_simp else ''
    hq_simp = f'  simp only [{cast_simp}] at hq\n' if cast_simp else ''
    tube_arg = f'(by simpa only [{cast_simp}] using hq)' if cast_simp else 'hq'
    src = header(name,[f'{CELL_PACKAGE}.{cell}', 'PlasmaLean.Design.DommaschkPhysicalArcTrace'])
    src += '''open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkSignedObservable
open DommaschkPhysicalActionPanel DommaschkBounceField DommaschkKam
'''
    for back in (False,True):
        mode = 'backward' if back else 'forward'
        phi = '(-q)' if back else 'q'
        flag = 'true' if back else 'false'
        branch = 'br' if back else 'fr'
        time = f'(-(({cast}+1)/64))' if back else f'({cast}/64)'
        method = 'backward_physical' if back else 'physical'
        src += f'''
theorem {mode} {{n : ℕ}} {{fs bs : Certificates.PositionFrameSlabs.State}} {{fr br : List Step}}
    {{x : Plane}} {{y : ℝ → Plane}} (path : Path n fs bs fr br x y) (inside : {i+1} < n)
    (hr : {i} < {branch}.length) (row_eq : {branch}[{i}] = {cell}.{mode}Row) :
    Cells true (fun t => ‖deriv (fun s => Contract.cylPoint (y s 0) s (y s 1)) t‖)
      (fun t => strength t (y t)) {cell}.height {time} 48 {cell}.{mode}Block.packed := by
  rw [{cell}.{mode}_archive]
  apply NativeActionInterval.{mode}_cells (i := {i})
  obtain ⟨_,prev,tube⟩ := path.at_row (show {i} < n by omega) {flag} hr
{tube_simp}  change ∀ q ∈ Icc ({i}/64:ℝ) ((({i}:ℝ)+1)/64), y {phi} ∈
    (physicalSlab prev {branch}[{i}] ({i}/64)).tube q at tube
  rw [row_eq] at tube
  intro j q hq hs
  have space := tube q {tube_arg}
  rw [show (({i}:ℕ):ℝ) + 1 = {i+1} by norm_num] at hq
  rw [show 2*(({i}:ℕ):ℝ)+1 = {2*i+1} by norm_num] at hs
{hq_simp}  obtain ⟨radius,den,_⟩ := {model}.{method} hq space
  obtain ⟨_,cert⟩ := {tick}.checked j
  have hd : 0 < atPoint dD (y {phi} 0) {phi} (y {phi} 1) := by
    apply pos_of_mem cert.den_pos
    exact onPanel_mem (time_mem hs) den
  have stop : ({i+1}:ℝ) < n := by exact_mod_cast inside
  have interior : {phi} ∈ Ioo (-(n:ℝ)/64) (n/64) :=
    ⟨by linarith [hq.1,hq.2], by linarith [hq.1,hq.2]⟩
  rw [arcDensity_on_path path interior radius hd]
  exact {cell}.{mode}_point j hq space hs
'''
    return name,src+f'end PlasmaLean.Design.{name}\n',['forward','backward']


def cellref(k):
    back = k < 325
    i = 324-k if back else k-325
    return i, 'backward' if back else 'forward'


def cover_source(n,left,right,children=None):
    name = f'DommaschkNativeCover{n:03d}L{left:03d}R{right:03d}'
    fwd,back = f'DommaschkPhysicalPrefix{n:03}',f'DommaschkBackwardPrefix{n:03}'
    pair = f'DommaschkPairedPrefix{n:03}'
    deps = sorted({f'DommaschkNativeArcCells{cellref(j)[0]:03}' for j in range(left,right)})
    if children:
        deps = [item[0] for item in children]
    src = header(name,[f'PairedPrefixCache.{pair}','PlasmaLean.Certificates.MirrorActionBlockBounds',
                       *[f'{PACKAGE}.{d}' for d in deps]])
    src += f'''
open DommaschkMirrorTubeCrossing DommaschkSignedObservable Certificates.PositionFrameSlabs
abbrev blocks := (DommaschkActionQ0R470.slabs.drop {left}).take {right-left}
abbrev start : ℝ := ({left}:ℝ)/64-325/64
abbrev height : ℝ := (DommaschkFirstMirrorLaunchSign.height true : ℚ)
def Covered (y : ℝ → Plane) : Prop :=
  Covers true (fun t => ‖deriv (fun s => Contract.cylPoint (y s 0) s (y s 1)) t‖)
    (fun t => strength t (y t)) height start blocks

theorem path_cover {{x : Plane}} {{y : ℝ → Plane}}
    (path : Path {n} {fwd}.exitState {back}.exitState {fwd}.rows {back}.rows x y) : Covered y := by
'''
    if children:
        (lower,lo_count),(upper,_) = children
        src += f'''  have adjacent : blocks = {lower}.blocks ++ {upper}.blocks := by with_unfolding_all rfl
  unfold Covered
  rw [adjacent, covers_append_iff]
  refine ⟨{lower}.path_cover path, ?_⟩
  have clock : start + {lower}.blocks.length / 64 = {upper}.start := by
    change start + ({lo_count}:ℝ)/64 = _
    norm_num [start,{upper}.start]
  rw [clock]
  exact {upper}.path_cover path
'''
    else:
        rows = [cellref(j) for j in range(left,right)]
        names = [f'DommaschkNativePathCellsPaired{i:03}.{mode}Block' for i,mode in rows]
        src += ('  unfold Covered\n  have original : blocks = ['+', '.join(names)+
                '] := by with_unfolding_all rfl\n  rw [original]\n  refine ⟨'
                +', '.join(['?_']*(right-left)+['trivial'])+'⟩\n')
        for i,mode in rows:
            src += f'''  · have h := DommaschkNativeArcCells{i:03}.{mode} path (by norm_num)
      (by change {i} < {n}; norm_num) (by with_unfolding_all rfl)
    convert h using 1 <;> norm_num [start,height,DommaschkNativePathCellsPaired{i:03}.height,
      DommaschkNativeTicksPaired{i:03}.height,DommaschkFirstMirrorLaunchSign.height]
'''
    src += f'''
theorem from_birth : BirthWith (fun x => ∃ y, Path {n} {fwd}.exitState {back}.exitState
    {fwd}.rows {back}.rows x y ∧ Covered y) := by
  apply birth_with {pair}.exists_nested_paired
  exact fun _ _ path => path_cover path
end PlasmaLean.Design.{name}
'''
    return name,src,['path_cover','from_birth']


def compile_waves(n,left,right,env,roots,keys,cache):
    rows = sorted({cellref(j)[0] for j in range(left,right)})
    declarations = [geometry(i) for i in rows]
    def tree(l,r):
        children = None
        if r-l > 8:
            mid = (l+r)//2
            children = [tree(l,mid),tree(mid,r)]
        item = cover_source(n,l,r,children)
        declarations.append(item)
        return item[0],r-l
    top,_ = tree(left,right)
    overlay = merge_import_roots(cache,roots,keys)
    base,rec = compile_modules(cache/top,declarations,[overlay],keys,env,PACKAGE)
    return base,rec,overlay


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--paired',type=Path,required=True,help='Audited paired physical trajectory prefix')
    p.add_argument('--blocks',nargs=2,type=int,required=True,metavar=('FIRST','STOP'))
    p.add_argument('--row-cache',type=Path,default=ROOT/'.lake/native-path-cells')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/native-action-birth')
    p.add_argument('--output',type=Path,required=True)
    a = p.parse_args()
    left,right = a.blocks
    if not 0 <= left < right <= 650:
        p.error('expected a nonempty chronological block range within [0,650)')
    pair = json.loads(a.paired.read_text())
    n = pair['slabs_per_direction']
    signed_hash = digest(RECORD)
    if pair['module'] != f'DommaschkPairedPrefix{n:03}' or pair['packet_sha256'] != signed_hash:
        raise ValueError('paired prefix belongs to another archive')
    if any(cellref(j)[0]+1 >= n for j in range(left,right)):
        p.error('both closed edges must lie in the interior of the trajectory for its ordinary derivative')
    roots = list(map(Path,pair['import_paths']))
    admitted(roots[0],pair['module'],pair['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    keys = [lake('lean','--version'), signed_hash, digest(DESIGN/'DommaschkPhysicalArcTrace.trace'),
            digest(DESIGN.parent/'Certificates/MirrorActionBlockBounds.trace'),pair['key']]
    for i in sorted({cellref(k)[0] for k in range(left,right)}):
        report = json.loads((a.row_cache/'paired-rows'/f'{i:03}.json').read_text())
        if report['module'] != f'DommaschkNativePathCellsPaired{i:03}' or report['packet_sha256'] != signed_hash:
            raise ValueError(f'wrong physical action row {i}')
        paths = list(map(Path,report['import_paths']))
        admitted(paths[0],report['module'],report['key'])
        keys.append(report['key'])
        roots.extend(paths)
    base,rec,overlay = compile_waves(n,left,right,env,roots,keys,a.cache)
    out = {k:v for k,v in rec.items() if k != 'artifacts'}
    out.update(packet_sha256=signed_hash,paired=pair['key'],length=n,block_range=[left,right],
               physical_cells=48*(right-left),import_paths=[str(base),str(overlay)])
    save(a.output,out)
    print(out['module'],out['key'],flush=True)


if __name__ == '__main__':
    main()
