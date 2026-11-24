"""Prove both chronological action blocks on one signed physical path using one native Horner trace."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace
import time

from emit_sparse_taylor_slab import ROOT, RECORD
from verify_backward_physical_prefix import compile_modules, union
import verify_native_action_columns as ticks
import verify_native_action_models as models
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_sparse_reference_slabs import GIB, available_ram


PACKAGE = 'NativePathCellCache'


def row_source(i, model, tick):
    name = f'DommaschkNativePathCellsPaired{i:03d}'
    src = ticks.header(name, [models.OUTPUT_PACKAGE+'.'+model, ticks.PACKAGE+'.'+tick,
                      'PlasmaLean.Certificates.NativeActionArchivePair',
                      'PlasmaLean.Design.DommaschkSignedObservable'])
    src += '''
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkSignedObservable
open DommaschkPhysicalActionPanel DommaschkBounceField
'''
    bg, bo = divmod(324-i,16)
    src += f'''
abbrev height := {tick}.height
abbrev forwardArchive := {tick}.archive
def backwardArchive := DommaschkActionQ0R470.slabGroup{bg}[{bo}].packed
def backwardRecord (j : ℕ) := backwardArchive >>> (72*(47-j))

theorem mirrored (j : Fin 48) : SameDigits ({tick}.record j) (backwardRecord j) := by
  fin_cases j <;> constructor <;> with_unfolding_all rfl
'''
    for backward in (False,True):
        mode = 'backward' if backward else 'forward'
        phi = '(-q)' if backward else 'q'
        row = 'backRow' if backward else 'row'
        bound = 'backward_physical' if backward else 'physical'
        arc = f'{mode}Archive'
        record = 'backwardRecord' if backward else tick+'.record'
        chrono = 324-i if backward else 325+i
        time = f'(-((({i}:ℝ)+1)/64))' if backward else f'(({i}:ℝ)/64)'
        branch = 'br' if backward else 'fr'
        flag = 'true' if backward else 'false'
        src += f'''
abbrev {mode}Row := {model}.{row}
abbrev {mode}Block := DommaschkActionQ0R470.slabs[{chrono}]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)
theorem {mode}_archive : {mode}Block.packed = {arc} := by with_unfolding_all rfl

theorem {mode}_point {{prev : Certificates.PositionFrameSlabs.State}} {{q : ℝ}} {{x : Plane}}
    (j : Fin 48) (hq : q ∈ Icc ({i}/64:ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {mode}Row ({i}/64)).tube q)
    (hs : 128*q-{2*i+1} ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1)) :
    arcDensity (x 0) {phi} (x 1) ≤ density ({record} j) / 1048576 ∧
    max (2*((height:ℝ) - strength {phi} x)) 0 ≤ speedSq ({record} j) / 67108864 := by
  obtain ⟨hr,hd,h8,h16,hu,hn⟩ := {model}.{bound} hq hx
  rw [← DommaschkNativeActionGeometry.squared_numerator hr {phi}] at hu
  have mem : Five.Rel (fun m z => m.Mem (128*q-{2*i+1}) z)
      {tick}.models (quantities (x 0) {phi} (x 1) height) := by
    with_unfolding_all exact ⟨hd,h8,h16,hu,hn⟩
'''
        if backward:
            src += f'''  obtain ⟨_,cert⟩ := {tick}.checked j
  exact physical hr (by norm_num [height,{tick}.height]) (cert.of_sameDigits (mirrored j))
    (five_mem (time_mem hs) mem)
'''
        else:
            src += f'  exact {tick}.physical_columns j hs hr mem\n'
        src += f'''
/-- The original block at chronological index {chrono}, evaluated on the prescribed path. -/
theorem {mode}_cells {{n : ℕ}} {{fs bs : Certificates.PositionFrameSlabs.State}}
    {{fr br : List Step}} {{x : Plane}} {{y : ℝ → Plane}} (path : Path n fs bs fr br x y)
    (within : {i} < n) (hr : {i} < {branch}.length) (row_eq : {branch}[{i}] = {mode}Row) :
    Cells true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
      height {time} 48 {mode}Block.packed := by
  rw [{mode}_archive]
  apply NativeActionInterval.{mode}_cells (i := {i})
  obtain ⟨_,prev,tube⟩ := path.at_row within {flag} hr
  change ∀ q ∈ Icc ({i}/64:ℝ) ((({i}:ℝ)+1)/64), y {phi} ∈
    (physicalSlab prev {branch}[{i}] ({i}/64)).tube q at tube
  rw [row_eq] at tube
  intro j q hq hs
  have space := tube q hq
  rw [show (({i}:ℕ):ℝ) + 1 = {i+1} by norm_num] at hq
  rw [show 2*(({i}:ℕ):ℝ)+1 = {2*i+1} by norm_num] at hs
  exact {mode}_point j hq space hs
'''
    return name, src+f'end PlasmaLean.Design.{name}\n', ['forward_cells','backward_cells']


def verify(i,args):
    emitted = ticks.check((i,False,args.version,args,args.tick_cache,True))
    tick_dir = Path(emitted['import_paths'][0])
    tick = (tick_dir,json.loads((tick_dir/'accepted.json').read_text()))
    ma = SimpleNamespace(**{**vars(args), 'cache':args.model_cache, 'row':i, 'direction':1,
                            'paired':True, 'fields':list(range(4))})
    field_data = models.static_data()
    static = models.verify_static(ma,field_data)
    pieces = models.verify_row(ma,field_data,static)
    deps = [*static,*pieces,tick]
    item = row_source(i,pieces[-1][1]['module'],emitted['module'])
    overlay = union(args.cache,deps)
    structural = [digest(DESIGN/'DommaschkSignedObservable.trace'),
                  digest(DESIGN.parent/'Certificates/NativeActionArchivePair.trace')]
    base,result = compile_modules(args.cache/item[0],[item],[overlay],
                                  [args.version,digest(RECORD),structural,*[m['key'] for _,m in deps]],
                                  args,PACKAGE)
    out = {k:v for k,v in result.items() if k != 'artifacts'}
    out.update(index=i, panels=96, archive_indices=[324-i,325+i], packet_sha256=digest(RECORD),
               model=pieces[-1][1]['key'], ticks=emitted['key'],
               import_paths=[str(base),str(overlay)])
    save(base/'row.json',out)
    save(args.cache/'paired-rows'/f'{i:03}.json',out)
    print(f'{item[0]} accepted {result["key"]}',flush=True)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    select = parser.add_mutually_exclusive_group(required=True)
    select.add_argument('--row', type=int, choices=range(325), metavar='0..324')
    select.add_argument('--range', type=int, nargs=2, metavar=('FIRST','LAST'))
    parser.add_argument('--workers', type=int, choices=range(1,9), default=2)
    parser.add_argument('--reserve-gib', type=int, default=32)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/native-path-cells')
    parser.add_argument('--model-cache', type=Path, default=ROOT/'.lake/native-action-checks')
    parser.add_argument('--tick-cache', type=Path, default=ROOT/'.lake/native-action-columns')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()
    args.version = lake('lean','--version')
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    (args.cache/'paired-rows').mkdir(exist_ok=True,parents=True)
    if args.row is not None:
        result = verify(args.row,args)
        if args.output:
            save(args.output,result)
        return
    first, last = args.range
    if not (0 <= first <= last < 325) or args.reserve_gib < 0:
        parser.error('require 0 ≤ FIRST ≤ LAST < 325 and a nonnegative memory reserve')
    pending = set(range(first,last+1))
    active, records = {}, {}
    began = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while pending or active:
            for i in sorted(pending):
                if len(active) >= args.workers or available_ram() < (args.reserve_gib+4)*GIB:
                    break
                if (args.model_cache/'paired-rows'/f'{i:03}.json').is_file():
                    active[pool.submit(verify,i,args)] = i
                    pending.remove(i)
            if active:
                done, _ = wait(active,timeout=10,return_when=FIRST_COMPLETED)
                for item in done:
                    i = active.pop(item)
                    row = item.result()
                    records[i] = {'index':i,'key':row['key']}
            elif pending:
                time.sleep(10)
            if args.output:
                save(args.output, {'range':[first,last],'accepted_pairs':len(records),
                     'accepted_cells':96*len(records),'complete':not pending and not active,
                     'active_indices':sorted(active.values()), 'elapsed_seconds':round(time.monotonic()-began),
                     'records':[records[i] for i in sorted(records)]})


if __name__ == '__main__':
    main()
