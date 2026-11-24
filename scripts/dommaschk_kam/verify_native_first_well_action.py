"""Combine actual first mirror contacts, the positive action floor, and the complete original cap."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace
import time

from emit_sparse_taylor_slab import RECORD, ROOT
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_native_action_birth import PACKAGE as COVER_PACKAGE
from verify_native_action_columns import header
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'NativeFirstWellCache'


def source(n, contacts, floor, cover):
    pair = f'DommaschkPairedPrefix{n:03}'
    fwd,back = f'DommaschkPhysicalPrefix{n:03}',f'DommaschkBackwardPrefix{n:03}'
    name = f'DommaschkNativeFirstWell{"Complete" if cover else "OfCover"}{n:03}'
    deps = ['PlasmaLean.Design.DommaschkNativeWellAction','PlasmaLean.Design.DommaschkFirstMirrorWell',
            'PlasmaLean.Design.DommaschkNativeActionColumns',
            f'SignedMirrorBirthCache.{contacts}',f'SignedActionFloorCache.{floor}']
    if cover:
        deps.append(COVER_PACKAGE+'.'+cover)
    src = header(name,deps)
    src += f'''
open DommaschkSignedObservable DommaschkNativeWellAction
theorem level_eq : ((DommaschkFirstMirrorLaunchSign.height true : ℚ):ℝ) = level := by
  norm_num [DommaschkFirstMirrorLaunchSign.height,level]
abbrev ActualPath (x : Certificates.PositionFrameSlabs.Plane) (y : ℝ → Certificates.PositionFrameSlabs.Plane) :=
  Path {n} {fwd}.exitState {back}.exitState {fwd}.rows {back}.rows x y
def ArchiveOn (y : ℝ → Certificates.PositionFrameSlabs.Plane) : Prop :=
  Covers true (DommaschkNativeWellAction.density y) (field y) level (-325/64) DommaschkActionQ0R470.slabs

theorem bind_archive {{y}} (cells : Covers true (DommaschkNativeWellAction.density y) (field y)
    (DommaschkFirstMirrorLaunchSign.height true) ((0:ℝ)/64-325/64)
    ((DommaschkActionQ0R470.slabs.drop 0).take 650)) : ArchiveOn y := by
  have len : DommaschkActionQ0R470.slabs.length = 650 := DommaschkActionQ0R470.checked.len
  simpa only [ArchiveOn,List.drop_zero,List.take_of_length_le len.le,zero_div,zero_sub,neg_div,level_eq] using cells

theorem on_path {{x y}} (path : ActualPath x y) (cells : ArchiveOn y)
    (first : DommaschkSignedMirrorSlope.FirstTransverseBoth (324/64) (325/64) level (1/400) y) :
    FirstWellAction y := by
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have mass := ({floor}.on_path path).2
  rw [level_eq] at mass
  exact first_well path (by norm_num)
    (fun t ht => region t ⟨by linarith [ht.1], by linarith [ht.2]⟩) mass cells first
'''
    if cover:
        src += f'''
theorem all_cells {{x y}} (path : ActualPath x y) : ArchiveOn y := by
  exact bind_archive ({cover}.path_cover path)
'''
    arg = '' if cover else ' (cells : ∀ x y, ActualPath x y → ArchiveOn y)'
    apply = 'all_cells path' if cover else 'cells _ _ path'
    src += f'''
theorem from_birth{arg} :
    BirthWith (fun x => ∃ y, ActualPath x y ∧
      DommaschkSignedMirrorSlope.FirstTransverseBoth (316/64) (317/64)
        (DommaschkFirstMirrorLaunchSign.height false) (1/128) y ∧
      DommaschkSignedMirrorSlope.FirstTransverseBoth (324/64) (325/64) level (1/400) y ∧
      FirstWellAction y) := by
  apply DommaschkFirstMirrorWell.map_birth {contacts}.contacts_from_birth
  rintro x ⟨y,path,lower,upper⟩
  rw [level_eq] at upper
  exact ⟨y,path,lower,upper,on_path path ({apply}) upper⟩

end PlasmaLean.Design.{name}
'''
    return name,src,['on_path',*(['all_cells'] if cover else []),'from_birth']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paired', required=True,type=Path)
    parser.add_argument('--contacts', required=True,type=Path)
    parser.add_argument('--floor',required=True,type=Path)
    parser.add_argument('--cover',type=Path,help='All 650 original blocks; otherwise check the conditional bridge')
    parser.add_argument('--wait-seconds',type=float,default=0,
                        help='Maximum time to wait for the atomic complete-cover report')
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/native-first-well')
    parser.add_argument('--output',required=True,type=Path)
    args = parser.parse_args()
    pair,contacts,floor = [json.loads(p.read_text()) for p in [args.paired,args.contacts,args.floor]]
    n = pair['slabs_per_direction']
    if n <= 325 or floor['bound'] != '553/2000' or floor['slabs'] != 316 or floor['paired_key'] != pair['key']:
        raise ValueError('expected a complete signed prefix with its 316-slab numeric action floor')
    deps = [(pair,f'DommaschkPairedPrefix{n:03}'),(contacts,f'DommaschkTransverseMirrorBirth{n:03}'),
            (floor,f'DommaschkSignedActionFloor316Of{n:03}')]
    cover = None
    if args.cover:
        deadline = time.monotonic()+args.wait_seconds
        while not args.cover.exists() and time.monotonic() < deadline:
            time.sleep(min(15,max(0,deadline-time.monotonic())))
        cover = json.loads(args.cover.read_text())
        if cover['block_range'] != [0,650] or cover['paired'] != pair['key']:
            raise ValueError('archived cover must include all blocks on the selected trajectory')
        deps.append((cover,f'DommaschkNativeCover{n:03}L000R650'))
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version = lake('lean','--version')
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    packet = digest(RECORD)
    keys = [version,packet,digest(DESIGN/'DommaschkNativeActionColumns.trace'),
            digest(DESIGN/'DommaschkNativeWellAction.trace'),
            digest(DESIGN/'DommaschkFirstMirrorWell.trace')]
    roots = []
    for r,name in deps:
        if r['module'] != name or r['packet_sha256'] != packet:
            raise ValueError(f'wrong parent receipt for {name}')
        paths = list(map(Path,r['import_paths']))
        admitted(paths[0],name,r['key'])
        keys.append(r['key'])
        roots.extend(paths)
    item = source(n,contacts['module'],floor['module'],cover['module'] if cover else None)
    overlay = merge_import_roots(args.cache,roots,keys)
    base,marker = compile_modules(args.cache/item[0],[item],[overlay],keys,env,PACKAGE)
    report = {k:v for k,v in marker.items() if k != 'artifacts'}
    report.update(packet_sha256=packet,paired=pair['key'],complete=bool(cover),floor='553/2000',
                  rectangle_mass='1146552112157123/844424930131968',
                  target_gap='274671348019911459639037/128849018880000000000000000',
                  target='6799610938322487/5000000000000000',height='5300546391395933/5000000000000000',
                  import_paths=[str(base),str(overlay)])
    save(args.output,report)
    print(item[0],report['key'],flush=True)


if __name__ == '__main__':
    main()
