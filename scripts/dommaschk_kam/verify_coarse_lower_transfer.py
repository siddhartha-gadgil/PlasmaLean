"""Transfer checked 48-panel physical rows to their 16-panel lower-action blocks."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_physical_action import PACKAGE
from verify_coarse_secondary_lower import packet_inputs
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_action_cells import PHYSICAL
from verify_signed_mirror_passage import merge_import_roots


def source(i, sign, pack, fine):
    side = 'forward' if sign==1 else 'backward'
    name = f'DommaschkCoarseTransferredQ0R478{side.capitalize()}{i:03}'
    j = pack['counts'][0] + i if sign==1 else pack['counts'][0] - 1 - i
    t = 't' if sign==1 else '(-t)'
    start = f'({i}/64:ℝ)' if sign==1 else f'(-({i+1}:ℝ)/64)'
    table = pack['module']
    src = f'''module
public import PlasmaLean.Certificates.WeakenLowerActionCells
public import {PHYSICAL}.{fine}
public import {pack['package']}.{table}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.MirrorActionQuadrature Certificates.PositionFrameSlabs Set
open DommaschkPhysicalActionPanel DommaschkMirrorTubeCrossing
set_option maxRecDepth 32768
set_option linter.style.longLine false
abbrev row := {fine}.{side}Row
abbrev height := {fine}.height
abbrev phase : ℝ := 0
abbrev block := {table}.slabs[{j}]'(by rw [{table}.checked.len]; norm_num)

theorem columns : lowerColumnsLE 48 block.packed {fine}.{side}Block.packed = true := by
  with_unfolding_all rfl

theorem cells {{prev : State}} {{y : ℝ → Plane}}
    (tube : ∀ t ∈ Icc ({i}/64:ℝ) ({i+1}/64), y {t} ∈ (physicalSlab prev row ({i}/64)).tube t) :
    Cells false (fun t => arcDensity (y t 0) (phase+t) (y t 1)) (fun t => strength (phase+t) (y t))
      height {start} 48 block.packed := by
  simpa only [phase,zero_add] using
    cells_of_lowerColumnsLE columns ({fine}.{side}_cells (prev := prev) (y := y) tube)
end PlasmaLean.Design.{name}
'''
    return name, src, ['cells']


def transfer(a, pack, packet_root, blocks, i):
    fine = json.loads((a.fine_cache/'rows'/f'{i:03}.json').read_text())
    name = f'DommaschkLowerCellsQ0R478{i:03}'
    if (fine['module'],fine['endpoint'],fine['index'],fine['packet_sha256'],fine['archive_sha256']) != (
            name,'q0r478',i,pack['packet_sha256'],pack['action_sha256']):
        raise ValueError('expected a signed native proof of this Q0R478 row')
    paths = list(map(Path,fine['import_paths']))
    admitted(paths[0],name,fine['key'])
    keys = [a.version,pack['key'],fine['key'],digest(DESIGN.parent/'Certificates/WeakenLowerActionCells.trace')]
    overlay=merge_import_roots(a.cell_cache,[packet_root,*paths],keys)
    rows=[]
    for sign in [1,-1]:
        decl=source(i,sign,pack,name)
        base,rec=compile_modules(a.cell_cache/decl[0],[decl],[overlay],keys,a,PACKAGE)
        j=pack['counts'][0]+i if sign==1 else pack['counts'][0]-1-i
        r={k:rec[k] for k in ['module','key','theorems','axioms','wall_seconds','peak_rss_kib']}
        r.update(endpoint='q0r478',index=i,direction=sign,upper=False,height=pack['height'],splits=16,
                 coarse_packet=pack['key'],packet_sha256=pack['packet_sha256'],native=fine['key'],
                 mass=blocks[j][1],expanded_hex=hex(blocks[j][0]),chronological_block=j,
                 import_paths=[str(base),str(overlay)])
        rows.append(r)
        print(decl[0],r['key'],flush=True)
    save(a.cell_cache/'rows'/f'{i:03}.json',rows)
    return rows


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',required=True,type=Path)
    p.add_argument('--rows',required=True,nargs='+',type=int)
    p.add_argument('--fine-cache',type=Path,default=ROOT/'.lake/secondary-lower-action')
    p.add_argument('--cell-cache',type=Path,default=ROOT/'.lake/coarse-secondary-lower')
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    if len(set(a.rows))!=len(a.rows) or any(not 0<=i<327 for i in a.rows):
        p.error('choose distinct valid outward rows')
    env(a)
    pack,root,_,blocks,_,_=packet_inputs(a.packet)
    (a.cell_cache/'rows').mkdir(parents=True,exist_ok=True)
    rows=[]
    for i in a.rows:
        rows.extend(transfer(a,pack,root,blocks,i))
        save(a.output,rows)
