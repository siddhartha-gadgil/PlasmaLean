"""Ground selected central opposite-section action panels on the genuine singleton tubes."""
import argparse
import json
from pathlib import Path

from bounce_common_section import section_polynomial_data
from bounce_mirror_pilot import HEIGHTS
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import panel_row, slab_witness
from replay_physical_action_archive import segment
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env, section_data, verify_packet
from verify_coarse_physical_action import PACKAGE, TICKS, cell, tick_modules
from verify_mirror_physical_hit import admitted
from verify_opposite_action_subwell import CUT, NAME, PACKAGE as ARCHIVE, load
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',required=True,type=Path)
    p.add_argument('--core',required=True,type=Path)
    p.add_argument('--rows',type=int,nargs='+',required=True)
    p.add_argument('--directions',type=int,nargs='+',choices=(-1,1),default=(-1,1))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-action-models')
    p.add_argument('--cell-cache',type=Path,default=ROOT/'.lake/opposite-action-inner-rows')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    env(a)
    packet=load(a.packet)
    key=digest(a.packet)
    pack=json.loads(a.core.read_text())
    if ((pack['packet_sha256'],pack['package'],pack['module'],pack['counts'],pack['upper'])!=
            (key,ARCHIVE,NAME,[CUT,CUT],False) or any(not 0<=i<CUT for i in a.rows)):
        p.error('expected the original positive-speed central singleton archive and a covered row')
    base=Path(pack['import_paths'][0])
    admitted(base,NAME,pack['key'])
    field,static=section_data(a,1)
    model_inputs=False,HEIGHTS[1],pack['counts'],[],packet['traces'],key,pack['key']
    exact=section_polynomial_data(1)
    shifted=ShiftedStrength(exact)
    m=pack['splits']
    results=[]
    for i in a.rows:
        for sign in a.directions:
            model,nums=verify_packet(a,'q1r470',i,sign,field,static,model_inputs)
            trace=packet['traces'][int(sign==1)]
            word,mass=panel_row(segment(trace,i),exact,shifted,HEIGHTS[1],False,m)
            flat=int(slab_witness(word,mass,False,m).split('0x',1)[1].split(',',1)[0],16)
            atom=model['module'].replace('CoarseModel','CoarseTicks')+f'N{m}'
            deps=[a.version,key,pack['key'],digest(DESIGN.parent/'Certificates/CoarseActionCells.trace')]
            tb,tr=compile_modules(a.cell_cache/atom,tick_modules(atom,nums,HEIGHTS[1],False,m,word,sign<0),
                                 [],deps,a,TICKS)
            keys=[*deps,model['key'],tr['key']]
            overlay=merge_import_roots(a.cell_cache,[base,tb,*map(Path,model['import_paths'])],keys)
            item=cell('q1r470',i,sign,pack,model['module'],atom,flat,mass)
            root,rec=compile_modules(a.cell_cache/item[0],[item],[overlay],keys,a,PACKAGE)
            new={k:rec[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')}
            new.update(index=i,direction=sign,model=model['key'],ticks=tr['key'],
                       import_paths=[str(root),str(overlay)])
            results.append(new)
            save(a.output,dict(packet_sha256=key,core=pack['key'],signed_rows=results))
            print(i,sign,item[0],rec['key'],flush=True)


if __name__=='__main__':
    main()
