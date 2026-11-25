"""Verify signed row coverage and compose the physical no-grazing theorem per radial tile."""
import argparse
import json
from pathlib import Path
from types import SimpleNamespace
import time

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_orientation import package, real, verify
from verify_radial_ribbon_slopes import load_ribbon
from verify_signed_mirror_passage import merge_import_roots


def contiguous(items,a,b):
    i=a
    for item in sorted(items,key=lambda r:r['start']):
        if item['start']!=i:
            return False
        i=item['stop']
    return i==b


def compose_tile(a,hash_,pkt,signs,rates,cap):
    k=pkt['tile']
    if not contiguous(signs,0,317) or not contiguous(rates,317,331):
        raise ValueError('both complete intervals are required')
    signs=sorted(signs,key=lambda r:r['start'])
    rates=sorted(rates,key=lambda r:r['start'])
    rows=signs+rates
    parents=[*rows,pkt,cap]
    paths=[]
    for parent in parents:
        root,*extra=map(Path,parent['import_paths'])
        admitted(root,parent['module'],parent['key'])
        paths.extend([root,*extra])
    parent_keys=[r['key'] for r in parents]
    overlay=merge_import_roots(a.cache,paths,parent_keys)
    original=pkt['module']
    name='DommaschkRadialRibbonNoGrazing'+str(k)
    imports=['PlasmaLean.Design.DommaschkRibbonFirstMirrors','PlasmaLean.Design.DommaschkRadialFamilyContinuity',
             'RadialRibbonPacketCache.'+original,'RadialRibbonCapCache.'+cap['module'],
             *[package(r['mode'])+'.'+r['module'] for r in rows]]
    src='module\n'+''.join('public import '+m+'\n' for m in imports)+f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkLowerActionPath DommaschkFirstMirrorLaunchSign
open DommaschkSignedMirrorBand DommaschkRibbonFirstMirrors DommaschkMirrorTubeCrossing
open DommaschkRadialFamilyContinuity
set_option maxRecDepth 65536
set_option linter.all false
'''
    for label,cover,ty,lo,hi,extra in [('early',signs,'Below',0,317,'(height true)'),
                                      ('rates',rates,'Rates',317,331,'derivativeFloor')]:
        term=f'({cover[-1]["module"]}.tracked tr)'
        for r in reversed(cover[:-1]):
            term=f'(({r["module"]}.tracked tr).append {term})'
        src+=f'''
theorem {label} {{y : ℝ → Plane}} (tr : Tracks {original}.forwardRows {original}.backwardRows 332 y) :
    {ty} y {real(lo)} {real(hi)} {extra} := {term}
'''
    src+=f'''
theorem on_original_tubes {{y : ℝ → Plane}} (closed : Enclosed y (-capClock) capClock)
    (tr : Tracks {original}.forwardRows {original}.backwardRows 332 y) : NoGrazing y := by
  apply no_grazing (fun t ht => (closed.ode t ht).hasDerivWithinAt)
    (fun t ht => lt_of_lt_of_le (by norm_num : (0:ℝ) < 7/8) (closed.region t ht).1.1)
    (Below.signed (by simpa only [Nat.cast_zero,zero_div] using early tr)) _ _ (rates tr)
'''
    for i,(flag,direction) in enumerate([('false','forward'),('true','backward')]):
        clock='(-capClock)' if i else 'capClock'
        src+=f'''  · have hj : 330 < {original}.{direction}Rows.length := by rw [{original}.{direction}_count]; omega
    obtain ⟨prev,h⟩ := tr.{i+1} 330 (by omega) hj
    have x := h capClock (by norm_num [capClock])
    have row : {original}.{direction}Rows[330]'hj = {cap['module']}.row {flag} {k} := by with_unfolding_all rfl
    rw [row] at x
    exact {cap['module']}.above {k} {flag} x
'''
    src+=f'end PlasmaLean.Design.{name}\n'
    root,rec=compile_modules(a.cache/name,[(name,src,['early','rates','on_original_tubes'])],[overlay],
                             [a.version,hash_,parent_keys,digest(DESIGN/'DommaschkRadialFamilyContinuity.trace')],
                             a,'RadialRibbonNoGrazingCache')
    out={k:rec[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
    out.update(tile=k,ribbon=hash_,parents=parent_keys,import_paths=[str(root),str(overlay)])
    return out


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--packets',type=Path,required=True)
    p.add_argument('--caps',type=Path,required=True)
    p.add_argument('--below',type=Path,nargs='+',required=True)
    p.add_argument('--slopes',type=Path,nargs='+',required=True)
    p.add_argument('--tiles',type=int,nargs='+',choices=range(4),default=list(range(4)))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-ribbon-orientation')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--wait',action='store_true')
    a=p.parse_args()
    traces=load_ribbon(a.ribbon)
    hash_=digest(a.ribbon)
    packets=json.loads(a.packets.read_text())
    tiles=sorted(set(a.tiles))
    if len(tiles)!=len(a.tiles):
        p.error('choose distinct tile indices')
    for tile in tiles:
        pkt=packets[str(tile)]
        if pkt['ribbon']!=hash_ or pkt['module']!='DommaschkRadialRibbonRows'+str(tile) or pkt['length']<331:
            p.error('wrong canonical packet')
    env(a)
    done={k:{} for k in tiles}
    physical={}
    def report():
        save(a.output,{'ribbon':hash_,'tiles':{str(k):{'rows':list(done[k].values()),
             **({'physical':physical[k]} if k in physical else {})} for k in tiles}})
    while True:
        for mode,paths in [('slope',a.slopes),('below',a.below)]:
            for path in paths:
                if not path.exists():
                    continue
                manifest=json.loads(path.read_text())
                if manifest['ribbon']!=hash_:
                    raise ValueError('estimates describe another packet')
                for g in manifest['groups']:
                    key=(mode,g['start'])
                    for k in tiles:
                        if k not in g.get('tiles',range(4)) or key in done[k]:
                            continue
                        args=SimpleNamespace(**vars(a),mode=mode,tile=k)
                        result=verify(args,traces,hash_,packets[str(k)],g)
                        done[k][key]=result
                        report()
                        print('accepted',result['module'],result['key'],flush=True)
        for k in tiles:
            if k in physical:
                continue
            s=[r for (m,_),r in done[k].items() if m=='slope']
            e=[r for (m,_),r in done[k].items() if m=='below']
            if contiguous(s,317,331) and contiguous(e,0,317) and a.caps.exists():
                cap=json.loads(a.caps.read_text())
                if (cap['ribbon'],cap['time'],cap['module'])!=(hash_,'331/64','DommaschkRadialRibbonUpperCaps'):
                    raise ValueError('wrong archive or exterior time in cap proof')
                physical[k]=compose_tile(a,hash_,packets[str(k)],e,s,cap)
                report()
                print('complete',physical[k]['module'],physical[k]['key'],flush=True)
        if not a.wait or len(physical)==len(tiles):
            return
        time.sleep(20)


if __name__=='__main__':
    main()
