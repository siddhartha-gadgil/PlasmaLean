"""Attach shared field or derivative estimates to the actual signed ribbon packet rows."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from emit_position_slabs import step
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_slopes import GROUPS, RATE, RESULT, load_ribbon
from verify_radial_ribbon_incoming import OUT
from verify_signed_mirror_passage import merge_import_roots


def package(mode):
    return 'RadialRibbon'+('Slope' if mode=='slope' else 'Below')+'RowsCache'


def real(i):
    return f'({i} / 64 : ℝ)'


def signed_rows(mode, tile, traces, packet, group, prefix=None):
    a,b=group['start'],group['stop']
    stop = b if prefix is None else prefix
    n = 332 if prefix is None else prefix
    if not a < stop <= b:
        raise ValueError('the physical prefix must lie in the certified group')
    name=group['module']+f'Tile{tile}Rows'+('' if prefix is None else f'Before{stop:03}')
    original=packet['module']
    p='RadialRibbonPacketCache.'+original
    estimate=group['module']
    estimate_pkg=RESULT if mode=='slope' else OUT
    hs=[f'DommaschkHarmonicBlock{z:02}' for z in range(a//8,(b-1)//8+1)]
    imports=[p,estimate_pkg+'.'+estimate,'PlasmaLean.Design.DommaschkRibbonFirstMirrors',
             *['PlasmaLean.Design.'+v for v in hs]]
    src='module\n'+''.join('public import '+s+'\n' for s in imports)
    src+=f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkRibbonFirstMirrors DommaschkRibbonSlopeCover
open DommaschkGroupedMirrorModels DommaschkSignedMirrorBand DommaschkLowerActionPath
open DommaschkFirstMirrorLaunchSign DommaschkMirrorTubeCrossing
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.all false
'''
    for i in range(a,stop):
        offset=Fraction(2*i+1-a-b,b-a)
        scale=Fraction(1,b-a)
        h=f'(DommaschkHarmonicBlock{i//8:02}.packet {i%8})'
        for lab,short,back,t in [('forward','f','false',traces[1]),('backward','b','true',traces[0])]:
            tag=f'{short}{i:03}'
            src+=f'''
private def {tag} : Step := {step(t['steps'][i])}
private theorem {tag}At : {original}.{lab}Rows[{i}]'(by rw [{original}.{lab}_count]; omega) = {tag} := by
  with_unfolding_all rfl
private theorem {tag}Fits : Covers (i := {i}) {h} {back} {tag} ({offset}) ({scale}) {estimate}.group := by
  constructor <;> kernel_fact
'''
        conclusion = 'Rates' if mode=='slope' else 'Below'
        threshold='derivativeFloor' if mode=='slope' else '(height true)'
        fn='attach (k := derivativeFloor)' if mode=='slope' else 'attach_below (h := (height true : ℝ))'
        src+=f'''
private theorem row{i:03} {{y : ℝ → Plane}} (tr : Tracks {original}.forwardRows {original}.backwardRows {n} y) :
    {conclusion} y {real(i)} {real(i+1)} {threshold} := by
  have f : {i} < {original}.forwardRows.length := by rw [{original}.forward_count]; omega
  have b : {i} < {original}.backwardRows.length := by rw [{original}.backward_count]; omega
  have res := {fn} (i := {i}) tr (by omega) f b
  rw [f{i:03}At, b{i:03}At] at res
'''
        if mode=='slope':
            src+=f'''  have r := res (slope f{i:03}Fits {estimate}.outward) (slope b{i:03}Fits {estimate}.outward)
  convert r using 1 <;> norm_num [derivativeFloor]
'''
        else:
            src+=f'''  have r := res
    (fun _ _ _ ht hx => f{i:03}Fits.below {estimate}.below ht hx)
    (fun _ _ _ ht hx => b{i:03}Fits.below {estimate}.below ht hx)
  convert r using 1 <;> norm_num
'''
    src+=f'''
theorem tracked {{y : ℝ → Plane}} (tr : Tracks {original}.forwardRows {original}.backwardRows {n} y) :
    {conclusion} y {real(a)} {real(stop)} {threshold} := by
'''
    term=f'(row{stop-1:03} tr)'
    for i in reversed(range(a,stop-1)):
        term=f'((row{i:03} tr).append {term})'
    src+=f'  exact {term}\nend PlasmaLean.Design.{name}\n'
    return (name,src,['tracked']),hs


def verify(a,traces,hash_,pkt,g):
    a0,b=g['start'],g['stop']
    if a.mode=='slope':
        if ((tuple(g['tiles']),a0,b) not in GROUPS or Fraction(g['squared_slope'])!=RATE
                or g['module']!=f'DommaschkRibbonSlopeT{g["tiles"][0]}{g["tiles"][1]}R{a0}To{b}'):
            raise ValueError('unexpected upper-height slope group')
    elif g['module']!=f'DommaschkRibbonUpperExclusion{a0:03}To{b:03}' or not 0<=a0<b<=317:
        raise ValueError('unexpected incoming sign group')
    paths=[*map(Path,g['import_paths']),*map(Path,pkt['import_paths'])]
    admitted(paths[0],g['module'],g['key'])
    admitted(Path(pkt['import_paths'][0]),pkt['module'],pkt['key'])
    roots=merge_import_roots(a.cache,paths,[g['key'],pkt['key']])
    item,hs=signed_rows(a.mode,a.tile,traces[a.tile],pkt,g,getattr(a,"short_prefix",None))
    keys=[a.version,hash_,g['key'],pkt['key'],digest(DESIGN/'DommaschkRibbonFirstMirrors.trace'),
          *[digest(DESIGN/(m+'.trace')) for m in hs]]
    root,rec=compile_modules(a.cache/item[0],[item],[roots],keys,a,package(a.mode))
    out={k:rec[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
    out.update(ribbon=hash_,tile=a.tile,start=a0,stop=getattr(a,'short_prefix',None) or b,mode=a.mode,
               tracks=getattr(a,'short_prefix',None) or 332,
               estimate=g['key'],packet=pkt['key'],import_paths=[str(root),str(roots)])
    return out


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mode',choices=['slope','below'],required=True)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--packets',type=Path,required=True)
    p.add_argument('--estimate',type=Path,required=True)
    p.add_argument('--tile',type=int,choices=range(4),required=True)
    p.add_argument('--start',type=int,required=True)
    p.add_argument('--short-prefix',type=int,help='ground a shorter original track ending inside this group')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-ribbon-orientation')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    traces=load_ribbon(a.ribbon)
    hash_=digest(a.ribbon)
    pkt=json.loads(a.packets.read_text())[str(a.tile)]
    estimate=json.loads(a.estimate.read_text())
    if (pkt['ribbon']!=hash_ or estimate['ribbon']!=hash_ or pkt['tile']!=a.tile
            or pkt['module']!='DommaschkRadialRibbonRows'+str(a.tile) or pkt['length']<331):
        p.error('incompatible physical tile archive')
    groups=[r for r in estimate['groups'] if r['start']==a.start and a.tile in r.get('tiles',range(4))]
    if len(groups)!=1:
        p.error('one exact verified group must match this clock and tile')
    g=groups[0]
    env(a)
    out=verify(a,traces,hash_,pkt,g)
    save(a.output,out)
    print(out['module'],out['key'],flush=True)


if __name__=='__main__':
    main()
