"""Quantitative incoming clearance and raised cap signs for four physical QA2R ribbons."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
import json
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_harmonic_group_exclusion import radius_cap
from verify_mirror_endpoint_signs import endpoint_data, gap_proof
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_incoming import OUT
from verify_radial_ribbon_orientation import signed_rows
from verify_radial_ribbon_slopes import cover, load_ribbon
from verify_secondary_mirror_caps import SIGNS
from verify_signed_mirror_passage import merge_import_roots

CLEAR = HEIGHTS[1] - F(1,48000)
UPPER = HEIGHTS[1] + F(1,30000)
EST = 'RadialRibbonBandEstimateCache'
ROWS = 'RadialRibbonBandRowsCache'
CAP = 'RadialRibbonBandCapsCache'


def replay(a, name, src, claims, links, keys, package):
    root, rec = compile_modules(a.cache/name, [(name,src,claims)], links, [a.version, keys], a, package)
    return dict(module=name,key=rec['key'],axioms=rec['axioms'],import_paths=[str(root.resolve()),*[str(p.resolve()) for p in links]])


def group(a, traces, parent, packets, *, clearance=CLEAR, name_prefix='DommaschkRibbonBandBelow', short_track=False):
    old = parent['module']
    lo, hi = parent['start'],parent['stop']
    if old != f'DommaschkRibbonUpperExclusion{lo:03}To{hi:03}':
        raise ValueError('unexpected incoming group')
    base, overlay = map(Path,parent['import_paths'])
    admitted(base,old,parent['key'])
    name = f'{name_prefix}{lo:03}To{hi:03}'
    src = (base/OUT/(old+'.lean')).read_text().replace('namespace PlasmaLean.Design.'+old+'\n',
            'namespace PlasmaLean.Design.'+name+'\n').replace('module\n','module\npublic import PlasmaLean.Design.DommaschkGroupGapRadius\n',1)
    before, final = src.split('  apply physical_sign false hR',1)
    if not final.rstrip().endswith('end PlasmaLean.Design.'+old):
        raise ValueError('unexpected sign projection')
    cap = radius_cap(cover(traces,range(4),lo,hi)[0])
    maximum = F(parent['upper_gap'])
    if maximum + cap**16*(HEIGHTS[1]**2-clearance**2) >= 0:
        raise ValueError('insufficient grouped field margin')
    before = before.replace('theorem below : group.Below (height true)', f'theorem below : group.Below ({clearance})')
    src = before + f'''  have box := enclose (c := ⟨[({cap/2})],({cap/2})⟩) hw hr (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at box bound
  have old : gap R (height true) (atPoint dD R t z) (atPoint dnR R t z) (atPoint dnZ R t z) ≤ ({maximum}) := by
    unfold atPoint
    linarith only [bound.2]
  apply physical_sign false hR (by norm_num)
  exact DommaschkGroupGapRadius.at_lower (radius := ({cap})) hR.le (by linarith only [box.2])
    (by norm_num [height]) old (by norm_num [height])
end PlasmaLean.Design.{name}
'''
    est = replay(a,name,src,['below'],[overlay],[a.ribbon_key,parent['key'],digest(DESIGN/'DommaschkGroupGapRadius.trace')],EST)
    physical = []
    for k,pkt in enumerate(packets):
        links = [*map(Path,est['import_paths']),*map(Path,pkt['import_paths'])]
        key = [est['key'],pkt['key']]
        joins = merge_import_roots(a.cache,links,key)
        item, hs = signed_rows('below',k,traces[k],pkt,dict(start=lo,stop=hi,module=name),
                               prefix=hi if short_track else None)
        n,code,claims = item
        code = code.replace(OUT+'.'+name,EST+'.'+name).replace('(height true : ℝ)',f'({clearance} : ℝ)').replace('(height true)',f'({clearance})')
        row = replay(a,n,code,claims,[joins],[a.ribbon_key,key,digest(DESIGN/'DommaschkRibbonFirstMirrors.trace'),
                     *[digest(DESIGN/(h+'.trace')) for h in hs]],ROWS)
        physical.append(row)
    print(name,est['key'],flush=True)
    return dict(start=lo,stop=hi,maximum=str(maximum),radius=str(cap),estimate=est,tiles=physical)


def raised_cap(a, traces, parent, k):
    old = f'DommaschkRadialRibbon{k}MirrorUpper330Right'
    key = parent['tiles'][old]
    overlay = Path(parent['import_paths'][1])
    base = (overlay/SIGNS/(old+'.olean')).resolve(strict=True).parents[1]
    admitted(base,old,key)
    src = (base/SIGNS/(old+'.lean')).read_text()
    name = f'DommaschkRadialRibbonBandCap{k}'
    head,body = src.split('private def model_h : Model',1)
    _,point = body.split('/-- True field-strength sign',1)
    rad,cols = endpoint_data(330,True,traces[k])
    models = gap_proof(True,True,UPPER,rad,cols)
    adjusted = (models+'/-- True field-strength sign'+point).replace('DommaschkFirstMirrorLaunchSign.height true',f'({UPPER} : ℚ)')
    src = (head.replace('namespace PlasmaLean.Design.'+old,'namespace PlasmaLean.Design.'+name+'\nopen '+old)
           + adjusted.replace('end PlasmaLean.Design.'+old,'end PlasmaLean.Design.'+name))
    result = replay(a,name,src,['fwd_tube_sign','back_tube_sign'],[overlay],[a.ribbon_key,key],CAP)
    print(name,result['key'],flush=True)
    return result


def finish(a, orientation, out):
    family = orientation['module']
    if family != 'DommaschkRadialRibbonNoGrazingFamily':
        raise ValueError('wrong N181 selector for the original rows')
    base_import = 'RadialRibbonNoGrazingFamilyCache.' + family
    prelude = '''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.NAME
open Set Certificates.PositionFrameSlabs DommaschkNativeWellAction
open DommaschkLowerActionPath (Tracks)
open DommaschkRadialFamilyContinuity DommaschkRibbonFirstMirrors DommaschkRadialMirrorHeightBand
open DommaschkMirrorTubeCrossing DommaschkMirrorLaunch DommaschkRadialRibbonEntry
open DommaschkKamC KamNewton Theory.KAM WEll1Z2 Contract Forms Fields.VacuumBoozer
set_option linter.all false
set_option maxRecDepth 65536
'''
    def compile_family(name, imports, body, claims, parents, package):
        keys = [p['key'] for p in parents]
        roots = [Path(link) for p in parents for link in p['import_paths']]
        overlay = merge_import_roots(a.cache,roots,keys)
        head = 'module\npublic import PlasmaLean.Design.DommaschkRadialMirrorHeightBand\n'
        head += ''.join('public import '+s+'\n' for s in imports)
        src = head + prelude.replace('NAME',name) + body + '\nend PlasmaLean.Design.'+name+'\n'
        return replay(a,name,src,claims,[overlay],
                      [a.ribbon_key,keys,digest(DESIGN/'DommaschkRadialMirrorHeightBand.trace')],package)
    tiles=[]
    for k,cap in enumerate(out['caps']):
        flat=[g['tiles'][k] for g in out['groups']]
        rows=f'DommaschkRadialRibbonRows{k}'
        name=f'DommaschkRadialRibbonMirrorBandTile{k}'
        early=f'({flat[-1]["module"]}.tracked tr)'
        for g in reversed(flat[:-1]):
            early=f'(({g["module"]}.tracked tr).append {early})'
        body=f'''
theorem early {{y : ℝ → Plane}} (tr : Tracks {rows}.forwardRows {rows}.backwardRows 332 y) :
    Below y 0 lowerClock clearance := by
  have raw := {early}
  convert raw using 1 <;> norm_num [lowerClock,clearance,level]

theorem cap_signs {{y : ℝ → Plane}} (tr : Tracks {rows}.forwardRows {rows}.backwardRows 332 y) :
    upper < field y (-capClock) ∧ upper < field y capClock := by
  constructor
'''
        for short,direction,proj in [('back','backward',2),('fwd','forward',1)]:
            body+=f'''  · have idx : 330 < {rows}.{direction}Rows.length := by rw [{rows}.{direction}_count]; omega
    obtain ⟨prev,traces⟩ := tr.{proj} 330 (by omega) idx
    have point := traces capClock (by norm_num [capClock])
    have eq : {rows}.{direction}Rows[330]'idx = {cap['module']}.{short}Row := by with_unfolding_all rfl
    rw [eq] at point
    have sign := {cap['module']}.{short}_tube_sign point
    norm_num [DommaschkMirrorEndpointSign.oriented] at sign
    convert sign using 1 <;> norm_num [upper,level,field,capClock]
'''
        body+=f'''
theorem on_tubes {{y : ℝ → Plane}} (e : Enclosed y (-capClock) capClock)
    (tr : Tracks {rows}.forwardRows {rows}.backwardRows 332 y) : Verified y :=
  verified e (early tr) (cap_signs tr) (DommaschkRadialRibbonNoGrazing{k}.rates tr)
'''
        record=compile_family(name,[base_import,CAP+'.'+cap['module'],
                              *[ROWS+'.'+g['module'] for g in flat]],body,['early','cap_signs','on_tubes'],
                              [orientation,cap,*flat],'RadialRibbonHeightBandTileCache')
        tiles.append(record)
        print(name,record['key'],flush=True)
    name='DommaschkRadialRibbonMirrorBand'
    body=f'''
open {family} (forwardRows backwardRows)
theorem on_tubes (k : Fin 4) {{y : ℝ → Plane}} (e : Enclosed y (-capClock) capClock)
    (tr : Tracks (forwardRows k) (backwardRows k) 332 y) : Verified y := by
  fin_cases k
'''
    for tile in tiles:
        body+=f'  · exact {tile["module"]}.on_tubes e tr\n'
    body+='''
/-- The precise remaining trajectory certificate for this geometric launch rectangle. -/
def Through : Prop := ∀ (k : Fin 4) (x : Plane), x ∈ stateSet (seed k) →
  ∃ y : ℝ → Plane, y 0 = x ∧ Enclosed y (-capClock) capClock ∧
    Tracks (forwardRows k) (backwardRows k) 332 y

theorem from_entry {uC zC uA zA : FA} {u φ : ℝ} {k : Fin 4} (small : |φ| ≤ 1 / 2 ^ 19)
    (entry : Passage uC zC uA zA u φ k) (full : Through) :
    ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
      Enclosed y (-capClock) capClock ∧ Verified y := by
  apply DommaschkRadialSectionAction.from_section small entry
  intro j x hx
  obtain ⟨y,atZero,e,tr⟩ := full j x hx
  exact ⟨y,atZero,e,on_tubes j e tr⟩

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      (Through → ∀ u ∈ Icc (47/100:ℝ) (239/500), ∀ φ : ℝ, |φ| ≤ 1/2^19 →
        ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
          Enclosed y (-capClock) capClock ∧ Verified y) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,entries⟩ := DommaschkRadialRibbonEntry.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,?_⟩
  intro full u hu φ small
  obtain ⟨k,_,entry⟩ := entries u hu φ small
  exact from_entry small entry full
'''
    final=compile_family(name,[base_import,*['RadialRibbonHeightBandTileCache.'+t['module'] for t in tiles]],
                         body,['on_tubes','from_entry','from_nested_tori'],[orientation,*tiles],
                         'RadialRibbonHeightBandFamilyCache')
    out.update(final,tiles=tiles,orientation=orientation['key'],height_lower=str(HEIGHTS[1]-F(1,50000)),
               signed_incoming_rows=8*317,signed_slope_rows=8*14,signed_end_caps=8,
               clock_lipschitz=34740,physical_flight_time=[14,10000])
    save(a.output,out)
    print(name,final['key'],flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--incoming',type=Path,required=True)
    p.add_argument('--caps',type=Path,required=True)
    p.add_argument('--packets',type=Path,required=True)
    p.add_argument('--orientation',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-ribbon-height-band')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--workers',type=int,choices=(1,2),default=1)
    a=p.parse_args()
    env(a)
    a.ribbon_key=digest(a.ribbon)
    traces=load_ribbon(a.ribbon)
    incoming,caps,packets,orientation=[json.loads(p.read_text()) for p in (a.incoming,a.caps,a.packets,a.orientation)]
    packets=[packets[str(k)] for k in range(4)]
    for q in [incoming,caps,orientation,*packets]:
        if q['ribbon'] != a.ribbon_key:
            raise ValueError('ribbon checksum differs')
    for k,pkt in enumerate(packets):
        if pkt['tile']!=k or pkt['module']!=f'DommaschkRadialRibbonRows{k}':
            raise ValueError('unexpected packet tile')
    for q in [caps,orientation,*packets]:
        admitted(Path(q['import_paths'][0]),q['module'],q['key'])
    groups=sorted(incoming['groups'],key=lambda g:g['start'])
    if [g['start'] for g in groups] != [0,*[g['stop'] for g in groups[:-1]]] or groups[-1]['stop']!=317:
        raise ValueError('expected complete incoming cover')
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        cap_jobs=[pool.submit(raised_cap,a,traces,caps,k) for k in range(4)]
        group_jobs=[pool.submit(group,a,traces,g,packets) for g in groups]
        out=dict(ribbon=a.ribbon_key,clearance=str(CLEAR),upper=str(UPPER),caps=[j.result() for j in cap_jobs],groups=[])
        for j in group_jobs:
            out['groups'].append(j.result())
            save(a.output.with_suffix('.progress.json'),out)
    finish(a,orientation,out)


if __name__=='__main__':
    main()
