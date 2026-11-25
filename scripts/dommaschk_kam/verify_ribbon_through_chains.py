"""Compile original signed radius-row chains, then retain the section state and interior cap derivatives."""
import argparse
import json
from pathlib import Path
import time

from ribbon_central_data import LENGTH,WITNESS_SHA,label
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_radial_ribbon_packets import PACKAGE as PACKETS
from verify_ribbon_physical_group import PACKAGE as PHYSICAL,archived
from verify_signed_mirror_passage import merge_import_roots

PACKAGE='RadialRibbonThroughCache'
TILE_PACKAGE='RadialRibbonThroughTileCache'
FAMILY_PACKAGE='RadialRibbonThroughFamilyCache'
STATIC='DommaschkRibbonThroughChains'


def head(name,imports):
    return ('module\n'+''.join('public import '+m+'\n' for m in dict.fromkeys(imports))+
            '\n@[expose] public section\nnoncomputable section\nnamespace PlasmaLean.Design.'+name+
            '\nopen Certificates.PositionFrameSlabs DommaschkRibbonThroughChains DommaschkJacobian'+
            '\nopen DommaschkLowerActionPath DommaschkRadialFamilyContinuity DommaschkSignedTraceDomain'+
            '\nset_option linter.all false\nset_option maxRecDepth 16000\nset_option maxHeartbeats 0\n')


def segment(k,a,b,packet,parents):
    name=f'DommaschkRibbon{k}Segment{a:03}To{b:03}'
    src=head(name,['PlasmaLean.Design.'+STATIC,PACKETS+'.'+packet,*[PHYSICAL+'.'+r['module'] for r in parents]])
    for sign,tag,d,rate in [(1,'forward','Forward','1'),(-1,'backward','Back','(-1)')]:
        mods=[f'DommaschkPhysical{label(k).upper()}{d}{i:03}' for i in range(a,b)]
        prev=packet+'.seed' if a==0 else 'next ('+archived(packet,sign,a-1)+')'
        src+=f'def {tag}Rows : List Step := ['+', '.join(m+'.row' for m in mods)+']\n'
        src+=f'theorem {tag} : Steps (euclideanFlow 0 {rate}) {a} ({prev}) {b} (next {mods[-1]}.row) {tag}Rows := by\n'
        src+=f'  unfold {tag}Rows\n'
        for i,m in enumerate(mods,a):
            src+=f'  refine Steps.cons (r := {m}.row) ?_ ?_\n'
            src+=f'  · change Fields.TrajectorySlabs.Step _ (physicalSlab _ _ (({i}:ℕ)/64)) _ _\n'
            src+=f'    rw [show (({i}:ℕ):ℝ)/64 = {i}/64 by norm_num]\n    exact {m}.physical_step\n'
        src+='  exact Steps.nil _ _\n'
    return name,src+'end PlasmaLean.Design.'+name+'\n',['forward','backward']


def endpoint(k,n,packet,segments):
    name=f'DommaschkRibbon{k}Through{n:03}'
    src=head(name,['PlasmaLean.Design.'+STATIC,PACKETS+'.'+packet,*[PACKAGE+'.'+m for m in segments]])
    for sign,tag,rate in [(1,'forward','1'),(-1,'backward','(-1)')]:
        expr=segments[0]+'.'+tag
        for m in segments[1:]:
            expr=f'({expr}).append {m}.{tag}'
        src+=f'''theorem {tag}_steps : Steps (euclideanFlow 0 {rate}) 0 {packet}.seed {n}
    (next ({archived(packet,sign,n-1)})) ({packet}.{tag}Rows.take {n}) := by
  with_unfolding_all exact {expr}
private theorem {tag}_region : ({packet}.{tag}Rows.take {n}).all packed = true := by
  with_unfolding_all rfl
'''
    src+=f'''theorem from_seed (x : Plane) (hx : x ∈ stateSet {packet}.seed) :
    ∃ y, y 0 = x ∧ Enclosed y (-({n-1}/64)) ({n-1}/64) ∧
      Tracks {packet}.forwardRows {packet}.backwardRows {n} y := by
  apply from_chains (s := {packet}.seed) (by norm_num) (by norm_num)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) forward_region backward_region
      (by simpa only [Nat.cast_zero, zero_div] using forward_steps.chain)
      (by simpa only [Nat.cast_zero, zero_div] using backward_steps.chain) hx
end PlasmaLean.Design.{name}
'''
    return name,src,['forward_steps','backward_steps','from_seed']


def combined(n,per_tile,packets):
    name='DommaschkRadialRibbonThrough'+('' if n==LENGTH else f'{n:03}')
    src=head(name,[TILE_PACKAGE+'.'+m for m in per_tile])
    for tag,d in [('allForward','forward'),('allBackward','backward')]:
        src+=f'def {tag} (k : Fin 4) : List Step :=\n  match k with\n'
        src+=''.join(f'  | {j if j<3 else "_"} => {p}.{d}Rows\n' for j,p in enumerate(packets))
    src+=f'''theorem from_seed (k : Fin 4) (x : Plane) (hx : x ∈ stateSet (DommaschkRadialRibbonEntry.seed k)) :
    ∃ y, y 0 = x ∧ Enclosed y (-({n-1}/64)) ({n-1}/64) ∧ Tracks (allForward k) (allBackward k) {n} y := by
  fin_cases k
'''
    src+=''.join(f'  · exact {m}.from_seed x hx\n' for m in per_tile)
    return name,src+'end PlasmaLean.Design.'+name+'\n',['from_seed']


def regions(n,packets):
    name=f'DommaschkRibbonTubeRegions{n:03}'
    src=head(name,['PlasmaLean.Design.'+STATIC,*[PACKETS+'.'+m for m in packets]])
    claims=[]
    for k,pn in enumerate(packets):
        for tag in ('forward','backward'):
            claim=f'{tag}{k}'
            claims.append(claim)
            src+=f'''private theorem {claim}_packed : ({pn}.{tag}Rows.take {n}).all packed = true := by
  with_unfolding_all rfl
theorem {claim} {{i : ℕ}} (hi : i < {n}) (hr : i < {pn}.{tag}Rows.length)
    {{prev : State}} {{t : ℝ}} {{x : Plane}} (ht : t ∈ Set.Icc ((i : ℝ) / 64) ((i : ℝ) / 64 + 1 / 64))
    (hx : x ∈ (physicalSlab prev {pn}.{tag}Rows[i] (i / 64)).tube t) : Region x := by
  apply region_of_mem _ ht hx
  have mem := List.getElem_mem (l := {pn}.{tag}Rows.take {n}) (n := i) (by simpa using lt_min hi hr)
  simpa only [List.getElem_take] using List.all_eq_true.mp {claim}_packed _ mem
'''
    return name,src+'end PlasmaLean.Design.'+name+'\n',claims


def build_package(a,term,keys,roots,package=PACKAGE):
    deps=list(dict.fromkeys(keys))
    paths=list(dict.fromkeys(map(Path,roots)))
    links=merge_import_roots(a.cache,paths,deps)
    root,r=compile_modules(a.cache/term[0],[term],[links],
        [package,WITNESS_SHA,a.version,digest(DESIGN/(STATIC+'.trace')),deps],a,package)
    return r['key'],root,links


def checked_segment(a,k,start,stop,packet,checked):
    parents={}
    for i in range(start,stop):
        row=json.loads((a.physical/f'tile{k}'/'steps'/f'{i:03}.json').read_text())
        rr=Path(row['import_paths'][0])
        rkey=(rr,row['module'],row['key'])
        if rkey not in checked:
            checked[rkey]=set(admitted(*rkey)['theorems'])
        if row['tile']!=k or row['packet_sha256']!=WITNESS_SHA or any(
                f'PlasmaLean.Design.DommaschkPhysical{label(k).upper()}{d}{i:03}.physical_step'
                not in checked[rkey] for d in ('Forward','Back')):
            raise ValueError(f'unmatched original signed step {k},{i}')
        parents[row['key']]=row
    term=segment(k,start,stop,packet['module'],parents.values())
    pr,=map(Path,packet['import_paths'])
    key,root,links=build_package(a,term,[packet['key'],*parents],
                                [pr,*[s for r in parents.values() for s in r['import_paths']]])
    return term[0],key,root,links


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packets',required=True,type=Path)
    p.add_argument('--count',type=int,default=LENGTH)
    p.add_argument('--regions-only',action='store_true')
    p.add_argument('--wait',action='store_true',help='wait for every required signed physical receipt')
    p.add_argument('--physical',type=Path,default=ROOT/'.lake/ribbon-physical-campaign')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/ribbon-through-checks')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 1<a.count<=LENGTH:
        p.error('choose an outer row past the closed interior cap')
    if a.wait and not a.regions_only:
        paths=[a.physical/f'tile{k}'/'steps'/f'{i:03}.json' for k in range(4) for i in range(a.count)]
        while not all(p.exists() for p in paths):
            time.sleep(15)
    env(a)
    n=a.count
    packets=json.loads(a.packets.read_text())
    produced=[]
    all_keys=[]
    all_roots=[]
    checked={}
    for k in range(4):
        packet=packets[str(k)]
        pn=packet['module']
        pr,=map(Path,packet['import_paths'])
        if (pn,packet['ribbon'],packet['tile'])!=(f'DommaschkRadialRibbonRows{k}',WITNESS_SHA,k):
            raise ValueError(f'wrong physical records for ribbon {k}')
        admitted(pr,pn,packet['key'])
        if a.regions_only:
            all_roots.append(pr)
            all_keys.append(packet['key'])
            continue
        mods,keys,roots=[],[packet['key']],[pr]
        for start in range(0,n,8):
            stop=min(start+8,n)
            module,key,rr,overlay=checked_segment(a,k,start,stop,packet,checked)
            keys.append(key)
            roots.extend([rr,overlay])
            mods.append(module)
        term=endpoint(k,n,pn,mods)
        key,root,links=build_package(a,term,keys,roots,TILE_PACKAGE)
        produced.append(term[0])
        all_keys.append(key)
        all_roots.extend([root,links])
        print(f'{term[0]} {key}',flush=True)
    names=[packets[str(k)]['module'] for k in range(4)]
    term=regions(n,names) if a.regions_only else combined(n,produced,names)
    key,root,links=build_package(a,term,all_keys,all_roots,FAMILY_PACKAGE)
    rec=admitted(root,term[0],key)
    result={k:v for k,v in rec.items() if k!='artifacts'}
    result.update(packet_sha256=WITNESS_SHA,package=FAMILY_PACKAGE,outer_rows=n,cap=f'{n-1}/64',tile_keys=all_keys,
        import_paths=list(map(str,[root,links])))
    save(a.output,result)
    print(f'{term[0]} {key}',flush=True)


if __name__=='__main__':
    main()
