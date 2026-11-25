"""Join complete original ODE and action rows onto one signed q1r470 field trajectory."""
import argparse
import json
from pathlib import Path

from emit_position_slabs import step
from run_opposite_inner_action_campaign import entries
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_physical_action import PACKAGE as PANELS
from verify_endpoint_signed_prefix import PACKAGE as ODE
from verify_mirror_physical_hit import admitted
from verify_opposite_action_subwell import CUT, NAME, PACKAGE as CORE, load
from verify_opposite_inner_ode_group import CHECKSUM
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


PACK='OppositeInnerPacketCache'
GROUP='OppositeInnerSegmentCache'
TOP='OppositeInnerThroughCache'
THEORY='DommaschkOppositeInnerTrajectory'


def header(name,imports):
    return 'module\n'+''.join('public import '+s+'\n' for s in dict.fromkeys(imports))+f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature
open DommaschkOppositeInnerTrajectory DommaschkRibbonThroughChains DommaschkLowerActionPath
open DommaschkOppositeInnerSeed DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel
open DommaschkJacobian (euclideanFlow)
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
'''


def packet_source(n,packet):
    name=f'DommaschkOppositeInnerRows{n:03}'
    src=header(name,['PlasmaLean.Design.'+THEORY])
    for trace in packet['traces']:
        d='forward' if trace['direction']==1 else 'backward'
        groups=[]
        for i in range(0,n,16):
            base=d+str(i)
            groups.append(base)
            src+='def '+base+' : List Step := ['+',\n'.join(step(r) for r in trace['steps'][i:min(i+16,n)])+']\n'
        src+=f'def {d} : List Step := '+' ++ '.join(groups)+'\n'
        src+=f'theorem {d}_length : {d}.length = {n} := by with_unfolding_all rfl\n'
    return name,src+'end PlasmaLean.Design.'+name+'\n',[]


def angle_functions():
    return '(fun t => arcDensity (y t 0) (phase+t) (y t 1)) (fun t => strength (phase+t) (y t))'


def segment(pn,n,a,b,rows,panels):
    name=f'DommaschkOppositeInnerSegment{a:03}To{b:03}At{n:03}'
    imports=[PACK+'.'+pn,CORE+'.'+NAME]
    for i in range(a,b):
        for s in (1,-1):
            imports.extend([ODE+'.'+rows[i,s]['module'],PANELS+'.'+panels[i,s]['module']])
    src=header(name,imports)
    for s,branch,vel,side in [(1,'forward','1','.1'),(-1,'backward','(-1)','.2')]:
        mods=[rows[i,s]['module'] for i in range(a,b)]
        src+=f'def {branch}Rows : List Step := ['+', '.join(m+'.row' for m in mods)+']\n'
        src+=f'theorem {branch}_steps : Steps (euclideanFlow phase {vel}) {a} {mods[0]}.previous {b} (next {mods[-1]}.row) {branch}Rows := by\n  unfold {branch}Rows\n'
        for i,m in enumerate(mods,a):
            src+=f'  refine Steps.cons (r := {m}.row) ?_ ?_\n  · change Fields.TrajectorySlabs.Step _ (physicalSlab _ _ (({i}:ℕ)/64)) _ _\n    rw [show (({i}:ℕ):ℝ)/64 = {i}/64 by norm_num]\n    exact {m}.physical_step\n'
        src+='  exact Steps.nil _ _\n'
        indices=list(range(a,b)) if s==1 else list(range(b-1,a-1,-1))
        src+=f'def {branch}Blocks : List (Block false) := ['+', '.join(panels[i,s]['module']+'.block' for i in indices)+']\n'
        start=a if s==1 else -b
        src+=f'''theorem {branch}_cells (y : ℝ → Plane) (track : Tracks {pn}.forward {pn}.backward {n} y) :
    Covers false {angle_functions()} DommaschkNativeWellAction.level ({start}/64) {branch}Blocks := by
  unfold {branch}Blocks
'''
        for j,i in enumerate(indices):
            m=panels[i,s]['module']
            src+=f'''  obtain ⟨prev{i},mem{i}⟩ := track{side} {i} (by norm_num) (by rw [{pn}.{branch}_length]; norm_num)
  have row{i} : {pn}.{branch}[{i}]'(by rw [{pn}.{branch}_length]; norm_num) = {m}.row := by with_unfolding_all rfl
  rw [row{i},show (({i}:ℕ):ℝ)/64 = {i}/64 by norm_num] at mem{i}
  have c{i} := {m}.cells (y := y) (prev := prev{i}) (by
    intro t ht
    have time : t ∈ Icc ({i}/64:ℝ) (((({i}:ℕ):ℝ)+1)/64) := by convert ht using 1 <;> norm_num
    simpa only [Bool.false_eq_true,↓reduceIte] using mem{i} t time)
  refine ⟨?_,?_⟩
  · convert c{i} using 1 <;> norm_num [phase,{m}.phase,{m}.height,DommaschkNativeWellAction.level]
'''
        src+='  trivial\n'
    claims=[d+'_'+t for d in ('forward','backward') for t in ('steps','cells')]
    return name,src+'end PlasmaLean.Design.'+name+'\n',claims


def aggregate(n,pn,segments):
    name=f'DommaschkOppositeInnerThrough{n:03}'
    src=header(name,[CORE+'.'+NAME,PACK+'.'+pn,*[GROUP+'.'+m for _,_,m in segments]])
    for d,rate in [('forward','1'),('backward','(-1)')]:
        expr=segments[0][2]+'.'+d+'_steps'
        for _,_,m in segments[1:]:
            expr=f'({expr}).append {m}.{d}_steps'
        src+=f'''theorem {d}_steps : Steps (euclideanFlow phase {rate}) 0 seed {n}
    (next ({pn}.{d}[{n-1}]'(by rw [{pn}.{d}_length]; norm_num))) {pn}.{d} := by
  with_unfolding_all exact {expr}
'''
    groups=[(-b,-a,m+'.backward') for a,b,m in reversed(segments)]+[(a,b,m+'.forward') for a,b,m in segments]
    src+=f'def blocks := ({NAME}.slabs.drop {CUT-n}).take {2*n}\n'
    src+='theorem physical_cells (y : ℝ → Plane) (track : Tracks '+pn+'.forward '+pn+f'.backward {n} y) :\n    Covers false {angle_functions()} DommaschkNativeWellAction.level (-{n}/64) blocks := by\n'
    src+='  rw [show blocks = '+' ++ '.join(m+'Blocks' for _,_,m in groups)+' by with_unfolding_all rfl]\n'
    for a,b,m in groups[:-1]:
        src+=f'''  apply (covers_append_iff _ _ _).mpr
  refine ⟨{m}_cells y track,?_⟩
  rw [show ({a}/64:ℝ) + {m}Blocks.length / 64 = {b}/64 by
    rw [show {m}Blocks.length = {b-a} from rfl]; norm_num]
'''
    src+='  exact '+groups[-1][2]+'_cells y track\n'
    src+=f'''theorem original_birth {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}} (entry : Entry uC zC uA zA φ) :
    DommaschkOppositeInnerTrajectory.FromBirth uC zC uA zA φ {n} {pn}.forward {pn}.backward
      (fun y => Covers false {angle_functions()} DommaschkNativeWellAction.level (-{n}/64) blocks) :=
  from_entry entry forward_steps backward_steps physical_cells

open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ, |φ-phase| ≤ width → DommaschkOppositeInnerTrajectory.FromBirth uC zC uA zA φ
        {n} {pn}.forward {pn}.backward
        (fun y => Covers false {angle_functions()} DommaschkNativeWellAction.level (-{n}/64) blocks) := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,eC,eA,entry⟩ := DommaschkOppositeInnerSeed.from_nested_tori
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,eC,eA,fun φ hφ => original_birth (entry φ hφ)⟩
end PlasmaLean.Design.{name}
'''
    return name,src,['forward_steps','backward_steps','physical_cells','original_birth','from_nested_tori']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for x in ['packet','core','campaign','output']:
        p.add_argument('--'+x,required=True,type=Path)
    p.add_argument('--length',type=int,default=CUT)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-inner-through')
    a=p.parse_args()
    manifest=json.loads(a.campaign.read_text())
    core=json.loads(a.core.read_text())
    n=a.length
    if (not 0<n<=CUT or digest(a.packet)!=CHECKSUM or manifest['packet_sha256']!=CHECKSUM
            or core['packet_sha256']!=CHECKSUM or manifest['core']!=core['key'] or core['module']!=NAME):
        p.error('expected original q1r470 trajectory, matching full core and a valid prefix')
    archive=Path(core['import_paths'][0]); admitted(archive,NAME,core['key'])
    env(a)
    key=[CHECKSUM,a.version,digest(DESIGN/(THEORY+'.trace')),core['key']]
    tab={}
    for stage in ('ode','panels'):
        rr={}
        for lo,hi,path in manifest['receipts'][stage]:
            if lo>=n:
                continue
            checked=entries(Path(path),stage,lo,hi,core['key'])
            if checked is None:
                raise ValueError('incomplete signed receipt: '+path)
            for r in checked:
                if r['index']<n:
                    i=(r['index'],r['direction'])
                    if i in rr:
                        raise ValueError('overlapping receipts for '+str(i))
                    rr[i]=r
        if len(rr)!=2*n:
            raise ValueError('missing closed '+stage+' rows in requested prefix')
        tab[stage]=rr
    raw=packet_source(n,load(a.packet)); pn=raw[0]
    pr,prec=compile_modules(a.cache/pn,[raw],[],key,a,PACK,qualified_claims=[
        'PlasmaLean.Design.DommaschkOppositeInnerTrajectory.from_entry'])
    links=[pr,archive]; keys=[*key,prec['key']]; segments=[]
    for lo in range(0,n,8):
        hi=min(n,lo+8)
        part=segment(pn,n,lo,hi,tab['ode'],tab['panels'])
        parent=[r for stage in tab.values() for (i,_),r in stage.items() if lo<=i<hi]
        deps=[*key,prec['key'],*[r['key'] for r in parent]]
        overlay=merge_import_roots(a.cache,[pr,archive,*[Path(s) for r in parent for s in r['import_paths']]],deps)
        root,rec=compile_modules(a.cache/part[0],[part],[overlay],deps,a,GROUP)
        links.extend([root,overlay]); keys.append(rec['key']); segments.append((lo,hi,part[0]))
    overlay=merge_import_roots(a.cache,links,keys)
    term=aggregate(n,pn,segments)
    root,r=compile_modules(a.cache/term[0],[term],[overlay],keys,a,TOP)
    result={k:v for k,v in r.items() if k!='artifacts'}
    result.update(packet_sha256=CHECKSUM,core=core['key'],length=n,physical_rows=2*n,
                  panels=2*n*24,import_paths=[str(root),str(overlay)])
    save(a.output,result)
    print(term[0],r['key'],flush=True)


if __name__=='__main__':
    main()
