"""Check the five exact action Taylor models for an individual direction, section and height."""
import argparse
from fractions import Fraction
from math import comb
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_common_section import section_polynomial_data
from bounce_mirror_pilot import HEIGHTS, Model, R0
from bounce_phase_strength import ShiftedStrength
from emit_position_slabs import step
from emit_sparse_taylor_slab import model_literal
from screen_action_panel_resolution import endpoint_inputs
from screen_sparse_reference_defects import sparse_fields
from verify_backward_physical_prefix import compile_modules, union
import verify_native_action_models as native
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def env(a):
    def lake(*args):
        return subprocess.check_output(['lake','env',*args],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    a.version=lake('lean','--version')


def section_data(a,section):
    if not section:
        data=native.static_data()
        return data,native.verify_static(SimpleNamespace(**{**vars(a),'cache':a.native_cache,'fields':range(4)}),data)
    table=section_polynomial_data(1)
    models=[g[0] for g in table]+[ShiftedStrength(table).diff[0]]
    polys=list(sparse_fields())
    polys.append(polys[0]+[(-HEIGHTS[0]*comb(7,j)*R0**(7-j),(j,0,0,0)) for j in range(8)])
    opposite=[[(q*(-1)**(m[2]+m[3]),m) for q,m in p] for p in polys]
    data=native.weighted_channels(opposite,models)
    deps=[a.version,digest(DESIGN/'DommaschkCoarseActionPhase.trace')]
    leaves=[]
    for k,channels in enumerate(data):
        name='DommaschkOppositeActionData'+native.FIELDS[k]
        symbol='(DommaschkCoarseActionPhase.halfTurn '+native.SP_FIELDS[k]+')'
        _,code,audit=native.emit_static_field(name,symbol,channels)
        code=code.replace('module\n','module\npublic import PlasmaLean.Design.DommaschkCoarseActionPhase\n',1)
        leaves.append(compile_modules(a.cache/name,[(name,code,audit)],[],deps,a,native.DATA_PACKAGE))
    return data,leaves


def factors(r,raw,height):
    """Use precisely the operation order of ShiftedStrength.calculate and panel_row."""
    d,nr,nz,shift=raw
    models=dict(radius=r,den=d,nr=nr,nz=nz,shift=shift,
                coefficient=Model.rational(HEIGHTS[0]**2-height**2))
    ops=[('r2','*','radius','radius'),('r4','*','r2','r2'),('r8','*','r4','r4'),
         ('r16','*','r8','r8'),('rd','*','radius','den'),('rd2','*','rd','rd'),
         ('nr2','*','nr','nr'),('nz2','*','nz','nz'),('sum1','+','rd2','nr2'),('u','+','sum1','nz2'),
         ('twice','+','den','den'),('negativeShift','-','shift',None),('other','+','twice','negativeShift'),
         ('first','*','r2','shift'),('toroidal','*','first','other'),
         ('sum2','+','toroidal','nr2'),('base','+','sum2','nz2'),('adj','*','r16','coefficient'),
         ('gap','+','base','adj'),('num','-','gap',None)]
    for name,op,left,right in ops:
        v=models[left]
        models[name]=(-v if op=='-' else v+models[right] if op=='+' else v*models[right])
    return ops,models


def physical(stem,inp,fields,models,ops,i,sign,section,high):
    clock='t' if sign==1 else '(-t)'
    phase=f'(Real.pi/2+{clock})' if section else clock
    level='(height '+str(high).lower()+')'
    src=native.header(stem,['PlasmaLean.Design.DommaschkCoarseActionPhase',native.INPUT_PACKAGE+'.'+inp,
                            *[native.FIELD_PACKAGE+'.'+leaf for leaf in fields]])
    src+='open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkMirrorTubeCrossing\n'
    src+='open DommaschkFirstMirrorLaunchSign DommaschkNativeActionGeometry\n'
    src+=f'abbrev row := {inp}.row\nabbrev den := {fields[0]}.model\n'
    coefficient=models['coefficient']
    src+=f'def coefficient : Weight := ⟨(height false)^2-{level}^2, {coefficient.a[0]}, {coefficient.e}, by kernel_fact⟩\n'
    for name,*_ in ops:
        src+=f'def {name} : Model := {model_literal(models[name])}\n'
    src+=f'''theorem physical {{prev : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}}
    (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64)) (hx : x ∈ (physicalSlab prev row ({i}/64)).tube t) :
    0 < x 0 ∧ den.Mem (128*t-{2*i+1}) (atPoint dD (x 0) {phase} (x 1)) ∧
    r8.Mem (128*t-{2*i+1}) ((x 0)^8) ∧ r16.Mem (128*t-{2*i+1}) ((x 0)^16) ∧
    u.Mem (128*t-{2*i+1}) ((x 0)^16*(strength {phase} x)^2) ∧
    num.Mem (128*t-{2*i+1}) ((x 0)^16*((({level}:ℚ):ℝ)^2-(strength {phase} x)^2)) := by
  have hr := DommaschkMirrorBracketSlab.positive_radius (a := {i}/64) (r := row)
    (by rwa [show ({i}/64:ℝ)+1/64={i+1}/64 by norm_num]) hx (by kernel_fact) (by kernel_fact)
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  obtain ⟨h_radius,hu,hz⟩ := {inp}.space hx
  have ha := {inp}.angles ht
  have h_coefficient := coefficient.mem (128*t-{2*i+1})
'''
    for k,leaf,symbol in zip(['den','nr','nz','shift'],fields,native.SP_FIELDS,strict=True):
        if k=='shift':
            symbol='(DommaschkCompensatedAction.shiftedD (height false))'
        src+=f'  have h_{k} := {leaf}.sound hs hu hz ha\n'
        if section:
            src+=f'  rw [DommaschkCoarseActionPhase.physical_phase] at h_{k}\n'
        src+=f'  change {leaf}.model.Mem _ (atPoint {symbol} (x 0) {phase} (x 1)) at h_{k}\n'
    for key,op,left,right in ops:
        term={'*':'checked_product','+':'checked_sum','-':'checked_neg'}[op]
        args=('hs ' if op=='*' else '')+f'h_{left}'+(f' h_{right}' if right else '')
        src+=f'  have h_{key} := {term} (out := {key}) {args} ({native.MATCH})\n'
    src+=f'''  refine ⟨hr,h_den,?_,?_,?_,?_⟩
  · convert h_r8 using 1 <;> ring
  · convert h_r16 using 1 <;> ring
  · rw [← squared_numerator hr]
    convert h_u using 1 <;> ring
  · rw [← compensated_numerator hr {phase} (height false) {level}]
    change num.Mem _ (-(_ + _ * (((height false)^2-{level}^2:ℚ):ℝ))) at h_num
    convert h_num using 1 <;> ring
'''
    return stem,src+native.footer(stem),['physical']


def verify(a,label,i,sign,data,static,*,mirror_height=None):
    upper,height,counts,_,traces,packet,ar=endpoint_inputs(label)
    section=int(label[1])
    trace=traces[int(sign==1)]
    if mirror_height is not None and mirror_height not in HEIGHTS:
        raise ValueError('expected one of the two original mirror heights')
    limit = len(trace['steps']) if mirror_height is not None else counts[int(sign==1)]
    if not 0<=i<limit:
        raise ValueError('row outside the selected signed archive')
    ins=native.row_inputs(i,trace)
    stem='DommaschkCoarseModel'+label.upper()+('Fwd' if sign==1 else 'Back')+f'{i:03}'
    if mirror_height is not None and mirror_height != height:
        height = mirror_height
        stem += 'AtUpper' if height == HEIGHTS[1] else 'AtLower'
    old,src,thms=native.emit_input(i,sign,ins)
    inp=stem+'Inputs'
    lookup=f'DommaschkPositionFrames{"Fwd" if sign==1 else "Back"}.block{i//16}[{i%16}]'
    if src.count(lookup)!=1:
        raise ValueError('unexpected reference to the pilot trajectory')
    src=src.replace(lookup,step(trace['steps'][i])).replace(old,inp)
    deps=[a.version,packet,digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),
          digest(DESIGN/'DommaschkPreMirrorSigns.trace')]
    inputs=compile_modules(a.cache/inp,[(inp,src,thms)],[],deps,a,native.INPUT_PACKAGE)
    leaves=[]
    values=[]
    for k,(channels,datum) in enumerate(zip(data,static,strict=True)):
        symbol=native.SP_FIELDS[k]
        if section:
            symbol='(DommaschkCoarseActionPhase.halfTurn '+symbol+')'
        item,value=native.emit_horner_field(stem+native.FIELDS[k],symbol,channels,ins,datum[1]['module'],
                                             inp,native.DATA_PACKAGE,native.INPUT_PACKAGE)
        leaves.append(compile_modules(a.cache/item[0],[item],[union(a.cache,[inputs,datum])],
                                      [a.version,inputs[1]['key'],datum[1]['key']],a,native.FIELD_PACKAGE))
        values.append(value)
    ops,models=factors(ins[0],values,height)
    parents=[*static,inputs,*leaves]
    overlay=union(a.cache,parents)
    item=physical(stem,inp,[r['module'] for _,r in leaves],models,ops,i,sign,section,height==HEIGHTS[1])
    root,m=compile_modules(a.cache/stem,[item],[overlay],[a.version,packet,*[r['key'] for _,r in parents],
                           digest(DESIGN/'DommaschkCoarseActionPhase.trace')],a,native.OUTPUT_PACKAGE)
    out={k:m[k] for k in ['module','key','axioms','theorems']}
    out.update(endpoint=label,direction=sign,index=i,height=str(height),upper=upper,packet_sha256=packet,
               action_sha256=ar,import_paths=[str(root),str(overlay)])
    return out,[models[k] for k in ['den','r8','r16','u','num']]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',required=True)
    p.add_argument('--row',type=int,default=0)
    p.add_argument('--directions',type=int,nargs='+',choices=(-1,1),default=[1,-1])
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-action-models')
    p.add_argument('--native-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    env(a)
    data,static=section_data(a,int(a.endpoint[1]))
    reports=[]
    for sign in a.directions:
        m,_=verify(a,a.endpoint,a.row,sign,data,static)
        reports.append(m)
        save(a.output,reports)
        print(m['module'],m['key'],flush=True)


if __name__=='__main__':
    main()
