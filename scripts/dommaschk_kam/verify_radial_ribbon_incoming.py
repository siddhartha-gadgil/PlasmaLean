"""Prove upper-height exclusion from birth to the turning collar on four radial ribbons."""
import argparse
from fractions import Fraction
from math import comb
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS, R0, R0M
from emit_sparse_taylor_slab import model_literal
from screen_sparse_jacobians import field_jet
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_harmonic_group_exclusion import harmonics, inputs, negative_gap
from verify_native_action_models import MATCH, emit_horner_field, emit_static_field, footer, header
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_slopes import channels, cover, load_ribbon, value

STATIC='RadialRibbonIncomingDataCache'
INPUT='RadialRibbonIncomingInputCache'
FIELDS='RadialRibbonIncomingFieldsCache'
OUT='RadialRibbonIncomingGroupCache'
TILES=tuple(range(4))


def field_tables():
    den, radial, height = [t[0] for t in field_jet()]
    ref=HEIGHTS[1]
    shifted=den + [(-ref*comb(7,j)*R0**(7-j),(j,0,0,0)) for j in range(8)]
    return list(zip(('D','R','Z','S'), ('dD','dnR','dnZ',f'(DommaschkCompensatedAction.shiftedD ({ref}))'),
                    map(channels,(den,radial,height,shifted)),strict=True))


def plan(traces,tables,a,b):
    tube=cover(traces,TILES,a,b)
    r,z,c,s=tube
    params=r-R0M,z,harmonics(c,s)
    vals=[value(table,params) for _,_,table in tables]
    gap=negative_gap(r,vals)
    if gap.bound()[1]<0:
        return [(a,b,tube,gap)]
    if b==a+1:
        raise ValueError(f'upper-height gap contains zero on incoming row {a}')
    m=(a+b)//2
    return plan(traces,tables,a,m)+plan(traces,tables,m,b)


def prove(group,tables,static,original,args):
    a,b,tube,gap=group
    name=f'DommaschkRibbonUpperExclusion{a:03}To{b:03}'
    keys=[args.version,original,a,b,digest(DESIGN/'DommaschkGroupedHarmonicGap.trace')]
    inp,coords=inputs(name+'Inputs',tube)
    ir=compile_modules(args.cache/inp[0],[inp],[],keys,args,INPUT)
    packages=[ir,*static]
    providers=[]
    models=[]
    for (tag,symbol,table),(sr,sm) in zip(tables,static,strict=True):
        field,model=emit_horner_field(name+tag,symbol,table,coords,sm['module'],inp[0],STATIC,INPUT)
        checked=compile_modules(args.cache/field[0],[field],[sr,ir[0]],[keys,sm['key'],ir[1]['key']],args,FIELDS)
        packages.append(checked)
        providers.append(field[0])
        models.append(model)
    lo,hi=negative_gap(tube[0],models).bound()
    if (lo,hi)!=gap.bound() or hi>=0:
        raise ValueError('the proposed and checked incoming models disagree')
    src=header(name,[INPUT+'.'+inp[0],*[FIELDS+'.'+f for f in providers]])
    src+='open DommaschkGroupedMirrorModels DommaschkGroupedHarmonicGap DommaschkPreMirrorSigns\n'
    src+='open DommaschkMirrorEndpointSign DommaschkFirstMirrorLaunchSign DommaschkBounceField\n'
    src+=f'''abbrev group := {inp[0]}.group
private def evaluated : Model := {model_literal(gap)}

theorem below : group.Below (height true) := by
  intro w R z t hw hR hr hz hc hs
  have hu := shifted_mem (u := {inp[0]}.displacement) hr (eq_of_beq (by kernel_fact)) (by kernel_fact)
  have waves := {inp[0]}.angles hw hc hs
'''
    for j,f in enumerate(providers):
        src+=f'  have field{j} := {f}.sound hw hu hz waves\n'
    src+=f'''  have observed := estimate_mem (k := height true) hw hr field0 field1 field2 field3
  have same : Matches (estimate group.radial {' '.join(f+'.model' for f in providers)}) evaluated :=
    {MATCH}
  rw [same.eq] at observed
  have bound := enclose (c := ⟨[({(lo+hi)/2})],({(hi-lo)/2})⟩) hw observed (by kernel_fact)
  apply physical_sign false hR (by norm_num [height])
  change gap R (height true) (atPoint dD R t z) (atPoint dnR R t z) (atPoint dnZ R t z) < 0
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at bound
  unfold atPoint
  linarith only [bound.2]
'''+footer(name)
    overlay=union(args.cache,packages)
    root,rec=compile_modules(args.cache/name,[(name,src,['below'])],[overlay],
                             [keys,[m['key'] for _,m in packages]],args,OUT)
    return dict(start=a,stop=b,key=rec['key'],module=name,upper_gap=str(hi),
                axioms=rec['axioms'],import_paths=[str(root),str(overlay)])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ribbon',type=Path,required=True)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-ribbon-incoming')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--screen',action='store_true')
    parser.add_argument('--groups',type=int,nargs='+',help='starting indices of required groups')
    args=parser.parse_args()
    table=field_tables()
    traces=load_ribbon(args.ribbon)
    plan_=plan(traces,table,0,317)
    original=digest(args.ribbon)
    if args.screen:
        save(args.output,dict(ribbon=original,groups=[dict(start=a,stop=b,upper=str(gap.bound()[1]))
                                                      for a,b,_,gap in plan_]))
        return
    if args.groups:
        wanted=set(args.groups)
        plan_=[g for g in plan_ if g[0] in wanted]
        if {g[0] for g in plan_}!=wanted:
            parser.error('unknown starting row')
    env(args)
    static=[]
    for tag,target,p in table:
        item=emit_static_field('DommaschkRibbonUpperData'+tag,target,p)
        static.append(compile_modules(args.cache/item[0],[item],[],
                      [args.version,digest(DESIGN/'DommaschkNativeActionModel.trace')],args,STATIC))
    out=[]
    for group in plan_:
        row=prove(group,table,static,original,args)
        out.append(row)
        save(args.output,dict(ribbon=original,groups=out))
        print(row['module'],row['key'],flush=True)


if __name__=='__main__':
    main()
