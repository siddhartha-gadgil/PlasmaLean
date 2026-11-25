"""Verify independent signed q1r470 spatial bounds, central defects and actual physical ODE rows."""
import argparse
import json
from pathlib import Path
from types import SimpleNamespace

from grouped_opposite_central import direction_data, stem
from grouped_profile_harmonics import prepare
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_endpoint_signed_prefix import PACKAGE as PHYSICAL, input_root, physical_source
from verify_fused_endpoint_jacobians import checked_roots, finish
from verify_grouped_central_defects import group_fields
from verify_grouped_endpoint_jacobians import trial_data
from verify_grouped_opposite_defects import PACKAGE as CENTRAL, checked_parents, row_proof
from verify_opposite_action_subwell import CUT, load
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_ribbon_dyadic_jet import dyadic_jet
from verify_signed_mirror_passage import merge_import_roots


LABEL='q1r470'
CHECKSUM='97906e2444eae3e25f072f411b91f8799c1adf2044da9b05469475dec029c13d'


def central(packet,a,b):
    result={}
    for trace in packet['traces']:
        rows=trace['steps']
        sign=trace['direction']
        fs=packet['frame_denominator']
        jobs=[(1,sign,i,rows[i]['coefficients'],rows[i-1]['frame_end'] if i else [[fs,0],[0,fs]],
               rows[i]['frame_end'],rows[i]['defect_upper'],8) for i in range(a,b)]
        result[sign]=direction_data(jobs,a,b)
    return result


def stage(args,group,a,b,data,frames):
    if group=='central':
        items=central(data,a,b)
        failed=[(s,i) for s,(_,_,rr) in items.items() for i,row in rr.items() if row[-1]>1]
    else:
        _,branches,box,matrix,failed=trial_data(LABEL,a,b,args.packet)
    if failed:
        if b==a+1:
            raise ValueError(f'{group} row {a} cannot close original signed budgets: {failed}')
        m=(a+b)//2
        return stage(args,group,a,m,data,frames)+stage(args,group,m,b,data,frames)
    if args.preflight:
        return [dict(stage=group,span=[a,b])]
    if group=='central':
        records=[]
        for sign,(ins,models,rows) in items.items():
            parents=group_fields(stem(LABEL,sign,a,b),ins,models,args,integer=True)
            for i,row in rows.items():
                records.append(row_proof(args,a,b,i,sign,row,parents))
        return records
    key=f'Dommaschk{LABEL.upper()}FusedTrial{a:03}To{b:03}'
    result,models,providers=dyadic_jet(key,box,args)
    if any((m.a,m.e)!=(q.a,q.e) for m,q in zip(models,matrix,strict=True)):
        raise ValueError('the compiled dyadic jet differs from the exact frame preflight')
    local=SimpleNamespace(**(vars(args)|{'output':args.cache/f'matrices-{a:03}-{b:03}.json'}))
    finish(key,a,b,branches,result,models,providers,local)
    return json.loads(local.output.read_text())


def physical(args,i,sign,pair,former,jac,ref):
    tag='Forward' if sign==1 else 'Back'
    jn=f'DommaschkJacobianQ1R470Independent{tag}{i:03}'
    rn=f'DommaschkTraceResidualQ1R470{tag}{i:03}'
    j=input_root(jac,LABEL,1,i,jn,CHECKSUM,args.version)
    r=input_root(ref,LABEL,sign,i,rn,CHECKSUM,args.version)
    if jac['matrix_direction']!=sign or ref['package']!=CENTRAL:
        raise ValueError('different signed rate or central field package')
    paths=[j,*checked_roots(jac,j,args.version),r,*checked_parents(ref,r,args.version)]
    parents=[jac['key'],ref['key']]
    overlay=merge_import_roots(args.cache,paths,parents)
    seed=('PlasmaLean.Design.DommaschkOppositeInnerSeed','DommaschkOppositeInnerSeed.seed') if i==0 else None
    name,src=physical_source(LABEL,sign,pair,former,jn,rn,CENTRAL,initial=seed)
    deps=[CHECKSUM,args.version,digest(DESIGN/'DommaschkEndpointContinuation.trace'),
          digest(DESIGN/'DommaschkOppositeInnerSeed.trace'),*parents]
    root,m=compile_modules(args.cache/name,[(name,src,['checked','field_bounds','physical_step'])],
                           [overlay],deps,args,PHYSICAL)
    return {k:v for k,v in m.items() if k!='artifacts'}|dict(index=i,direction=sign,
            packet_sha256=CHECKSUM,jacobian=jac['key'],residual=ref['key'],import_paths=[str(root),str(overlay)])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',required=True,type=Path)
    p.add_argument('--span',required=True,nargs=2,type=int,metavar=('FIRST','STOP'))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-inner-ode')
    p.add_argument('--preflight',action='store_true')
    p.add_argument('--output',required=True,type=Path)
    args=p.parse_args()
    a,b=args.span
    if digest(args.packet)!=CHECKSUM or not 0<=a<b<=CUT:
        p.error('expected the authenticated q1r470 singleton and an original central span within 0..320')
    args.endpoint,args.checksum,args.rows,args.handoff=LABEL,CHECKSUM,None,None
    args.cache=args.cache.resolve()
    packet=load(args.packet)
    frames={t['direction']:t['steps'] for t in packet['traces']}
    if not args.preflight:
        env(args)
        args.keys=[[CHECKSUM],args.version]
        prepare(args)
    jac=stage(args,'spatial',a,b,packet,frames)
    refs=stage(args,'central',a,b,packet,frames)
    if args.preflight:
        save(args.output,dict(packet_sha256=CHECKSUM,span=[a,b],groups=jac+refs))
        return
    from screen_independent_endpoint_frames import trial_frames
    matrices={(r['index'],r['matrix_direction']):r for r in jac}
    defects={(r['index'],r['direction']):r for r in refs}
    signed=[]
    for i,(pair,_) in enumerate(trial_frames(args.packet,a,b-1),a):
        for sign in (1,-1):
            former=frames[sign][i-1] if i else None
            signed.append(physical(args,i,sign,pair,former,matrices[i,sign],defects[i,sign]))
        save(args.output,dict(packet_sha256=CHECKSUM,span=[a,b],rows=signed))
        print(f'physical q1r470 signed row {i} accepted',flush=True)


if __name__=='__main__':
    main()
