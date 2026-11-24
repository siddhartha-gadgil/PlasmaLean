"""Certify several original phase-zero central ODE defects from one higher-order harmonic evaluation."""
import argparse
from fractions import Fraction as F
from pathlib import Path
import subprocess

from emit_sparse_taylor_slab import model_literal
from grouped_central_models import DEGREE,boxes,compress,field_models,quotient
from screen_endpoint_jacobian_sharing import native_jet
from screen_reflected_reference import paired_jobs
from screen_sparse_jacobians import field_jet
from screen_sparse_reference_defects import jobs
from verify_backward_physical_prefix import compile_modules,union
from verify_horner_endpoint_jacobian import DATA
from verify_native_action_models import WAVES,emit_horner_field,emit_static_field,footer,header,weighted_channels
from verify_native_endpoint_residuals import SYMBOLS,TAGS
from verify_physical_trace_slabs import DESIGN,RECORD,ROOT,digest,save

FIELDS='GroupedCentralFieldCache'
LABELS=('q0r478','q0r523','q0r531')


def inputs_source(name,values):
    _,u,z,waves=values
    src=header(name,['PlasmaLean.Design.DommaschkVariableHorner'])
    src+=f'def displacement : Model := {model_literal(u)}\ndef vertical : Model := {model_literal(z)}\n'
    src+='def phase : Wave → Model\n'+''.join(f'  | .{w} => {model_literal(m)}\n' for w,m in zip(WAVES,waves,strict=True))
    return name,src+footer(name),[]


def data(label,a,b):
    p=RECORD.with_name(f'bounce_frame_q0_u{label[3:]}.json.gz')
    forward=[(f,bb) for f,bb in paired_jobs(p) if a<=f[2]<b]
    backward={job[2]:job for job in jobs(p,8,False) if job[1]==-1 and a<=job[2]<b}
    ins=boxes([j for j,_ in forward])
    models=field_models(ins)
    rows={}
    for job,bb in forward:
        i=job[2]
        if F(backward[i][6])!=bb:
            raise ValueError(f'changed backward budget at {label} {i}')
        local=[compress(m,i,a,b) for m in models]
        ratios,box,sharp=quotient(job,local)
        rows[i]=(job,backward[i],local,ratios,box,sharp/min(bb,F(job[6])))
    return p,ins,models,rows


def group_fields(stem,ins,models,args):
    item=inputs_source(stem+'Inputs',ins)
    decls=[item]
    parents=[]
    channels=weighted_channels([j[0] for j in field_jet()],[j[0] for j in native_jet()])
    for t,s,g,expected in zip(TAGS,SYMBOLS,channels,models,strict=True):
        name='DommaschkHornerJetData'+t
        static=compile_modules(ROOT/'.lake/endpoint-horner-jacobians'/name,[emit_static_field(name,s,g)],[],
                  [DATA,args.version,digest(DESIGN/'DommaschkNativeActionModel.trace')],args,DATA)
        parents.append(static)
        (n,src,proofs),m=emit_horner_field(stem+t,s,g,ins,name,item[0],DATA,FIELDS,degree=DEGREE)
        if m.a!=expected.a or m.e!=expected.e:
            raise ValueError(f'inconsistent native physical field {n}')
        if t=='Z':
            src=src.replace('module\n',f'module\npublic import {FIELDS}.{stem}D\npublic import {FIELDS}.{stem}R\n',1)
        decls.append((n,src,proofs))
    keys=[args.version,args.checksum,digest(DESIGN/'DommaschkVariableHorner.trace'),*[m['key'] for _,m in parents]]
    group=compile_modules(args.cache/(stem+'Z'),decls,[union(args.cache,parents)],keys,args,FIELDS)
    return parents+[group]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=LABELS,required=True)
    p.add_argument('--span',required=True,nargs=2,type=int,metavar=('FIRST','STOP'))
    p.add_argument('--preflight',action='store_true')
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--handoff',type=Path,help='install missing pairs in this matching continuation campaign')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-central-defects')
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    a,b=args.span
    if not 0<=a<b<=391:
        p.error('choose a nonempty original interval within [0,391)')
    packet,ins,models,rows=data(args.endpoint,a,b)
    args.checksum=digest(packet)
    ratios={i:str(r[-1]) for i,r in rows.items()}
    if args.preflight:
        save(args.output,dict(endpoint=args.endpoint,span=[a,b],packet=args.checksum,ratios=ratios))
        return
    if max(F(v) for v in ratios.values())>1:
        raise ValueError(f'one of the original signed budgets fails: {ratios}')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path=lake('printenv','LEAN_PATH')
    args.version=lake('lean','--version')
    args.cache=args.cache.resolve()
    stem=f'Dommaschk{args.endpoint.upper()}Central{a:03}To{b:03}'
    parents=group_fields(stem,ins,models,args)
    if args.fields_only:
        final=parents[-1][1]
        save(args.output,{k:v for k,v in final.items() if k!='artifacts'})
        return
    from grouped_central_defect_rows import finish
    finish(stem,a,b,rows,parents,args)


if __name__=='__main__':
    main()
