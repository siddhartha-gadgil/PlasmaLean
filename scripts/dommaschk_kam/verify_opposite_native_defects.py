"""Certify the two original opposite-section defects using independent native harmonic models."""
import argparse
from fractions import Fraction
from pathlib import Path
from string import Template
import subprocess

from bounce_mirror_pilot import R0M
from emit_sparse_taylor_slab import model_literal
from emit_sparse_trace_defect_samples import matrix_literal
from screen_endpoint_jacobian_sharing import native_jet
from screen_native_endpoint_residuals import residual_data,sharp_budget
from screen_sparse_jacobians import field_jet
from screen_sparse_reference_defects import jobs
from verify_backward_physical_prefix import compile_modules,union
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_horner_endpoint_jacobian import DATA,inputs_source
from verify_mirror_physical_hit import admitted
from verify_native_action_models import emit_horner_field,emit_static_field,weighted_channels
from verify_native_endpoint_residuals import SYMBOLS,TAGS
from verify_physical_trace_slabs import DESIGN,HERE,RECORD,ROOT,digest,key_of,save

FIELDS='SignedCentralFieldCache'
PACKAGE='SignedNativeEndpointResidualCache'
TEMPLATE=HERE/'templates/signed_native_central.lean.tpl'


def names(label,sign,i):
    tag='Forward' if sign==1 else 'Back'
    return (f'DommaschkSignedCentral{label.upper()}{tag}{i:03}',
            f'DommaschkTraceResidual{label.upper()}{tag}{i:03}')


def keys(version,checksum,parents):
    return [version,checksum,digest(DESIGN/'DommaschkPhysicalCentralJet.trace'),
            *[p['key'] for p in parents]]


def checked_parents(row,root,version):
    stem,name=names(row['endpoint'],row['direction'],row['index'])
    parents=row['signed_native_parents']
    if ([p['module'] for p in parents]!=['DommaschkHornerJetData'+t for t in TAGS]+[stem+'Z'] or
            name!=row['module'] or row['endpoint'] not in ENDPOINTS[4:]):
        raise ValueError('incompatible direction, section or physical central polynomials')
    for p in parents:
        admitted(Path(p['root']),p['module'],p['key'])
    code=(root/PACKAGE/(name+'.lean')).read_text()
    if key_of([keys(version,row['packet_sha256'],parents),[(name,code,['physical_defect'])]])!=row['key']:
        raise ValueError('signed central evidence does not match the dependency keys')
    return [Path(p['root']) for p in parents]


def physical_source(name,job,ratio,box,inputs,fields,field_import):
    """Bind the exact signed centre, original frame and archived allowance to field memberships."""
    _,sign,i,_,left,right,budget,_=job
    x,y,den=box
    template=TEMPLATE.read_text()
    original_import='public import SignedCentralFieldCache.$fieldZ'
    if template.count(original_import)!=1:
        raise ValueError('missing the certified field import in the signed central template')
    template=template.replace(original_import,'public import $field_import')
    return Template(template).substitute(name=name,input=inputs,field_import=field_import,
        fieldR=fields['R'],fieldZ=fields['Z'],fieldD=fields['D'],left=matrix_literal(left),
        right=matrix_literal(right),budget=budget,x=x,y=y,den=den,ratio=', '.join(map(model_literal,ratio)),
        i=i,stop=i+1,off=2*i+1,back=str(sign==-1).lower(),sign=sign)


def check_direction(job,data,args):
    section,sign,i,_,_,_,budget,_=job
    stem,name=names(args.endpoint,sign,i)
    (r,z,angles),actual,ratio,(x,y,den)=residual_data(job)
    if sharp_budget(x,y,den)>Fraction(budget):
        raise ValueError(f'the native quotient exceeds the original {sign} budget at {i}')
    inputs=(r,r-R0M,z,angles)
    decls=[inputs_source(stem+'Inputs',i,inputs,section,backward=sign==-1)]
    parents=[]
    for (tag,sym,group,static),expected in zip(data,actual,strict=True):
        (mod,source,claims),m=emit_horner_field(stem+tag,sym,group,inputs,static[1]['module'],
                                                stem+'Inputs',DATA,FIELDS)
        if m.a!=expected.a or m.e!=expected.e:
            raise ValueError(f'physical harmonic evaluation mismatch at {mod}')
        if tag=='Z':
            source=source.replace('module\n',f'module\npublic import {FIELDS}.{stem}D\npublic import {FIELDS}.{stem}R\n',1)
        decls.append((mod,source,claims))
        parents.append(static)
    version,checksum=args.version,args.checksum
    field_keys=[version,checksum,digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),
                digest(DESIGN/'DommaschkOppositeHarmonic.trace'),*[m['key'] for _,m in parents]]
    jet=compile_modules(args.cache/(stem+'Z'),decls,[union(args.cache,parents)],field_keys,args,FIELDS)
    parents.append(jet)
    deps=[dict(module=m['module'],key=m['key'],root=str(path)) for path,m in parents]
    src=physical_source(name,job,ratio,(x,y,den),stem+'Inputs',{t:stem+t for t in TAGS},FIELDS+'.'+stem+'Z')
    root,record=compile_modules(args.cache/name,[(name,src,['physical_defect'])],[union(args.cache,parents)],
                                keys(version,checksum,deps),args,PACKAGE)
    row={k:v for k,v in record.items() if k!='artifacts'}
    row.update(endpoint=args.endpoint,index=i,direction=sign,launch_u=str(Fraction(int(args.endpoint[3:]),1000)),
        section_in_half_pi=section,packet_sha256=checksum,lean_version=version,import_paths=[str(root)],
        signed_native_parents=deps,package=PACKAGE)
    checked_parents(row,root,version)
    print(f'{name} {row["key"]} field {jet[1]["wall_seconds"]}s defect {row["wall_seconds"]}s',flush=True)
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',required=True,choices=ENDPOINTS[4:])
    p.add_argument('--row',required=True,type=int)
    p.add_argument('--direction',type=int,choices=(-1,1))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-native-central')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 0<=a.row<391:
        p.error('the original slab must lie in [0,391)')
    if a.direction is None and a.output.parent.name=='references':
        from plan_opposite_central_groups import MARKER,validate
        if (a.output.parent.parent/MARKER).exists():
            from campaign_grouped_central import dispatch
            if dispatch(a,marker_name=MARKER,labels=ENDPOINTS[4:],check_plan=validate,
                        producer='verify_grouped_opposite_defects.py'):
                return
    a.cache=a.cache.resolve()
    packet=RECORD.with_name(f'bounce_frame_q1_u{a.endpoint[3:]}.json.gz')
    a.checksum=digest(packet)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    a.version=lake('lean','--version')
    channels=weighted_channels([j[0] for j in field_jet()],[j[0] for j in native_jet()])
    data=[]
    for t,s,g in zip(TAGS,SYMBOLS,channels,strict=True):
        n='DommaschkHornerJetData'+t
        dep=compile_modules(ROOT/'.lake/endpoint-horner-jacobians'/n,[emit_static_field(n,s,g)],[],
                            [DATA,a.version,digest(DESIGN/'DommaschkNativeActionModel.trace')],a,DATA)
        data.append((t,s,g,dep))
    rows=[check_direction(job,data,a) for job in jobs(packet,8,False) if
          job[2]==a.row and (a.direction is None or a.direction==job[1])]
    if len(rows)!=(2 if a.direction is None else 1):
        raise ValueError('missing original signed reference data')
    save(a.output,rows)


if __name__=='__main__':
    main()
