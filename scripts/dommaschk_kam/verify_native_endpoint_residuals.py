"""Check two signed physical central defects using one harmonic Horner evaluation of D, nR and nZ."""
import argparse
from fractions import Fraction
from pathlib import Path
import subprocess
from string import Template
import time

from bounce_mirror_pilot import R0M
from emit_sparse_taylor_slab import model_literal
from emit_sparse_trace_defect_samples import matrix_literal, reference_columns
from screen_endpoint_jacobian_sharing import native_jet
from screen_native_endpoint_residuals import residual_data, sharp_budget
from screen_reflected_reference import paired_jobs
from screen_sparse_jacobians import field_jet
from screen_sparse_reference_defects import jobs
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_horner_endpoint_jacobian import DATA, inputs_source
from verify_mirror_physical_hit import admitted
from verify_native_action_models import emit_horner_field, emit_static_field, weighted_channels
from verify_physical_trace_slabs import DESIGN, HERE, RECORD, ROOT, digest, key_of, save
from verify_signed_mirror_passage import merge_import_roots


FIELDS = 'NativeCentralFieldCache'
BOUNDS = 'NativeCentralBoundsCache'
PACKAGE = 'NativeEndpointResidualCache'
SYMBOLS = ('dD','dnR','dnZ')
TAGS = ('D','R','Z')
THEOREMS = ['exact_pair','forward_sharp','forward_defect','backward_defect']
TEMPLATE = HERE/'templates/native_central_residual.lean.tpl'


def sharp_source(stem,forward,backward,ratios,box):
    _,_,i,_,left,right,budget,_ = forward
    x,y,den=box
    sharp=sharp_budget(x, y, den)
    if sharp>min(Fraction(budget),Fraction(backward[6])):
        raise ValueError(f'central norm exceeds one of the signed allowances at {i}')
    coords=reference_columns(0,-1,i,backward[3])
    source=Template(TEMPLATE.read_text()).substitute(
        name=stem,i=i,stop=i+1,off=2*i+1,back_coords=', '.join(map(model_literal,coords)),
        left=matrix_literal(left),right=matrix_literal(right),back_left=matrix_literal(backward[4]),
        back_right=matrix_literal(backward[5]),forward_budget=budget,back_budget=backward[6],
        sharp=sharp,ratio=', '.join(map(model_literal,ratios)),x=x,y=y,den=den)
    return stem,source,THEOREMS


def wrapper(label,i,sign,provider):
    tag='Forward' if sign==1 else 'Back'
    ref,frame,budget,proof=(('reference','frame','budget','forward_defect') if sign==1 else
                            ('backReference','backFrame','backBudget','backward_defect'))
    name=f'DommaschkTraceResidual{label.upper()}{tag}{i:03}'
    source=f'''module
public import {BOUNDS}.{provider}
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkBounceField DommaschkBounceTaylor FramedTaylorResidual
abbrev reference := {provider}.{ref}
abbrev frame := {provider}.{frame}
abbrev budget := {provider}.{budget}
theorem physical_defect {{t : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64)) :
    let s := 128*t-{2*i+1}
    let v := physicalFlow 0 ({sign}:ℝ) t (position reference s) - velocity reference 128 s
    let w := pulled frame s v
    Real.sqrt ((w 0)^2+(w 1)^2) ≤ (budget:ℝ) := {provider}.{proof} ht
end PlasmaLean.Design.{name}
'''
    return name,source,['physical_defect']


def checked_parents(row,root,version):
    label,i,sign=row['endpoint'],row['index'],row['direction']
    stem=f'DommaschkNativeCentral{label.upper()}{i:03}'
    expected=['DommaschkHornerJetData'+tag for tag in TAGS]+[stem+'Z',stem]
    parents=row['native_parents']
    if [p['module'] for p in parents] != expected:
        raise ValueError('wrong native central field or quotient dependencies')
    roots=[]
    for p in parents:
        base=Path(p['root'])
        admitted(base,p['module'],p['key'])
        roots.append(base)
    decl=wrapper(label,i,sign,stem)
    keys=[version,row['packet_sha256'],*[p['key'] for p in parents]]
    if (decl[0]!=row['module'] or (root/PACKAGE/(decl[0]+'.lean')).read_text()!=decl[1]
            or key_of([keys,[decl]])!=row['key']):
        raise ValueError('native central signed theorem has inconsistent archived parents')
    return roots


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=ENDPOINTS[1:4],required=True)
    p.add_argument('--row',type=int,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-native-central')
    p.add_argument('--static-cache',type=Path,default=ROOT/'.lake/endpoint-horner-jacobians')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 0<=a.row<391:
        p.error('row must lie between 0 and 390')
    a.cache=a.cache.resolve()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    version=lake('lean','--version')
    started=time.monotonic()
    label,i=a.endpoint,a.row
    packet=RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')
    checksum=digest(packet)
    f,back_budget=next(it for it in paired_jobs(packet) if it[0][2]==i)
    b=next(it for it in jobs(packet,8,False) if (it[1],it[2])==(-1,i))
    if Fraction(b[6])!=back_budget:
        raise ValueError('inconsistent backward frame data')
    (r,z,waves),physical,ratios,box=residual_data(f)
    stem=f'DommaschkNativeCentral{label.upper()}{i:03}'
    inputs=(r,r-R0M,z,waves)
    groups=weighted_channels([g[0] for g in field_jet()],[g[0] for g in native_jet()])
    base=[version,digest(DESIGN/'DommaschkNativeActionModel.trace')]
    static=[]
    fields=[inputs_source(stem+'Inputs',i,inputs,0)]
    for tag,symbol,channels,expected in zip(TAGS,SYMBOLS,groups,physical,strict=True):
        name='DommaschkHornerJetData'+tag
        static.append(compile_modules(a.static_cache/name,[emit_static_field(name,symbol,channels)],
                                     [],[DATA,*base],a,DATA))
        decl,actual=emit_horner_field(stem+tag,symbol,channels,inputs,name,stem+'Inputs',DATA,FIELDS)
        if model_literal(actual)!=model_literal(expected):
            raise ValueError('native centre accumulator differs from emitted Horner proof')
        name,source,theorems=decl
        if tag == 'Z':
            source=source.replace('module\n',f'module\npublic import {FIELDS}.{stem}D\n'
                                  f'public import {FIELDS}.{stem}R\n',1)
        fields.append((name,source,theorems))
    def union(items):
        return merge_import_roots(a.cache,[root for root,_ in items],[x['key'] for _,x in items])
    def check(decls,parents,keys,package):
        name=decls[-1][0]
        out=compile_modules(a.cache/name,decls,[union(parents)],keys,a,package)
        print(name,out[1]['key'],out[1]['wall_seconds'],flush=True)
        return out
    field_keys=[version,checksum,digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),
                *[x['key'] for _,x in static]]
    jet=check(fields,static,field_keys,FIELDS)
    parents=[*static,jet]
    sharp=check([sharp_source(stem,f,b,ratios,box)],parents,
                [version,checksum,jet[1]['key'],digest(DESIGN/'DommaschkPhysicalCentralJet.trace'),
                 digest(DESIGN/'DommaschkSectionReflection.trace')],BOUNDS)
    parents.append(sharp)
    deps=[{'root':str(root),'module':x['module'],'key':x['key']} for root,x in parents]
    results=[]
    for sign in (1,-1):
        root,rec=check([wrapper(label,i,sign,stem)],parents,[version,checksum,*[d['key'] for d in deps]],PACKAGE)
        row={k:v for k,v in rec.items() if k!='artifacts'}
        row.update(endpoint=label,index=i,direction=sign,section_in_half_pi=0,
                   launch_u=str(Fraction(int(label[3:]),1000)),packet_sha256=checksum,lean_version=version,
                   package=PACKAGE,import_paths=[str(root)],native_parents=deps)
        results.append(row)
    save(a.output,results)
    print(f'Elapsed {time.monotonic()-started:.3f}s for both actual signs',flush=True)


if __name__=='__main__':
    main()
