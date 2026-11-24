"""Use compiled central fields and a common spatial perturbation bound for strict physical signs."""
import argparse
import ast
import gzip
import json
from pathlib import Path
import re
import subprocess

from bounce_mirror_pilot import HEIGHTS, Model, ZERO
from emit_sparse_taylor_slab import RECORD, ROOT, model_literal, models as sparse_models
from emit_uniform_field_error import budget
from screen_sparse_reference_defects import sparse_fields
from verify_mirror_endpoint_signs import header
from verify_pre_mirror_signs import (ALLOWED, DESIGN, artifact_hashes, compile_modules, digest,
                                    inputs, jacobian, own_fields, prove_row, quarters, save, split)


PACKAGE='UniformFieldCache'


def existing(args,i,upper):
    path=args.cache/'rows'/f'{i:03}.json'
    if not path.is_file():
        return None
    public=json.loads(path.read_text())
    stem=('DommaschkUpperPreMirrorSign' if upper else 'DommaschkPreMirrorSign')+f'{i:03}'
    if (public.get('module')!=stem or public.get('index')!=i or public.get('packet_sha256')!=args.keys[0]
            or public.get('lean_version')!=args.keys[1] or set(public['axioms'])!=ALLOWED):
        return None
    root=Path(public['import_paths'][0])
    r=json.loads((root/'accepted.json').read_text())
    if (root!=args.cache/stem/public['key'] or r['key']!=public['key'] or set(r['axioms'])!=ALLOWED
            or set(r['theorems'])!={f'PlasmaLean.Design.{stem}.{phase}_tube_below' for phase in ('fwd','back')}):
        raise ValueError('inconsistent row manifest')
    artifact_hashes(root,r)
    if not Path(public['import_paths'][1]).is_dir():
        raise ValueError('missing upstream row imports')
    return public


def central(args,i,row):
    stem=f'DommaschkTraceResidualForward{i:03}'
    for marker in sorted((args.central_cache/stem).glob('*/accepted.json')):
        rec=json.loads(marker.read_text())
        if (rec['index']!=i or rec['direction']!=1 or rec['theorem']!=stem+'.physical_defect'
                or set(rec['axioms'])!=ALLOWED):
            continue
        base=marker.parent
        tree=base/'TraceCache'
        _,nom=inputs(row,i,0,0)
        rx=r'ofDyadic 80 (\[[^\]]*\]) \((-?\d+)\)'
        params=[Model(ast.literal_eval(p),int(e)) for p,e in re.findall(rx,(tree/(stem+'Inputs.lean')).read_text())]
        if len(params)!=4 or any((a.a,a.e)!=(b.a,b.e) for a,b in zip(params,nom,strict=True)):
            continue
        artifact_hashes(base,rec)
        blocks=[]
        for p,tag in zip(('dD','dnR','dnZ'),'DRZ',strict=True):
            src=(tree/(stem+tag+'.lean')).read_text()
            m=re.search('^def '+p+'0 : Model := '+rx,src,re.MULTILINE)
            if not m:
                raise ValueError(f'cannot read central model {p} for row {i}')
            blocks.append(Model(ast.literal_eval(m[1]),int(m[2])))
        return stem,(base,rec),blocks
    return None


def gap_upper(rad,fs,height):
    d,n,z=fs
    r2=rad*rad
    r4=r2*r2
    h8=Model.rational(height)*(r4*r4)
    rd=rad*d
    return ((rd-h8)*(rd+h8)+n*n+z*z).bound()[1]


def transferred(args,i,row,out,upper):
    data=central(args,i,row)
    if data is None:
        return None
    source,record,vals=data
    fs=[Model(m.a,m.e+e) for m,e in zip(vals,args.errors,strict=True)]
    rad,cols=inputs(row,i,out,out)
    if gap_upper(rad,fs,HEIGHTS[int(upper)])>=0:
        return None
    stem=f'DommaschkUniformModel{i:03}'
    src=header(stem,['PlasmaLean.Design.DommaschkPerturbedFieldModel','TraceCache.'+source])
    src+=('open DommaschkPerturbedFieldModel\ndef trial : Inputs := ⟨'
          +', '.join(map(model_literal,cols))+'⟩\n')
    src+=f'''private theorem geometry : Geometry {source}.reference trial := by
  constructor
  · apply eq_of_beq; kernel_fact
  · apply eq_of_beq; kernel_fact
  · rfl
  · rfl
  all_goals kernel_fact
'''
    for p,m in zip(('dD','dnR','dnZ'),fs,strict=True):
        src+=f'''def {p}0 : Model := {model_literal(m)}
theorem {p}_checked : FieldModel trial {p} {p}0 :=
  transfer geometry {source}.{p}_checked DommaschkUniformFieldError.{p}_bound
    (eq_of_beq (by kernel_fact)) (by kernel_fact)
'''
    src+='\nend PlasmaLean.Design.'+stem+'\n'
    root,r=compile_modules(args.cache/stem,[(stem,src,[p+'_checked' for p in ('dD','dnR','dnZ')])],
                           [record[0]],[args.keys,record[1]['key'],digest(DESIGN/'DommaschkPerturbedFieldModel.trace')],
                           args,PACKAGE)
    provider=rad,cols,stem,[PACKAGE+'.'+stem],[record,(root,r)]
    return prove_row(args,i,row,out,[('',0,provider)],field_values=fs,upper=upper)


def run(args,i,b,f):
    upper=i>=316
    already=existing(args,i,upper)
    if already:
        return already
    out=max(t[i]['physical_radius_out'] for t in (b,f))
    if b[i]['coefficients']!=[f[i]['coefficients'][0],[-c for c in f[i]['coefficients'][1]]]:
        raise ValueError(f'wrong reflected reference on {i}')
    shared=jacobian(args,i,f[i],out)
    if shared:
        rad,cols=shared[:2]
        values=[sum(sparse_models(t,cols),ZERO) for t in sparse_fields()]
        if gap_upper(rad,values,HEIGHTS[int(upper)])<0:
            return prove_row(args,i,f[i],out,[('',0,shared)],upper=upper)
    r=transferred(args,i,f[i],out,upper)
    if r:
        return r
    rad,cols=inputs(f[i],i,out,out)
    nums=lambda cs:[sum(sparse_models(t,cs),ZERO) for t in sparse_fields()]
    if gap_upper(rad,nums(cols),HEIGHTS[int(upper)])<0:
        return prove_row(args,i,f[i],out,[('',0,(rad,cols,*own_fields(args,i,'',cols)))],upper=upper)
    cells=split(i,f[i],out)
    if any(gap_upper(r,nums(c),HEIGHTS[int(upper)])>=0 for _,_,(r,c) in cells):
        cells=quarters(i,f[i],out)
        if any(gap_upper(r,nums(c),HEIGHTS[int(upper)])>=0 for _,_,(r,c) in cells):
            raise ValueError(f'row {i} lacks a strict bound on one of its four radial cells')
    parts=[(tag,shift,(r,c,*own_fields(args,i,tag,c))) for tag,shift,(r,c) in cells]
    return prove_row(args,i,f[i],out,parts,upper=upper)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--range',nargs=2,type=int,metavar=('FIRST','LAST'))
    p.add_argument('--indices',nargs='+',type=int)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/pre-mirror-signs')
    p.add_argument('--jacobian-cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    p.add_argument('--central-cache',type=Path,default=ROOT/'.lake/trace-residual')
    a=p.parse_args()
    if (a.range is None)==(a.indices is None):
        p.error('choose --indices or --range')
    indices=a.indices if a.indices else list(range(a.range[0],a.range[1]+1))
    if not indices or min(indices)<0 or max(indices)>323:
        p.error('expected lower-height rows 0–315, upper-height rows 316–323')
    a.cached_only=False
    a.cache=a.cache.resolve()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    a.keys=[digest(RECORD),lake('lean','--version'),digest(DESIGN/'DommaschkBounceTaylor.trace')]
    a.errors=[budget(t) for t in sparse_fields()]
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    if (packet['section_in_half_pi'],packet['launch_u'],[t['direction'] for t in packet['traces']])!=(0,'47/100',[-1,1]):
        raise ValueError('expected the section-zero packet')
    b,f=[t['steps'] for t in packet['traces']]
    results=[]
    for i in indices:
        results.append(run(a,i,b,f))
        save(a.output,results)
