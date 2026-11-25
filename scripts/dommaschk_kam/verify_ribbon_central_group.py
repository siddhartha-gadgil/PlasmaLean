"""Prove one group of original central ODE defects for a widened phase-zero radial ribbon."""
import argparse
from fractions import Fraction as F
import json
import os
from pathlib import Path
from tempfile import NamedTemporaryFile

from grouped_central_defect_rows import restriction
from grouped_central_models import coordinates
from ribbon_central_data import LENGTH,WITNESS_SHA,data,label
from verify_backward_physical_prefix import compile_modules,union
from verify_coarse_action_models import env
from verify_endpoint_reference_slabs import PACKAGE
from verify_grouped_central_defects import FIELDS,group_fields
from verify_horner_endpoint_jacobian import inputs_source
from verify_native_endpoint_residuals import TAGS,sharp_source,wrapper
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save


def body(decl):
    name,source,_=decl
    begin='namespace PlasmaLean.Design.'+name+'\n'
    if source.count(begin)!=1:
        raise ValueError(f'missing generated declaration namespace {name}')
    return begin+source.split(begin,1)[1]


def rows_source(stem,rows,a,b,indices,endpoint):
    harmonic=sorted({i//8 for i in indices})
    imports=['PlasmaLean.Design.DommaschkPhysicalCentralJet','PlasmaLean.Design.DommaschkSectionReflection',
        'PlasmaLean.Design.DommaschkGroupedTrialJet',FIELDS+'.'+stem+'Z',
        *[f'PlasmaLean.Design.DommaschkHarmonicBlock{j:02}' for j in harmonic]]
    chunks=['module\n'+''.join('public import '+m+'\n' for m in imports)+
            '\n@[expose] public section\nnoncomputable section\n']
    namespaces={}
    for i in indices:
        f,back,local,ratios,box,_=rows[i]
        name=stem+f'Row{i:03}'
        inp=inputs_source(name+'Inputs',i,coordinates(f),0)
        rest=restriction(name+'Restricted',inp[0],stem,local,F(2*i+1-a-b,b-a),F(1,b-a))
        providers={t:rest[0]+'.'+t for t in TAGS}|{'Inputs':inp[0]}
        sharp=sharp_source(name,f,back,ratios,box,providers=providers,field_imports=[])
        chunks.extend(map(body,[inp,rest,sharp]))
        for sign in (1,-1):
            decl=wrapper(endpoint,i,sign,name)
            chunks.append(body(decl))
            namespaces[i,sign]=decl[0]
    return '\n'.join(chunks),namespaces


def authenticate(records,tile,i,cache):
    if [(r['packet_sha256'],r['endpoint'],r['index'],r['direction']) for r in records]!=[
            (WITNESS_SHA,label(tile),i,sign) for sign in (1,-1)]:
        raise ValueError(f'inconsistent ribbon proof for tile {tile} at {i}')
    for r in records:
        tag='Forward' if r['direction']==1 else 'Back'
        ns=f'DommaschkTraceResidual{label(tile).upper()}{tag}{i:03}'
        key=(r['import_paths'][0],r['import_module'],r['key'])
        if key not in cache:
            cache[key]=admitted(Path(key[0]),key[1],key[2])
        if (ns!=r['module'] or r['namespace']!=ns or r['package']!=PACKAGE or
                'PlasmaLean.Design.'+ns+'.physical_defect' not in cache[key]['theorems']):
            raise ValueError(f'missing actual signed physical defect for {ns}')


def install(path,records,tile,i,cache):
    path.parent.mkdir(parents=True,exist_ok=True)
    with NamedTemporaryFile('w',dir=path.parent,prefix='.pair-') as tmp:
        json.dump(records,tmp,indent=2)
        tmp.write('\n')
        tmp.flush()
        try:
            os.link(tmp.name,path)
        except FileExistsError:
            authenticate(json.loads(path.read_text()),tile,i,cache)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--tile',type=int,choices=range(4),required=True)
    p.add_argument('--span',nargs=2,type=int,required=True)
    p.add_argument('--rows',type=int,nargs='+')
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/ribbon-central-defects')
    p.add_argument('--handoff',type=Path,help='canonical root for all four ribbon campaigns')
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    a,b=args.span
    indices=sorted(args.rows if args.rows is not None else range(a,b))
    if not 0<=a<b<=LENGTH or not indices or len(indices)!=len(set(indices)) or any(not a<=i<b for i in indices):
        p.error('choose a nonempty subset of original rows in the indicated group')
    ins,models,rows=data(args.ribbon,args.tile,a,b)
    if any(r[-1]>1 for r in rows.values()):
        raise ValueError(f'one of the original ribbon defect budgets fails on [{a},{b})')
    endpoint=label(args.tile)
    stem=f'DommaschkRibbon{args.tile}Central{a:03}To{b:03}'
    args.cache=args.cache.resolve()
    args.checksum=WITNESS_SHA
    env(args)
    parents=group_fields(stem,ins,models,args)
    fields=parents[-1][1]
    print(f'{stem} physical fields {fields["key"]} {fields["wall_seconds"]} seconds',flush=True)
    if args.fields_only:
        save(args.output,{k:v for k,v in fields.items() if k!='artifacts'})
        return
    package=stem+f'Rows{indices[0]:03}To{indices[-1]+1:03}'
    src,ns=rows_source(stem,rows,a,b,indices,endpoint)
    claims=['PlasmaLean.Design.'+m+'.physical_defect' for m in ns.values()]
    links=union(args.cache,parents)
    dependencies=[digest(DESIGN/(m+'.trace')) for m in
        ('DommaschkGroupedTrialJet','DommaschkPhysicalCentralJet','DommaschkSectionReflection')]
    dependencies.extend(digest(DESIGN/f'DommaschkHarmonicBlock{j:02}.trace') for j in sorted({i//8 for i in indices}))
    keys=[args.version,WITNESS_SHA,dependencies,[m['key'] for _,m in parents]]
    root,receipt=compile_modules(args.cache/package,[(package,src,[])],[links],keys,args,PACKAGE,
                                 qualified_claims=claims)
    results=[]
    verified={}
    for i in indices:
        records=[]
        for sign in (1,-1):
            item={k:v for k,v in receipt.items() if k!='artifacts'}
            item.update(module=ns[i,sign],namespace=ns[i,sign],import_module=package,package=PACKAGE,
                endpoint=endpoint,index=i,direction=sign,tile=args.tile,section_in_half_pi=0,
                packet_sha256=WITNESS_SHA,central_group=[a,b],lean_version=args.version,
                field_key=fields['key'],import_paths=[str(root),str(links)])
            records.append(item)
        results.extend(records)
        if args.handoff:
            dest=args.handoff/f'tile{args.tile}'/'references'/f'{i:03}.json'
            install(dest,records,args.tile,i,verified)
    save(args.output,results)
    print(f'{package}: {len(claims)} signed physical defects, {receipt["key"]} in {receipt["wall_seconds"]}s',flush=True)


if __name__=='__main__':
    main()
