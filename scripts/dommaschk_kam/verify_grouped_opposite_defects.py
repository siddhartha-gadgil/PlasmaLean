"""Check the original signed opposite-section defects with separate shared physical field models."""
import argparse
from fractions import Fraction as F
from pathlib import Path
import subprocess

from grouped_central_defect_rows import ROW,install,restriction
from grouped_opposite_central import LABELS,coordinates,data,stem
from verify_backward_physical_prefix import compile_modules,union
from verify_grouped_central_defects import group_fields
from verify_horner_endpoint_jacobian import inputs_source
from verify_mirror_physical_hit import admitted
from verify_native_endpoint_residuals import TAGS
from verify_opposite_native_defects import names,physical_source
from verify_physical_trace_slabs import DESIGN,ROOT,digest,key_of,save

PACKAGE='OppositeGroupedCentralResidualCache'


def keys(version,checksum,parents):
    return [version,checksum,digest(DESIGN/'DommaschkPhysicalCentralJet.trace'),
            *[p['key'] for p in parents]]


def checked_parents(row,root,version):
    label,sign,i=row['endpoint'],row['direction'],row['index']
    a,b=row['central_group']
    if label not in LABELS or sign not in (-1,1) or not 0<=a<=i<b<=391:
        raise ValueError('incorrect signed group or endpoint')
    group=stem(label,sign,a,b)
    ps=row['signed_grouped_central_parents']
    name=names(label,sign,i)[1]
    if (row['section_in_half_pi']!=1 or row['module']!=name or
            [p['module'] for p in ps]!=['DommaschkHornerJetData'+t for t in TAGS]+
            [group+'Z',group+f'Row{i:03}Restricted']):
        raise ValueError('group field and row use different directions, coordinates or section')
    for p in ps:
        admitted(Path(p['root']),p['module'],p['key'])
    source=(root/PACKAGE/(name+'.lean')).read_text()
    if key_of([keys(version,row['packet_sha256'],ps),[(name,source,['physical_defect'])]])!=row['key']:
        raise ValueError('grouped signed physical defect does not match its dependency keys')
    return [Path(p['root']) for p in ps]


def row_proof(args,a,b,i,sign,item,parents):
    job,local,ratio,box,_=item
    group=stem(args.endpoint,sign,a,b)
    row=group+f'Row{i:03}'
    inp=inputs_source(row+'Inputs',i,coordinates(job),1,backward=sign==-1)
    rest=restriction(row+'Restricted',inp[0],group,local,F(2*i+1-a-b,b-a),F(1,b-a))
    r=compile_modules(args.cache/rest[0],[inp,rest],[union(args.cache,parents)],
        [args.version,args.checksum,*[m['key'] for _,m in parents],digest(DESIGN/'DommaschkGroupedTrialJet.trace'),
         digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),digest(DESIGN/'DommaschkOppositeHarmonic.trace')],args,ROW)
    all_parents=[*parents,r]
    deps=[dict(module=m['module'],key=m['key'],root=str(path)) for path,m in all_parents]
    name=names(args.endpoint,sign,i)[1]
    source=physical_source(name,job,ratio,box,inp[0],{t:rest[0]+'.'+t for t in TAGS},ROW+'.'+rest[0])
    root,m=compile_modules(args.cache/name,[(name,source,['physical_defect'])],[union(args.cache,all_parents)],
        keys(args.version,args.checksum,deps),args,PACKAGE)
    item={k:v for k,v in m.items() if k!='artifacts'}
    item.update(endpoint=args.endpoint,index=i,direction=sign,section_in_half_pi=1,
        launch_u=str(F(int(args.endpoint[3:]),1000)),packet_sha256=args.checksum,lean_version=args.version,
        import_paths=[str(root)],central_group=[a,b],signed_grouped_central_parents=deps,package=PACKAGE)
    checked_parents(item,root,args.version)
    return item


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=LABELS,required=True)
    p.add_argument('--span',nargs=2,type=int,required=True,metavar=('FIRST','STOP'))
    p.add_argument('--rows',type=int,nargs='+')
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-grouped-central')
    p.add_argument('--handoff',type=Path)
    p.add_argument('--output',required=True,type=Path)
    args=p.parse_args()
    a,b=args.span
    indices=args.rows if args.rows is not None else range(a,b)
    if not 0<=a<b<=391 or len(set(indices))!=len(indices) or any(not a<=i<b for i in indices):
        p.error('choose distinct rows in a valid original span')
    packet,directions=data(args.endpoint,a,b)
    args.checksum=digest(packet)
    args.cache=args.cache.resolve()
    for sign,(_,_,rows) in directions.items():
        for i,(_,_,_,_,ratio) in rows.items():
            if ratio>1:
                raise ValueError(f'original signed allowance failed at {i} direction {sign}: {ratio}')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path=lake('printenv','LEAN_PATH')
    args.version=lake('lean','--version')
    parents={}
    for sign,(ins,models,_) in directions.items():
        parents[sign]=group_fields(stem(args.endpoint,sign,a,b),ins,models,args)
        m=parents[sign][-1][1]
        print(f'{m["module"]}: {m["key"]} in {m["wall_seconds"]} seconds',flush=True)
    if args.fields_only:
        save(args.output,[{k:v for k,v in ps[-1][1].items() if k!='artifacts'} for ps in parents.values()])
        return
    results=[]
    for i in indices:
        records=[row_proof(args,a,b,i,sign,directions[sign][2][i],parents[sign]) for sign in (1,-1)]
        results.extend(records)
        source=Path(records[0]['import_paths'][0])/'signed-row.json'
        save(source,records)
        if args.handoff:
            install(records,source,args.handoff)
        save(args.output,results)
        print(f'{args.endpoint} row {i} original signed central defects accepted',flush=True)


if __name__=='__main__':
    main()
