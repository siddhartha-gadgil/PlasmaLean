"""Check grouped endpoint Jacobians and package their original individual signed matrix interfaces."""
from fractions import Fraction as F
from pathlib import Path

from bounce_mirror_pilot import R0M,angle_models
from grouped_trial_jacobian_rows import ADAPTER,handoff,restrict_source
from screen_endpoint_jacobian_sharing import own_models
from verify_backward_physical_prefix import compile_modules,union
from verify_grouped_endpoint_jacobians import restricted
from verify_horner_endpoint_jacobian import JACOBIAN,TAGS,endpoint_modules,inputs_source
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,digest,key_of,save
from verify_ribbon_spatial_group import fuse


PACKAGE='FusedEndpointSpatialCache'
MARKER='use-fused-spatial'


def declarations(stem,endpoint,a,b,branches,models,providers):
    section=int(endpoint[1])
    terms=[]
    matrices=[]
    for signed in branches:
        pair=signed[0][1]
        i=pair.index
        base=stem+f'Row{i:03}'
        r,z=own_models(pair)
        waves=angle_models(F(2*i+1,128),F(1,128),F(0))
        if section:
            waves=[w.integer((-1)**((j+1)//2)) for j,w in enumerate(waves)]
        inp=inputs_source(base+'Input',i,(r,r-R0M,z,waves),section)
        jet=restricted(models,a,b,i)
        res=restrict_source(base+'Restricted',inp[0],stem,providers,jet,F(2*i+1-a-b,b-a),F(1,b-a))
        terms.extend([inp,res])
        for sign,p in signed:
            docs=endpoint_modules(endpoint,p,jet,[res[0]+'.'+tag for tag in TAGS],inp[0],matrix_sign=sign,
                field_imports=[ADAPTER+'.'+res[0]],integer_frame=True)
            terms.extend(docs)
            matrices.append((sign,p,docs[-1][0],docs[-1][2]))
    return fuse(terms),matrices


def group_keys(source,checksum,version,parents):
    static=[line.removeprefix('public import PlasmaLean.Design.') for line in source.splitlines()
            if line.startswith('public import PlasmaLean.Design.')]
    return [PACKAGE,checksum,version,[digest(DESIGN/(m+'.trace')) for m in static],parents]


def original_interface(name,group,claims):
    return name,'module\npublic import '+PACKAGE+'.'+group+'\n',claims


def checked_roots(row,root,version):
    """Verify the canonical wrapper and the accepted field, matrix and grouping certificates."""
    label,i=row['endpoint'],row['index']
    a,b=row['fused_span']
    if not 0<=a<=i<b<=391:
        raise ValueError('different clock in fused spatial certificate')
    stem=f'Dommaschk{label.upper()}FusedTrial{a:03}To{b:03}'
    parents=row['fused_parents']
    prefix=['DommaschkHornerJetData'+tag for tag in TAGS]+[stem+'Fields']
    if [p['module'] for p in parents[:-1]]!=prefix or not parents[-1]['module'].startswith(stem+'Rows'):
        raise ValueError('wrong static physical input or fused group')
    data=[admitted(Path(p['root']),p['module'],p['key']) for p in parents]
    g=data[-1]
    ns=row['module']
    if not set(row['theorems']).issubset(g['theorems']):
        raise ValueError(f'missing real frame bound for {ns}')
    checksum=row['packet_sha256']
    src=(Path(parents[-1]['root'])/PACKAGE/(g['module']+'.lean')).read_text()
    group_common=group_keys(src,checksum,version,[r['key'] for r in data[:-1]])
    if g['key']!=key_of([group_common,[(g['module'],src,[])],g['theorems']]):
        raise ValueError('fused parent differs from the checked field jet')
    claims=[t.removeprefix('PlasmaLean.Design.'+ns+'.') for t in row['theorems']]
    wrapper=original_interface(ns,g['module'],claims)
    common=[JACOBIAN,version,checksum,g['key']]
    if (key_of([common,[wrapper]])!=row['key'] or
            (root/JACOBIAN/(ns+'.lean')).read_text()!=wrapper[1]):
        raise ValueError('individual signed namespace differs from the accepted original parent')
    return [Path(p['root']) for p in parents]


def finish(stem,a,b,branches,fields,models,providers,args):
    selected=set(args.rows or range(a,b))
    original=[row for row in branches if row[0][1].index in selected]
    output=[]
    parents=[*args.native_static,fields]
    links=union(args.cache,parents)
    checksum,version=args.keys[0][0],args.keys[1]
    for start in range(0,len(original),6):
        chunk=original[start:start+6]
        indices=[row[0][1].index for row in chunk]
        group=stem+f'Rows{indices[0]:03}To{indices[-1]+1:03}'+key_of(indices)[:8]
        src,matrices=declarations(stem,args.endpoint,a,b,chunk,models,providers)
        claim_list=['PlasmaLean.Design.'+ns+'.'+t for _,_,ns,claims in matrices for t in claims]
        result=compile_modules(args.cache/group,[(group,src,[])],[links],
            group_keys(src,checksum,version,[r['key'] for _,r in parents]),args,PACKAGE,
            qualified_claims=claim_list)
        active=[*parents,result]
        all_parents=[dict(module=p['module'],key=p['key'],root=str(r)) for r,p in active]
        overlay=union(args.cache,active)
        by_index={}
        for sign,p,ns,claims in matrices:
            term=original_interface(ns,group,claims)
            root,r=compile_modules(args.cache/ns,[term],[overlay],[JACOBIAN,version,checksum,result[1]['key']],
                                   args,JACOBIAN)
            rec={k:v for k,v in r.items() if k!='artifacts'}
            rec.update(endpoint=args.endpoint,section_in_half_pi=int(args.endpoint[1]),direction=1,index=p.index,
                launch_u=str(F(int(args.endpoint[3:]),1000)),paired_trials=True,projected_radii=p.common_radii,
                common_rate=str(p.common_rate),lean_version=version,packet_sha256=checksum,
                import_paths=[str(root)],fused_span=[a,b],fused_parents=all_parents)
            if sign is not None:
                rec['matrix_direction']=sign
            by_index.setdefault(p.index,[]).append(rec)
        for i,proofs in by_index.items():
            output.extend(proofs)
            save(args.output,output)
            if args.handoff:
                row=proofs[0]
                packet=Path(row['import_paths'][0])/'matrix-pair.json'
                save(packet,proofs)
                handoff(row,packet,args.handoff)
        print(f'{group}: {len(chunk)} original rows, {len(matrices)} signed matrices, {result[1]["key"]}',flush=True)
