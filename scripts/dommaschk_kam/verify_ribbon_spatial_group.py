"""Prove physical spatial Jacobian bounds on several closed radial tiles and signed slabs."""
import argparse
from fractions import Fraction as F
from pathlib import Path

from bounce_mirror_pilot import R0M, angle_models
from grouped_profile_harmonics import prepare
from grouped_trial_jacobian_rows import ADAPTER, restrict_source
from radial_ribbon_jacobians import projected_group
from ribbon_central_data import LENGTH, WITNESS_SHA, label
from screen_endpoint_jacobian_sharing import own_models
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_grouped_endpoint_jacobians import FIELDS, restricted, shared_jet
from verify_horner_endpoint_jacobian import JACOBIAN, TAGS, endpoint_modules, inputs_source
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_packets import load


def spatial_sources(tile, pairs, group, models, providers, start, stop, integer_frame=False):
    declarations = []
    claims = {}
    for pair in pairs:
        i = pair.index
        stem = group+f'Tile{tile}Row{i:03}'
        r,z = own_models(pair)
        waves = angle_models(F(2*i+1,128),F(1,128),F(0))
        inp = inputs_source(stem+'Input',i,(r,r-R0M,z,waves),0)
        jet = restricted(models,start,stop,i)
        local = restrict_source(stem+'Restricted',inp[0],group,providers,jet,
                                F(2*i+1-start-stop,stop-start),F(1,stop-start))
        matrix = endpoint_modules(label(tile),pair,jet,[local[0]+'.'+t for t in TAGS],inp[0],
                                  field_imports=[ADAPTER+'.'+local[0]],integer_frame=integer_frame)
        declarations.extend([inp,local,*matrix])
        claims[i] = (matrix[-1][0],matrix[-1][2][:3])
    return declarations,claims


def fuse(declarations):
    """Preserve the original namespace and scoped options of each generated source."""
    names = {n for n,_,_ in declarations}
    imports = []
    sections = []
    for name,source,_ in declarations:
        lines = source.splitlines()
        at = next(i for i,line in enumerate(lines) if line.startswith('namespace '))
        header = []
        for line in lines[:at]:
            if line.startswith(('import ','public import ')):
                imported = line.split()[-1]
                if imported.rsplit('.',1)[-1] not in names and imported not in imports:
                    imports.append(imported)
            elif line.startswith(('open ','set_option ')):
                header.append(line)
        sections.append('\n'.join(['section',*header,*lines[at:],'end']))
    return ('module\n'+''.join('public import '+m+'\n' for m in imports)+
            '\n@[expose] public section\nnoncomputable section\n'+'\n'.join(sections)+'\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--span',nargs=2,type=int,required=True)
    p.add_argument('--tiles',nargs='+',type=int,default=list(range(4)))
    p.add_argument('--prove-tiles',nargs='+',type=int)
    p.add_argument('--rows',nargs='+',type=int)
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--dyadic',action='store_true',help='use kernel checked integer Horner multiply-adds')
    p.add_argument('--integer-frame',action='store_true',
                   help='use integer matrix witnesses and the smallest sufficient dyadic time cover')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/ribbon-spatial-checks')
    p.add_argument('--handoff',type=Path,default=ROOT/'.lake/ribbon-spatial-campaign')
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    a,b=args.span
    tiles=sorted(set(args.tiles))
    selected=sorted(set(args.prove_tiles or tiles))
    indices=sorted(set(args.rows or range(a,b)))
    if (not 0<=a<b<=LENGTH or not set(indices)<=set(range(a,b)) or not set(tiles)<=set(range(4))
            or not set(selected)<=set(tiles) or digest(args.ribbon)!=WITNESS_SHA):
        p.error('choose signed rows and tiles in the authenticated radius packet')
    _,source=load(args.ribbon)
    pairs,box,candidate,failures=projected_group(source,tiles,a,b)
    if failures:
        raise ValueError(f'projected matrix enclosure exceeds original budgets at {failures}')
    env(args)
    args.keys=[[WITNESS_SHA],args.version]
    args.cache=args.cache.resolve()
    prepare(args)
    stem='DommaschkRibbonSpatial'+''.join(map(str,tiles))+f'Span{a:03}To{b:03}'
    if args.dyadic:
        from verify_ribbon_dyadic_jet import dyadic_jet
        fields,models,providers=dyadic_jet(stem,box,args)
    else:
        fields,models,providers=shared_jet(stem,box,args)
    if any(x.a!=y.a or x.e!=y.e for x,y in zip(models,candidate,strict=True)):
        raise ValueError('physical proof models differ from the screened enclosure')
    print(f'{stem} physical fields {fields[1]["key"]}',flush=True)
    if args.fields_only:
        save(args.output,{k:v for k,v in fields[1].items() if k!='artifacts'})
        return
    parents=[*args.native_static,fields]
    links=union(args.cache,parents)
    results=[]
    for k,g in zip(tiles,pairs,strict=True):
        if k not in selected:
            continue
        group=[r for r in g if r.index in indices]
        decls,claims=spatial_sources(k,group,stem,models,providers,a,b,args.integer_frame)
        name=stem+f'Tile{k}Rows{indices[0]:03}To{indices[-1]+1:03}'
        source=fuse(decls)
        static=[line.removeprefix('public import PlasmaLean.Design.')
                for line in source.splitlines() if line.startswith('public import PlasmaLean.Design.')]
        traces=[digest(DESIGN/(m+'.trace')) for m in static]
        audits=['PlasmaLean.Design.'+ns+'.'+t for ns,checks in claims.values() for t in checks]
        root,receipt=compile_modules(args.cache/name,[(name,source,[])],[links],
            [WITNESS_SHA,args.version,traces,[r['key'] for _,r in parents]],args,JACOBIAN,qualified_claims=audits)
        for pair in group:
            i=pair.index
            rec={key:v for key,v in receipt.items() if key!='artifacts'}
            rec.update(module=claims[i][0],namespace=claims[i][0],import_module=name,package=JACOBIAN,
                tile=k,index=i,endpoint=label(k),paired_trials=True,common_rate=str(pair.common_rate),
                projected_radii=pair.common_radii,packet_sha256=WITNESS_SHA,
                import_paths=list(map(str,[root,links])),span=[a,b],field_key=fields[1]['key'])
            path=args.handoff/f'tile{k}'/'jacobians'/f'{i:03}.json'
            path.parent.mkdir(parents=True,exist_ok=True)
            save(path,rec)
            results.append(rec)
        save(args.output,results)
        print(f'{name} {receipt["key"]} {len(audits)} spatial claims',flush=True)


if __name__=='__main__':
    main()
