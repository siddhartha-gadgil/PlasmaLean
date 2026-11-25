"""Check that integer Horner proofs enclose the same nine QA2R fields on a shared radial group."""
import argparse
from pathlib import Path

from grouped_profile_harmonics import prepare
from radial_ribbon_jacobians import projected_group
from ribbon_central_data import WITNESS_SHA
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_grouped_endpoint_jacobians import FIELDS
from verify_harmonic_group_exclusion import inputs
from verify_horner_endpoint_jacobian import DATA
from verify_native_action_models import emit_horner_field
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_radial_ribbon_packets import load


def dyadic_jet(stem,box,args):
    item,coordinates=inputs(stem+'Inputs',box)
    terms=[item]
    models=[]
    names=[]
    for tag,symbol,_,channels,(_,sta) in args.native_data:
        decl,model=emit_horner_field(stem+tag,symbol,channels,coordinates,sta['module'],item[0],
                                     DATA,FIELDS,integer=True)
        terms.append(decl)
        names.append(decl[0])
        models.append(model)
    name=stem+'Fields'
    src='module\n'+''.join('public import '+FIELDS+'.'+field+'\n' for field in names)
    terms.append((name,src,[]))
    key=[FIELDS,args.keys,[r['key'] for _,r in args.native_static],
         *[digest(DESIGN/(m+'.trace')) for m in ('DommaschkGroupedHarmonicGap','DommaschkDyadicHorner')]]
    result=compile_modules(args.cache/name,terms,[args.native_links],key,args,FIELDS)
    return result,models,names


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--span',nargs=2,type=int,required=True)
    p.add_argument('--tiles',nargs='+',type=int,default=list(range(4)))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/ribbon-spatial-checks')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if digest(a.ribbon)!=WITNESS_SHA:
        p.error('expected the authenticated four-ribbon packet')
    _,rows=load(a.ribbon)
    tiles=sorted(a.tiles)
    lo,hi=a.span
    _,box,expected,failures=projected_group(rows,tiles,lo,hi)
    if failures:
        raise ValueError(f'original row rate exceeded on {failures}')
    env(a)
    a.keys=[[WITNESS_SHA],a.version]
    prepare(a)
    stem='DommaschkRibbonSpatial'+''.join(map(str,tiles))+f'Span{lo:03}To{hi:03}'
    (root,receipt),models,names=dyadic_jet(stem,box,a)
    if any((m.a,m.e)!=(e.a,e.e) for m,e in zip(models,expected,strict=True)):
        raise ValueError('the integer proof encloses different field polynomials from the exact spatial screen')
    result={k:v for k,v in receipt.items() if k!='artifacts'}
    result.update(ribbon=WITNESS_SHA,span=[lo,hi],tiles=tiles,fields=names,
        import_paths=list(map(str,[root,a.native_links])))
    save(a.output,result)
    print(f'{receipt["key"]} {receipt["wall_seconds"]} seconds for nine fields',flush=True)


if __name__=='__main__':
    main()
