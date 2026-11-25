"""Partition the complete signed radius ribbon into exact shared spatial Jacobian checks."""
import argparse
from pathlib import Path

from radial_ribbon_jacobians import projected_group
from ribbon_central_data import LENGTH,WITNESS_SHA
from verify_physical_trace_slabs import digest,save
from verify_radial_ribbon_packets import load


def groups(rows,tiles,a,b):
    *_,bad=projected_group(rows,tiles,a,b)
    if not bad:
        yield dict(tiles=tiles,span=[a,b])
    elif b>a+1:
        m=(a+b)//2
        yield from groups(rows,tiles,a,m)
        yield from groups(rows,tiles,m,b)
    elif len(tiles)>1:
        n=len(tiles)//2
        yield from groups(rows,tiles[:n],a,b)
        yield from groups(rows,tiles[n:],a,b)
    else:
        raise ValueError(f'the original projected signed trial fails at {bad}')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--span',nargs=2,type=int,default=[0,LENGTH])
    p.add_argument('--size',type=int,default=8)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    lo,hi=a.span
    if not 0<=lo<hi<=LENGTH or a.size<1 or digest(a.ribbon)!=WITNESS_SHA:
        p.error('use a positive chunk size and an original interval')
    _,rows=load(a.ribbon)
    result=[]
    for start in range(lo,hi,a.size):
        result.extend(groups(rows,list(range(4)),start,min(start+a.size,hi)))
        save(a.output,dict(ribbon=WITNESS_SHA,span=[lo,hi],size=a.size,groups=result))
    covered=[(k,i) for g in result for k in g['tiles'] for i in range(*g['span'])]
    if sorted(covered)!=[(k,i) for k in range(4) for i in range(lo,hi)]:
        raise ValueError('missing or duplicated signed ribbon row')
    print(f'{len(result)} shared jets cover {len(covered)*2} signed physical trials',flush=True)


if __name__=='__main__':
    main()
