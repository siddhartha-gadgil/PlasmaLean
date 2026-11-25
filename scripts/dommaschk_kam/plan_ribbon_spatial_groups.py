"""Partition the complete signed radius ribbon into exact shared spatial Jacobian checks."""
import argparse
from functools import lru_cache
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


def partition(rows,lo,hi):
    """Minimize evaluated rectangles over all bisections of this time/radius block."""
    @lru_cache(None)
    def choose(tiles,a,b):
        *_,bad=projected_group(rows,tiles,a,b)
        if not bad:
            return [(tiles,a,b)]
        choices=[]
        if a+1<b:
            cut=(a+b)//2
            choices.append(choose(tiles,a,cut)+choose(tiles,cut,b))
        if len(tiles)>1:
            cut=len(tiles)//2
            choices.append(choose(tiles[:cut],a,b)+choose(tiles[cut:],a,b))
        if not choices:
            raise ValueError(f'original signed projected trial exceeds its rate at {bad}')
        return min(choices,key=len)
    return [dict(tiles=list(ks),span=[a,b]) for ks,a,b in choose(tuple(range(4)),lo,hi)]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--span',nargs=2,type=int,default=[0,LENGTH])
    p.add_argument('--size',type=int,default=8)
    p.add_argument('--partition-from',type=int,help='keep earlier groups and optimize later pairs of time blocks')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    lo,hi=a.span
    if (not 0<=lo<hi<=LENGTH or a.size<1 or digest(a.ribbon)!=WITNESS_SHA or
            a.partition_from is not None and ((a.partition_from-lo)%(2*a.size) or not lo<=a.partition_from<hi)):
        p.error('use a positive chunk size and an original interval')
    _,rows=load(a.ribbon)
    result=[]
    start=lo
    while start<hi:
        opt=a.partition_from is not None and start>=a.partition_from
        stop=min(hi,start+(2 if opt else 1)*a.size)
        original=[g for at in range(start,stop,a.size)
                  for g in groups(rows,list(range(4)),at,min(at+a.size,stop))]
        chosen=min((original,partition(rows,start,stop)),key=len) if opt else original
        result.extend(chosen)
        start=stop
    save(a.output,dict(ribbon=WITNESS_SHA,span=[lo,hi],size=a.size,groups=result))
    covered=[(k,i) for g in result for k in g['tiles'] for i in range(*g['span'])]
    if sorted(covered)!=[(k,i) for k in range(4) for i in range(lo,hi)]:
        raise ValueError('missing or duplicated signed ribbon row')
    print(f'{len(result)} shared jets cover {len(covered)*2} signed physical trials',flush=True)


if __name__=='__main__':
    main()
