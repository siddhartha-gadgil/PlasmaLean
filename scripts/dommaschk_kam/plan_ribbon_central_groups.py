"""Plan a contiguous cover of each widened ribbon by feasible central-field groups."""
import argparse
from pathlib import Path

from ribbon_central_data import LENGTH,WITNESS_SHA,data
from verify_physical_trace_slabs import save


def choose(source,tile,start,stop):
    _,_,rows=data(source,tile,start,stop)
    worst,i=max((row[-1],i) for i,row in rows.items())
    if worst<=1:
        return [dict(start=start,stop=stop,worst_index=i,ratio=str(worst))]
    if stop-start==1:
        raise ValueError(f'tile {tile} singleton {start} exceeds an original budget by a factor {worst}')
    mid=(start+stop)//2
    return choose(source,tile,start,mid)+choose(source,tile,mid,stop)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--width',type=int,default=8)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    if not 2<=args.width<=24:
        p.error('group width must be between 2 and 24')
    result={}
    for tile in range(4):
        groups=[]
        for start in range(0,LENGTH,args.width):
            groups.extend(choose(args.ribbon,tile,start,min(start+args.width,LENGTH)))
        result[tile]=groups
        print(f'tile {tile}: {len(groups)} groups, {LENGTH} original signed row pairs',flush=True)
    save(args.output,dict(witness=WITNESS_SHA,length=LENGTH,width=args.width,tiles=result))


if __name__=='__main__':
    main()
