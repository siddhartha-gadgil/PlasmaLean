"""Select intervals that fit both independently checked original opposite-section budgets."""
import argparse
from fractions import Fraction
from pathlib import Path

from grouped_central_models import DEGREE
from grouped_opposite_central import LABELS,data
from plan_endpoint_continuations import exterior
from verify_physical_trace_slabs import RECORD,digest,save

MARKER='opposite-grouped-central-plan.json'


def choose(label,a,b):
    _,directions=data(label,a,b)
    peaks={s:max((r[-1],i) for i,r in rows.items()) for s,(_,_,rows) in directions.items()}
    worst=max(t for t,_ in peaks.values())
    if worst<=1 or b-a==1:
        return [dict(start=a,stop=b,mode='grouped' if b-a>1 else 'singleton',ratio=str(worst),
                     signed_peaks={str(s):dict(ratio=str(t),index=i) for s,(t,i) in peaks.items()})]
    mid=(a+b)//2
    return choose(label,a,mid)+choose(label,mid,b)


def validate(plan,label):
    packet=RECORD.with_name(f'bounce_frame_q1_u{label[3:]}.json.gz')
    _,cap=exterior(label)
    if (label not in LABELS or plan['endpoint']!=label or plan['packet_sha256']!=digest(packet)
            or plan['target']!=cap+1 or plan['degree']!=DEGREE):
        raise ValueError('incorrect opposite-section reference packet, degree or target')
    start=0
    for g in plan['groups']:
        stop=g['stop']
        if not (start==g['start']<stop<=cap+1) or set(g['signed_peaks'])!={'1','-1'}:
            raise ValueError('incomplete opposite-section group')
        worst=max(Fraction(p['ratio']) for p in g['signed_peaks'].values())
        if (g['mode']!=('singleton' if stop-start==1 else 'grouped') or Fraction(g['ratio'])!=worst
                or worst>1 or any(not start<=p['index']<stop for p in g['signed_peaks'].values())):
            raise ValueError('unchecked original signed defect allowance')
        start=stop
    if start!=cap+1:
        raise ValueError('missing opposite-section exterior slab')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',choices=LABELS,nargs='+',default=LABELS)
    p.add_argument('--width',type=int,default=8)
    p.add_argument('--activate-campaign',type=Path)
    p.add_argument('--output',required=True,type=Path)
    args=p.parse_args()
    if not 2<=args.width<=24:
        p.error('choose a width from 2 to 24')
    result={}
    for label in args.endpoints:
        _,cap=exterior(label)
        groups=[]
        for a in range(0,cap+1,args.width):
            groups.extend(choose(label,a,min(a+args.width,cap+1)))
        packet=RECORD.with_name(f'bounce_frame_q1_u{label[3:]}.json.gz')
        plan=dict(endpoint=label,target=cap+1,packet_sha256=digest(packet),degree=DEGREE,groups=groups)
        validate(plan,label)
        result[label]=plan
        print(label,len(groups),'feasible groups on both original directions',flush=True)
    save(args.output,result)
    if args.activate_campaign:
        for label,plan in result.items():
            root=args.activate_campaign/label
            root.mkdir(parents=True,exist_ok=True)
            save(root/MARKER,plan)


if __name__=='__main__':
    main()
