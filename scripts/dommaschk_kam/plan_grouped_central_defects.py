"""Plan higher-order central groups and optionally select them in live phase-zero continuations."""
import argparse
from fractions import Fraction
from pathlib import Path

from plan_endpoint_continuations import exterior
from verify_grouped_central_defects import data
from verify_physical_trace_slabs import RECORD,digest,save

MARKER='grouped-central-plan.json'


def choose(label,a,b):
    _,_,_,rows=data(label,a,b)
    worst=max((r[-1],i) for i,r in rows.items())
    if worst[0]<=1 or b-a==1:
        return [dict(start=a,stop=b,worst_index=worst[1],ratio=str(worst[0]),
                     mode='grouped' if b-a>1 else 'singleton')]
    middle=(a+b)//2
    return choose(label,a,middle)+choose(label,middle,b)


def validate(plan,label):
    packet=RECORD.with_name(f'bounce_frame_q0_u{label[3:]}.json.gz')
    _,cap=exterior(label)
    if (plan['endpoint']!=label or plan['packet_sha256']!=digest(packet) or plan['target']!=cap+1 or
            plan['degree']!=12):
        raise ValueError('incorrect grouped central clock, packet or polynomial order')
    at=0
    for g in plan['groups']:
        if (g['start']!=at or not at<g['stop']<=cap+1 or g['mode'] not in ('grouped','singleton')
                or (g['mode']=='grouped' and Fraction(g['ratio'])>1)):
            raise ValueError('incomplete or infeasible grouped central plan')
        at=g['stop']
    if at!=cap+1:
        raise ValueError('missing the slab beyond the exterior cap')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',choices=('q0r523','q0r531'),nargs='+',default=('q0r523','q0r531'))
    p.add_argument('--width',type=int,default=8)
    p.add_argument('--activate-campaign',type=Path)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 2<=a.width<=24:
        p.error('choose a width from 2 to 24')
    result={}
    for label in a.endpoints:
        _,cap=exterior(label)
        packet=RECORD.with_name(f'bounce_frame_q0_u{label[3:]}.json.gz')
        groups=[]
        for i in range(0,cap+1,a.width):
            groups.extend(choose(label,i,min(i+a.width,cap+1)))
        plan=dict(endpoint=label,packet_sha256=digest(packet),target=cap+1,degree=12,groups=groups)
        validate(plan,label)
        result[label]=plan
    save(a.output,result)
    if a.activate_campaign:
        for label,plan in result.items():
            root=a.activate_campaign/label
            root.mkdir(parents=True,exist_ok=True)
            save(root/MARKER,plan)


if __name__=='__main__':
    main()
