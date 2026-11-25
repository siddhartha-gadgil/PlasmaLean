"""Compare the signed central defect budgets to two ways of reusing the spatial trial jet."""
import argparse
from collections import Counter
from fractions import Fraction as F
import json
from pathlib import Path

from bounce_mirror_pilot import Model
from grouped_central_models import boxes,compress,field_models,quotient
from radial_ribbon_jacobians import projected_group
from ribbon_central_data import WITNESS_SHA,load as centers
from run_ribbon_physical_campaign import work
from screen_endpoint_jacobian_sharing import first_failure
from verify_grouped_endpoint_jacobians import restricted
from verify_physical_trace_slabs import save
from verify_radial_ribbon_packets import load


def summary(records):
    records.sort()
    def result(item):
        ratio,src,dst,index=item
        return dict(ratio=str(ratio),base_tile=src,target_tile=dst,index=index)
    return dict(tests=len(records),passing=sum(score<=1 for score,*_ in records),
        best=result(records[0]),middle=result(records[len(records)//2]),worst=result(records[-1]))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',required=True,type=Path)
    p.add_argument('--plan',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    args=p.parse_args()
    plan=json.loads(args.plan.read_text())
    work(plan)
    _,rows=load(args.ribbon)
    center=centers(args.ribbon)
    direct,transfer=[],[]
    panel_counts=Counter()
    for group in plan['groups']:
        a,b=group['span']
        tiles=group['tiles']
        pairs,_,models,failed=projected_group(rows,tiles,a,b)
        if failed:
            raise ValueError(f'inadmissible source trial jet: {failed}')
        for i in range(a,b):
            jet=restricted(models,a,b,i)
            for branch in pairs:
                pair=branch[i-a]
                count=next(n for n in (1,2,4,8) if first_failure(jet,pair,panels=n) is None)
                panel_counts[count]+=1
            # Give the base center its own full-precision field evaluation on this single row.
            base={k:[compress(m,i,i,i+1) for m in field_models(boxes([center[k,1][i]]))] for k in tiles}
            curves={k:[Model(v) for v in center[k,1][i][3]] for k in tiles}
            for dst in tiles:
                actual=center[dst,1][i]
                budget=min(F(actual[6]),F(center[dst,-1][i][6]))
                direct.append((quotient(actual,[g[0] for g in jet])[2]/budget,dst,dst,i))
                for src in tiles:
                    if src==dst:
                        continue
                    dr,dz=[x-y for x,y in zip(curves[dst],curves[src],strict=True)]
                    # The group rectangle contains the line segment between the two centers.
                    estimates=[v+grad[1]*dr+grad[2]*dz for v,grad in zip(base[src],jet,strict=True)]
                    transfer.append((quotient(actual,estimates)[2]/budget,src,dst,i))
    result=dict(ribbon=WITNESS_SHA,spatial_groups=len(plan['groups']),direct=summary(direct),
                first_order=summary(transfer),panels=dict(sorted(panel_counts.items())))
    save(args.output,result)
    for name in ('direct','first_order'):
        r=result[name]
        print(f'{name}: {r["passing"]} of {r["tests"]} fit, nearest ratio {float(F(r["best"]["ratio"])):.6f}')


if __name__=='__main__':
    main()
