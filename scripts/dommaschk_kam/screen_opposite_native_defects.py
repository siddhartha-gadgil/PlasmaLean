"""Retest each original signed central defect up to and including the first post-cap slab."""
import argparse
from fractions import Fraction
from pathlib import Path

from plan_endpoint_continuations import exterior
from screen_native_endpoint_residuals import residual_data,sharp_budget
from screen_sparse_reference_defects import jobs
from verify_endpoint_reference_slabs import ENDPOINTS,NATIVE_OPPOSITE_MARKER
from verify_physical_trace_slabs import RECORD,digest,save


def screen(label):
    _,cap=exterior(label)
    packet=RECORD.with_name(f'bounce_frame_q1_u{label[3:]}.json.gz')
    rows=[]
    for job in jobs(packet,8,False):
        _,sign,i,_,_,_,budget,_=job
        if i>cap:
            continue
        _,_,_,(x,y,den)=residual_data(job)
        ratio=sharp_budget(x,y,den)/Fraction(budget)
        rows.append(dict(index=i,direction=sign,ratio=str(ratio)))
    worst=max(rows,key=lambda r:Fraction(r['ratio']))
    return dict(endpoint=label,packet_sha256=digest(packet),length=cap+1,rows=rows,worst=worst,
                passed=sum(Fraction(r['ratio'])<=1 for r in rows))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',nargs='+',choices=ENDPOINTS[4:],default=ENDPOINTS[4:])
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--activate-campaign',type=Path,
        help='select this backend for future signed reference rows in each screened endpoint campaign')
    a=p.parse_args()
    results=[screen(label) for label in a.endpoints]
    save(a.output,results)
    if a.activate_campaign:
        if any(r['passed']!=2*r['length'] for r in results):
            p.error('one of the original signed allowances failed the native arithmetic screen')
        for r in results:
            base=a.activate_campaign/r['endpoint']
            base.mkdir(parents=True,exist_ok=True)
            save(base/NATIVE_OPPOSITE_MARKER,dict(endpoint=r['endpoint'],packet_sha256=r['packet_sha256'],
                                                  backend='independent-harmonic'))


if __name__=='__main__':
    main()
