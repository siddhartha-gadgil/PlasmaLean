"""Screen shared spatial models and time groups against signed original action columns."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
from types import SimpleNamespace

from bounce_mirror_pilot import HEIGHTS, Model, ORDER, SCALE, ZERO
from emit_sparse_taylor_slab import RECORD, ROOT, models
from screen_physical_action_panels import packed_rows
from screen_sparse_reference_defects import horner_weights, sparse_fields
from verify_physical_action_launch_blocks import compensated_terms
from verify_pre_mirror_signs import inputs, jacobian


def panel_lower(m,groups,j):
    coefficients=m.a+[0]*(ORDER+1-len(m.a))
    weights=horner_weights(groups,ORDER)[j]
    low=0
    for k in reversed(range(ORDER+1)):
        shifted=sum(x*y for x,y in zip(coefficients[k:],weights[k],strict=True))
        low=shifted+min(low,0)
    return F(low-m.e*groups**ORDER,SCALE*groups**ORDER)


def screen(i,b,f,blocks,spatial,temporal,*,outgoing=False):
    e=max(b[i]['physical_radius_out'],f[i]['physical_radius_out'])
    physical=None if outgoing else jacobian(SimpleNamespace(jacobian_cache=ROOT/'.lake/jacobian-checks'),i,f[i],e)
    if physical:
        _,whole,provider=physical[:3]
    else:
        _,whole=inputs(f[i],i,e,e)
        provider='new outgoing field models'
    D,N,Z=[sum(models(t,whole),ZERO) for t in sparse_fields()]
    tran=N*N+Z*Z
    ticks=[]
    for j in range(48):
        codes=[(blocks[325+i]>>(72*j))%(1<<72),(blocks[324-i]>>(72*(47-j)))%(1<<72)]
        ticks.append((F(min(q%(1<<24) for q in codes),2**20),
                      F(min((q>>24)%(1<<24) for q in codes),2**26)))
    h=HEIGHTS[1]-min(g for _,g in ticks)/2
    shifted=compensated_terms(h)
    for k in spatial:
        boxes=[]
        for j in range(k):
            l=-e+2*e*j//k
            r=-e+2*e*(j+1)//k
            radius,cols=inputs(f[i],i,(r-l+1)//2,e,(l+r)//2)
            c=sum(models(shifted,cols),ZERO)
            r2=radius*radius
            r4=r2*r2
            r8=r4*r4
            boxes.append((radius,r8*r8,r2*c*(D.integer(2)-c)+N*N+Z*Z))
        for groups in temporal:
            passes=True
            minimum=None
            for j in range(groups):
                a,g=[min(s) for s in zip(*ticks[j*48//groups:(j+1)*48//groups])]
                density=Model.rational(a)
                factor=Model.rational(h*h-(HEIGHTS[1]-g/2)**2)
                for radius,r16,gap in boxes:
                    arc=((density-radius)*(density+radius))*(D*D)-tran
                    m=min(panel_lower(gap+r16*factor,groups,j),panel_lower(arc,groups,j))
                    minimum=m if minimum is None else min(m,minimum)
                    if m<0:
                        passes=False
                        break
                if not passes:
                    break
            if passes:
                return dict(row=i,provider=provider,radial_subintervals=k,time_groups=groups,
                            min_margin=str(minimum))
    return dict(row=i,provider=provider,unresolved=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    group=p.add_mutually_exclusive_group(required=True)
    group.add_argument('--rows',nargs='+',type=int,choices=range(325),metavar='0..324')
    group.add_argument('--range',nargs=2,type=int,metavar=('FIRST','LAST'))
    p.add_argument('--spatial',nargs='+',type=int,default=[1,2,4,5,8,16])
    p.add_argument('--time-groups',nargs='+',type=int,default=[1,2,4,8,12,24,48])
    p.add_argument('--output',type=Path)
    p.add_argument('--outgoing-fields',action='store_true',
                   help='evaluate all three polynomials afresh on the actual outgoing coordinate tube')
    a=p.parse_args()
    if any(k<=0 for k in a.spatial) or any(k<=0 or 48%k for k in a.time_groups):
        p.error('positive subdivisions and time group counts dividing 48 are required')
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    b,f=[t['steps'] for t in packet['traces']]
    blocks=packed_rows()
    out=[]
    if a.range and not 0<=a.range[0]<=a.range[1]<=324:
        p.error('the archive contains 325 signed rows')
    for i in a.rows if a.rows else range(a.range[0],a.range[1]+1):
        out.append(screen(i,b,f,blocks,a.spatial,a.time_groups,outgoing=a.outgoing_fields))
        print(json.dumps(out[-1]),flush=True)
        if a.output:
            a.output.write_text(json.dumps(out,indent=2)+'\n')
