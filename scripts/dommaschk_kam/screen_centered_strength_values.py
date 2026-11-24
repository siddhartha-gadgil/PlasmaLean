"""Screen the same center models, rounded gradient bounds and cross product as the Lean replay."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from math import ceil
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS, Model, SCALE, ZERO, angle_models, evaluate, polynomial_data
from emit_sparse_taylor_slab import models
from screen_sparse_jacobians import field_jet
from verify_centered_strength import DROP, HEIGHT
from verify_physical_trace_slabs import digest
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import joint_row


@lru_cache(maxsize=1)
def reference_fields():
    return [g[0] for g in polynomial_data()]


def centered_side(i, traces):
    r,cols,_=joint_row(i,traces)
    (d,du,dz),(n,nu,nz),(w,wu,wz)=[[sum(models(p,cols),ZERO) for p in g] for g in field_jet()]
    r2=r*r
    r4=r2*r2
    r8=r4*r4
    r16=r8*r8
    r6=r2*r4
    shifted=d-Model.rational(HEIGHTS[0])*(r*r6)
    shifted_r=du-Model.rational(7*HEIGHTS[0])*r6
    radial=(r2*d*(r*shifted_r-shifted.integer(7))).integer(2)
    radial+=r*(n*nu+w*wu).integer(2)-(n*n+w*w).integer(16)
    vertical=(r2*d*dz).integer(2)+(n*nz+w*wz).integer(2)
    rates=[]
    for numerator,denominator in [(radial,r16*r),(vertical,r16)]:
        lower=denominator.bound()[0]
        if lower<=0:
            raise ValueError(f'gradient denominator reaches zero on row {i}')
        rates.append(F(ceil(10**7*max(map(abs,numerator.bound()))/lower),10**7))
    waves=angle_models(F(2*i+1,128),F(1,128),F(0))
    radius,z=Model(r.a),Model(cols[1].a)
    d,n,w=[evaluate(p,[radius,z],waves)[0] for p in reference_fields()]
    rd=radius*d
    power=radius
    for _ in range(4):
        power=power*power
    return power,rd*rd+n*n+w*w,F(r.e,SCALE)*sum(rates)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rows',nargs=2,type=int,default=[0,324],metavar=('FIRST','LAST'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    first,last=args.rows
    if not 0<=first<=last<391:
        parser.error('choose a closed row range from 0 through 390')
    inputs=[load(k) for k in (470,478)]
    proof_rates=[]
    for i in range(first,last+1):
        (p,u,e),(q,v,f)=[centered_side(i,s[2]) for s in inputs]
        margin=(u*q-v*p-Model.rational(2*HEIGHT*DROP+e+f)*(p*q)).bound()[0]
        proof_rates.append((i,margin))
    worst,minimum=min(proof_rates,key=lambda r:r[1])
    result=dict(status='external exact arithmetic',rows_inclusive=[first,last],canonical_shift=str(2*HEIGHT*DROP),
                packet_hashes={p[0]:digest(p[1]) for p in inputs},minimum_margin=str(minimum),
                least_successful_row=worst,failed_rows=[i for i,m in proof_rates if m<=0])
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
