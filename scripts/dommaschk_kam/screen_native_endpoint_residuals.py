"""Retest both signed section-zero central defects with one harmonic Horner jet on the exact centre."""

import argparse
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path

from bounce_mirror_pilot import Model, SCALE, angle_models, evaluate
from bounce_phase_frame import affine_frame
from screen_endpoint_jacobian_sharing import native_jet
from screen_reflected_reference import paired_jobs
from screen_sparse_reference_defects import enclosing_box
from verify_physical_trace_slabs import RECORD


def sharp_budget(x, y, den):
    """Round the certified quotient norm up to the next 2⁻⁸⁰ tick."""
    square = F((x*x + y*y)*SCALE*SCALE, den*den)
    return F(isqrt(square.numerator // square.denominator) + 1, SCALE)


def residual_data(forward):
    _,_,i,coords,left,right,_,count=forward
    r,z=map(Model,coords)
    phase=angle_models(F(2*i+1,128),F(1,128),F(0))
    d,nr,nz=[evaluate(g[0],(r,z),phase)[0] for g in native_jet()]
    def slope(m):
        return Model([128*(j+1)*q for j,q in enumerate(m.a[1:])])
    vr,vz=nr-slope(r)*d,nz-slope(z)*d
    _,_,adj,det,_=affine_frame(left,right,F(1,64))
    x,y=[a*vr+b*vz for a,b in adj]
    den=det*d
    nx,ny,lo=enclosing_box([x,y],den,count)
    if lo<=0:
        raise ValueError('the central quotient denominator is not positive')
    return (r,z,phase),(d,nr,nz),(x,y,den),(nx,ny,lo)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=['q0r470','q0r478','q0r523','q0r531'],required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    packet=RECORD.with_name(f'bounce_frame_{a.endpoint[:2]}_u{a.endpoint[3:]}.json.gz')
    rows=[]
    for f,b in paired_jobs(packet):
        _,_,_,(x,y,d)=residual_data(f)
        square=F(x*x+y*y,d*d)
        limit=min(F(f[6]),b)
        rounded = sharp_budget(x, y, d)
        rows.append({'index':f[2], 'fits':rounded <= limit, 'square_ratio':str(square/limit**2),
                     'rounded_ratio':str(rounded/limit)})
    a.output.write_text(json.dumps(rows,indent=2)+'\n')


if __name__=='__main__':
    main()
