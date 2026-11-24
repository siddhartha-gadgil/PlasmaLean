"""Find full-slab and time-panel certificates below the first q0r470 mirror height."""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import json
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS, Model, ORDER, R0M, ZERO, angle_models
from emit_sparse_taylor_slab import RECORD, models
from screen_sparse_reference_defects import bounds, sparse_fields


def gap_model(radius,z,cosine,sine):
    d,nr,nz=(sum(models(terms,(radius-R0M,z,cosine,sine)),ZERO) for terms in sparse_fields())
    r2=radius*radius
    r4=r2*r2
    h8=Model.rational(HEIGHTS[0])*(r4*r4)
    rd=radius*d
    return (rd-h8)*(rd+h8)+nr*nr+nz*nz


def as_constant(lo,hi,count):
    scale=count**ORDER
    lo,hi=lo//scale,-(-hi//scale)
    mid=(lo+hi)//2
    return Model([mid],max(mid-lo,hi-mid))


def classify(index,back,forward):
    out=max(s['physical_radius_out'] for s in (back,forward))
    trial=forward['physical_trial_radius']
    if out>trial:
        raise ValueError('original forward trial box does not contain both certified outgoing tubes')
    if back['coefficients'] != [forward['coefficients'][0],[-x for x in forward['coefficients'][1]]]:
        raise ValueError('the signed centers do not reflect')
    angles=angle_models(F(2*index+1,128),F(1,128),F(0))
    for method,e in [('forward_trial',trial),('physical_out',out)]:
        r,z=(Model(c,e) for c in forward['coefficients'])
        g=gap_model(r,z,angles[2],angles[1])
        for count in (1,2,4,8):
            hi=max(h for _,h in bounds(g,count))
            if hi<0:
                return method,count,1
    a,*tail=forward['coefficients'][0]
    halves=[]
    for lo,hi in ((-out,0),(0,out)):
        mid=(lo+hi)//2
        radial=Model([a+mid,*tail],max(mid-lo,hi-mid))
        halves.append(gap_model(radial,z,angles[2],angles[1]))
    if all(g.bound()[1]<0 for g in halves):
        return 'radial_bisection',1,2
    for count in (2,4,8,16,32,64,128,256):
        enclosure=[bounds(m,count) for m in (r,z,angles[2],angles[1])]
        for boxes in zip(*enclosure,strict=True):
            a,b,c,s=[as_constant(lo,hi,count) for lo,hi in boxes]
            radial=Model([a.a[0],a.e])
            if gap_model(radial,b,c,s).bound()[1] >= 0:
                break
        else:
            return 'radial_parameter',count,1
    return 'unresolved',0,0


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--range',type=int,nargs=2,default=(0,315),metavar=('FIRST','LAST'))
    args=parser.parse_args()
    lo,hi=args.range
    if not 0<=lo<=hi<316:
        parser.error('the strict lower-height prefix uses rows 0–315')
    p=json.loads(gzip.decompress(RECORD.read_bytes()))
    if p['section_in_half_pi']!=0 or p['launch_u']!='47/100':
        raise ValueError('wrong witness')
    b,f=(t['steps'] for t in p['traces'])
    data=[{'index':i,'method':m,'time_panels':n,'radial_pieces':k} for i in range(lo,hi+1)
          for m,n,k in [classify(i,b[i],f[i])]]
    print(Counter((row['method'],row['time_panels'],row['radial_pieces']) for row in data))
    print('refinements:',[r for r in data if r['method']!='forward_trial'])
    if args.output:
        args.output.write_text(json.dumps(data,indent=2)+'\n')
