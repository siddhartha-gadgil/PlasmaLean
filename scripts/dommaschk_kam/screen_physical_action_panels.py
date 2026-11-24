"""Test the two original Q0R470 action columns on a full physical time panel."""
import argparse
from fractions import Fraction as F
import gzip
from itertools import islice
import json
import re

from bounce_mirror_pilot import HEIGHTS, Model, ORDER, R0M, SCALE, ZERO
from emit_sparse_taylor_slab import DEST, RECORD, models
from screen_sparse_reference_defects import bounds, sparse_fields
from verify_pre_mirror_signs import inputs


def packed_rows():
    src=(DEST/'DommaschkActionQ0R470.lean').read_text()
    rows=[int(x,16) for x in re.findall(r'^  ⟨0x([0-9a-fA-F]+),',src,re.MULTILINE)]
    if len(rows)!=650:
        raise ValueError('expected 325 backward and 325 forward blocks')
    return rows


def panel_models(rad,fields,density,speed_sq):
    den,nr,nz=fields
    h=Model.rational(HEIGHTS[1]-speed_sq/2)
    a=Model.rational(density)
    r2=rad*rad
    r4=r2*r2
    hr8=h*(r4*r4)
    rd=rad*den
    transverse=nr*nr+nz*nz
    density_margin=((a-rad)*(a+rad))*(den*den)-transverse
    speed_margin=(rd-hr8)*(rd+hr8)+transverse
    return den,density_margin,speed_margin


def radial_parameter_panel(radius,coords,n):
    """Enclose the time panel first and retain the physical radius as a shared variable."""
    def box(m):
        lo,hi=next(islice(bounds(m,48),n,None))
        lo,hi=lo//48**ORDER,-(-hi//48**ORDER)
        return Model([(lo+hi)//2],(hi-lo+1)//2)
    center=box(radius)
    radial=Model([center.a[0],center.e])
    return radial,(radial-R0M,*map(box,coords[1:]))


def screen(args):
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    back,fwd=[t['steps'] for t in packet['traces']]
    rows=packed_rows()
    out=[]
    for i in args.rows:
        radius_error=max(b[i]['physical_radius_out'] for b in (back,fwd))
        rad,cols=inputs(fwd[i],i,radius_error,radius_error)
        fields=[sum(models(term,cols),ZERO) for term in sparse_fields()]
        for rev in (False,True):
            packed=rows[324-i if rev else 325+i]
            for n in args.panels:
                idx=47-n if rev else n
                p=(packed>>(72*idx))%(1<<72)
                density_ticks=p%(1<<24)
                speed_ticks=(p>>24)%(1<<24)
                density,squared=F(density_ticks,2**20),F(speed_ticks,2**26)
                margins=panel_models(rad,fields,density,squared)
                lo=[F(next(islice(bounds(m,48),n,None))[0],SCALE*48**ORDER) for m in margins]
                radial,coordinates=radial_parameter_panel(rad,cols,n)
                radial_fields=[sum(models(term,coordinates),ZERO) for term in sparse_fields()]
                shared=[m.bound()[0] for m in panel_models(radial,radial_fields,density,squared)]
                out.append(dict(row=i,back=rev,panel=n,density_ticks=density_ticks,
                                speed_squared_ticks=speed_ticks,den_pos=float(lo[0]),
                                density_margin=float(lo[1]),speed_margin=float(lo[2]),
                                passes=min(lo)>=0,radial_margins=list(map(float,shared)),
                                radial_passes=min(shared)>=0))
    return out


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rows',nargs='+',type=int,default=[0,324],choices=range(325),metavar='0..324')
    p.add_argument('--panels',nargs='+',type=int,default=[0,47],choices=range(48),metavar='0..47')
    for row in screen(p.parse_args()):
        print(json.dumps(row))
