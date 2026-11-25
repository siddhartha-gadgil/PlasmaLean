"""Construct projected trial rectangles for the signed radius intervals and screen shared jets."""
import argparse
from fractions import Fraction as F

from bounce_mirror_pilot import Model, evaluate
from bounce_phase_frame import FRAME_SCALE
from endpoint_reflected_trials import TrialPair
from screen_endpoint_jacobian_sharing import first_failure, native_jet
from screen_projected_jacobians import projected_radii
from screen_reflected_reference import conjugate
from verify_grouped_endpoint_jacobians import restricted, tube
from verify_harmonic_group_exclusion import harmonics
from verify_radial_ribbon_packets import load


def trial(rows, k, i):
    backward,forward = (rows[k,sign][i] for sign in (-1,1))
    identity = [[FRAME_SCALE,0],[0,FRAME_SCALE]]
    lf = rows[k,1][i-1]["frame_end"] if i else identity
    lb = rows[k,-1][i-1]["frame_end"] if i else identity
    if lf != conjugate(lb) or forward["frame_end"] != conjugate(backward["frame_end"]):
        raise ValueError(f"tile {k}, row {i} frames do not reflect")
    if forward["coefficients"] != [backward["coefficients"][0],[-v for v in backward["coefficients"][1]]]:
        raise ValueError(f"tile {k}, row {i} central trajectory does not reflect")
    fr,br = [projected_radii(frame,row["frame_end"],row["frame_trial_radius"])
             for frame,row in [(lf,forward),(lb,backward)]]
    widths = tuple(map(max,zip(fr,br,strict=True)))
    mu = min(F(forward["log_norm_upper"]),F(backward["log_norm_upper"]))
    return TrialPair(i,lf,forward,lb,backward,fr,br,(0,0),widths,mu)


def projected_group(rows, ks, start, stop):
    if (not ks or len(set(ks))!=len(ks) or not set(ks)<=set(range(4))
            or not 0<=start<stop<=min(len(rows[k,s]) for k in ks for s in (-1,1))):
        raise ValueError('choose distinct radial intervals and an available nonempty group')
    pairs = [[trial(rows,k,i) for i in range(start,stop)] for k in ks]
    boxes = [tube(g) for g in pairs]
    # The enclosing polynomial is the arithmetic mean coefficient by coefficient.
    # Each time model receives its full l1 difference plus its own uniform radius.
    result = []
    for col in zip(*boxes,strict=True):
        center=[sum(values)//len(values) for values in zip(*(m.a for m in col),strict=True)]
        radius=max(m.e+sum(abs(x-y) for x,y in zip(center,m.a,strict=True)) for m in col)
        result.append(Model(center,radius))
    r,z,c,s=result
    angular=harmonics(c,s)
    models=[evaluate(channel,(r,z),angular)[0] for cells in native_jet() for channel in cells]
    fails=[]
    for k,g in zip(ks,pairs,strict=True):
        for p in g:
            panel=first_failure(restricted(models,start,stop,p.index),p)
            if panel is not None:
                fails.append((k,p.index,panel))
    return pairs,result,models,fails


if __name__=="__main__":
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ribbon",required=True,type=Path)
    ap.add_argument("--span",required=True,nargs=2,type=int)
    ap.add_argument("--tiles",nargs="+",type=int,default=list(range(4)))
    a=ap.parse_args()
    _,r=load(a.ribbon)
    *_,fail=projected_group(r,a.tiles,*a.span)
    print(f"tiles {a.tiles}, span {a.span}, failures {fail}")
