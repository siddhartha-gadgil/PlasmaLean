"""Check joint rectangles for neighbouring launches against each launch's exact frame budgets."""

import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path

from bounce_mirror_pilot import Model, angle_models, evaluate, polynomial_data
from bounce_phase_frame import affine_frame, product
from endpoint_reflected_trials import paired_rows
from screen_sparse_reference_defects import bounds
from verify_physical_trace_slabs import RECORD


NEIGHBOURS = [('q0r470','q0r478'), ('q0r523','q0r531'),
              ('q1r456','q1r464'), ('q1r509','q1r517')]


@lru_cache(maxsize=1)
def native_jet():
    return polynomial_data()


def harmonic_jet(section, i, coordinates):
    phase = angle_models(F(2*i+1,128), F(1,128), F(0))
    if section:
        phase = [m.integer((-1)**((j+1)//2)) for j,m in enumerate(phase)]
    return [[evaluate(channel,coordinates,phase)[0] for channel in g] for g in native_jet()]


def frame_models(jet, pair):
    d, du, dz = jet[0]
    j = [[nx*d-n*dx for nx,dx in zip((nu,nz),(du,dz))] for n,nu,nz in jet[1:]]
    m, velocity, adj, det, _ = affine_frame(pair.forward_left,pair.forward['frame_end'],F(1,64))
    den_sq = d*d
    jm = product(j,m)
    a = product(adj, [[jm[i][k]-den_sq*velocity[i][k] for k in (0,1)] for i in (0,1)])
    return det*den_sq, a[0][0], a[1][1], a[0][1]+a[1][0]


def first_failure(jet, pair, panels=8):
    # All four interval endpoints use the same positive integer denominator.
    for j,(den,a,d,off) in enumerate(zip(*(bounds(m,panels) for m in frame_models(jet,pair)),strict=True)):
        x, y = pair.common_rate*den[0]-a[1], pair.common_rate*den[0]-d[1]
        if den[0] <= 0 or min(x,y) < 0 or max(map(abs,off))**2 > 4*x*y:
            return j
    return None


def own_models(pair):
    return [Model(p,e) for p,e in zip(pair.forward['coefficients'],pair.common_radii,strict=True)]


def joint_models(left, right):
    models = []
    for a,b in zip(left,right,strict=True):
        centre = [(m+n)//2 for m,n in zip(a.a,b.a,strict=True)]
        width = max(src.e+sum(abs(x-y) for x,y in zip(src.a,centre,strict=True)) for src in (a,b))
        models.append(Model(centre,width))
    return models


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--range',type=int,nargs=2,default=[0,3],metavar=('FIRST','LAST'))
    p.add_argument('--panels',type=int,choices=(8,16,32,64),default=8)
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    lo,hi = args.range
    rows = []
    for e,f in NEIGHBOURS:
        def read(label):
            return paired_rows(RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz'),
                               lo,hi,allow_unpaired=True)
        for i,(a,b) in enumerate(zip(read(e),read(f),strict=True),start=lo):
            if a is None or b is None:
                rows.append({'endpoints':[e,f],'index':i,
                             'nonconjugate_endpoints':[v for v,pair in ((e,a),(f,b)) if pair is None]})
                continue
            individual = [own_models(pair) for pair in (a,b)]
            common = joint_models(*individual)
            sec, i = int(e[1]), a.index
            shared = harmonic_jet(sec,i,common)
            rows.append({'endpoints':[e,f], 'index':i,
                         'shared_widths':[m.e for m in common],
                         'individual_widths':[[m.e for m in coords] for coords in individual],
                         'panels':args.panels,
                         'shared_first_failing_panel':[first_failure(shared,pair,args.panels) for pair in (a,b)],
                         'individual_first_failing_panel':[first_failure(harmonic_jet(sec,i,coords),pair,args.panels)
                             for coords,pair in zip(individual,(a,b),strict=True)]})
    args.output.write_text(json.dumps(rows,indent=2)+'\n')


if __name__ == '__main__':
    main()
