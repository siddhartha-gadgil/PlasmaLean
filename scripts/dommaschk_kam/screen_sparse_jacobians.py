"""Test archived logarithmic norms with the four-variable sparse physical field.

The unit-slab test preserves the correlation in the trace of det(M)D² M⁻¹(JM−M′).
The panel test checks both positive semidefinite principal minors directly at the
archived threshold. Both tests include the full physical trial radius.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import gzip
import json
from pathlib import Path

from bounce_mirror_pilot import Model, R0M, ZERO, angle_models
from bounce_phase_frame import FRAME_SCALE, affine_frame, product
from emit_sparse_jacobian import derivative
from emit_sparse_taylor_slab import DATA, RECORD, models
from screen_sparse_reference_defects import bounds, sparse_fields


@lru_cache(maxsize=1)
def field_jet():
    return [(p, derivative(p,0), derivative(p,1)) for p in sparse_fields()]


def evaluate_box(section, sign, index, start, step, panels, r, z):
    angles = angle_models(F(sign*(2*index+1),128),F(sign,128),F(0))
    angle_sign = (-1)**section
    columns = (r-R0M,z,angles[2].integer(angle_sign),angles[1].integer(angle_sign))
    rows = [[sum(models(p,columns),ZERO) for p in g] for g in field_jet()]
    d, du, dz = rows[0]
    j = [[(nx*d - n*dx).integer(sign) for nx,dx in zip((nu,nz),(du,dz))]
         for n,nu,nz in rows[1:]]
    m, velocity, adj, det, _ = affine_frame(start,step['frame_end'],F(1,64))
    den_sq = d*d
    den = det*den_sq
    jm = product(j,m)
    a = product(adj, [[jm[i][k]-den_sq*velocity[i][k] for k in (0,1)] for i in (0,1)])
    mu = F(step['log_norm_upper'])
    if mu <= 0:
        raise ValueError('nonpositive budget requires a two-sided denominator test')
    off = a[0][1]+a[1][0]
    # In the whole-slab test the trace and diagonal difference retain cancellation.
    base = 2 * mu * den.bound()[0] - (a[0][0]+a[1][1]).bound()[1]
    diff = max(map(abs,(a[0][0]-a[1][1]).bound()))
    width = max(map(abs,off.bound()))
    trace_pass = den.bound()[0] > 0 and base >= 0 and diff**2+width**2 <= base**2
    if trace_pass:
        return True,True
    for bd,aa,dd,bc in zip(*(bounds(model,panels) for model in (den,a[0][0],a[1][1],off)),
                            strict=True):
        l = mu*bd[0]-aa[1]
        r = mu*bd[0]-dd[1]
        if bd[0] <= 0 or min(l,r) < 0 or max(map(abs,bc))**2 > 4*l*r:
            return False,False
    return False,True


def split_coordinate(model, pieces):
    for i in range(pieces):
        lo = -model.e + 2*i*model.e//pieces
        hi = -model.e + 2*(i+1)*model.e//pieces
        mid = (lo+hi)//2
        yield Model([model.a[0]+mid,*model.a[1:]], max(mid-lo,hi-mid))


def evaluate(job):
    section, sign, index, start, step, panels, pieces = job
    r, z = (Model(row,step['physical_trial_radius']) for row in step['coefficients'])
    args = (section,sign,index,start,step,panels)
    tr,ok = evaluate_box(*args,r,z)
    if ok:
        return sign,index,tr,ok,1
    for count in sorted({n for n in (2,pieces) if 1 < n <= pieces}):
        if all(evaluate_box(*args,R,Z)[1]
               for R in split_coordinate(r,count) for Z in split_coordinate(z,count)):
            return sign,index,tr,ok,count
    return sign,index,tr,ok,0


def jobs(path, panels, sample, pieces):
    with gzip.open(path,'rt') as file:
        packet = json.load(file)
    if (packet['coordinate_denominator'] != 2**80 or packet['frame_denominator'] != FRAME_SCALE
            or packet['order'] != 7 or packet['step'] != '1/64'
            or packet['section_in_half_pi'] not in (0,1)):
        raise ValueError('trace has different field coordinates or scales')
    for trace in packet['traces']:
        sign = trace['direction']
        if sign not in (-1,1) or len(trace['steps']) != 391:
            raise ValueError('unexpected trace')
        start = [[FRAME_SCALE,0],[0,FRAME_SCALE]]
        for i, step in enumerate(trace['steps']):
            if step['index'] != i or step['physical_trial_radius'] < 0:
                raise ValueError('unexpected slab index or radius')
            if not sample or i in (0,97,195,293,390):
                yield packet['section_in_half_pi'],sign,i,start,step,panels,pieces
            start = step['frame_end']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('records', type=Path, nargs='*', default=[RECORD])
    parser.add_argument('--workers', type=int, default=1)
    parser.add_argument('--panels', type=int, default=8)
    parser.add_argument('--spatial', type=int, default=1)
    parser.add_argument('--sample', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.workers < 1 or args.panels < 1 or args.spatial < 1:
        parser.error('positive workers and panels required')
    report = {'field_sha256':sha256(DATA.read_bytes()).hexdigest(),'records':[]}
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for path in args.records:
            results = list(pool.map(evaluate,jobs(path,args.panels,args.sample,args.spatial),chunksize=3))
            for sign in (-1,1):
                rows = [r for r in results if r[0] == sign]
                summary = {'source':path.name,'input_sha256':sha256(path.read_bytes()).hexdigest(),
                    'sign':sign,'rows':len(rows),'whole_trace_pass':sum(r[2] for r in rows),
                    'time_panels_pass':sum(r[3] for r in rows),
                    'spatial_resolution':{str(k):sum(r[4] == k for r in rows)
                        for k in sorted({1,2,args.spatial}) if k <= args.spatial},
                    'total_pass':sum(r[4] != 0 for r in rows),'panels':args.panels,
                    'failures':[r[1] for r in rows if r[4] == 0]}
                report['records'].append(summary)
                print(json.dumps(summary),flush=True)
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+'\n')



if __name__ == '__main__':
    main()
