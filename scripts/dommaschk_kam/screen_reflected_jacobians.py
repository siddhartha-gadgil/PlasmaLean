"""Check one full physical Jacobian tube and the stricter signed budget for each q0 pair."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

from emit_sparse_taylor_slab import RECORD
from screen_reflected_reference import conjugate
from screen_sparse_jacobians import evaluate,jobs


def paired(path):
    rows = {(j[1],j[2]):j for j in jobs(path,8,False,4)}
    for i in range(391):
        f,b = rows[1,i],rows[-1,i]
        sec,_,_,start,p,panels,spatial = f
        q = b[4]
        if (sec != 0 or p['coefficients'][0] != q['coefficients'][0] or
                [-x for x in p['coefficients'][1]] != q['coefficients'][1] or
                conjugate(start) != b[3] or conjugate(p['frame_end']) != q['frame_end']):
            raise ValueError(f'{path.name}: no exact section-zero reflection at row {i}')
        radius = max(p['physical_trial_radius'],q['physical_trial_radius'])
        mu = min(F(p['log_norm_upper']),F(q['log_norm_upper']))
        check=(sec,1,i,start,{**p,'physical_trial_radius':radius,'log_norm_upper':str(mu)},panels,spatial)
        yield check, radius-p['physical_trial_radius'], mu < F(p['log_norm_upper'])


def verify(item):
    check,dr,strict = item
    return (*evaluate(check),dr,strict)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,default=1,choices=range(1,7))
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    records=[]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for path in sorted(RECORD.parent.glob('bounce_frame_q0_u???.json.gz')):
            rows=list(pool.map(verify,paired(path),chunksize=3))
            records.append({'source':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),
              'matched_rows':len(rows),'passes':sum(r[4]!=0 for r in rows),
              'spatial_resolution':{str(k):sum(r[4]==k for r in rows) for k in (1,2,4)},
              'larger_backward_trial':sum(r[5]>0 for r in rows),
              'maximum_trial_increase_dyadic_units':max(r[5] for r in rows),
              'smaller_backward_mu':sum(r[6] for r in rows),'failed':[r[1] for r in rows if r[4]==0]})
            print(json.dumps(records[-1]),flush=True)
    if args.output:
        args.output.write_text(json.dumps(records,indent=2)+'\n')
