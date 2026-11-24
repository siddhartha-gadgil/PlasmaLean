"""Retest forward squared defect enclosures against their reflected section-zero rows."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from hashlib import sha256
import json
from math import sqrt
from pathlib import Path

from emit_sparse_taylor_slab import RECORD
from screen_sparse_reference_defects import evaluate, jobs


def conjugate(a):
    return [[v if i == j else -v for j,v in enumerate(row)] for i,row in enumerate(a)]


def paired_jobs(path):
    forward,backward = {},{}
    for job in jobs(path,8,False):
        if job[0] != 0:
            raise ValueError('section-zero reflection required')
        (forward if job[1] == 1 else backward)[job[2]] = job
    for i in range(391):
        f,b = forward[i],backward[i]
        if (f[3][0] != b[3][0] or [-v for v in f[3][1]] != b[3][1]
                or conjugate(f[4]) != b[4] or conjugate(f[5]) != b[5]):
            raise ValueError(f'{path.name}: reflection fails at row {i}')
        yield f,Fraction(b[6])


def check(pair):
    forward,back_budget = pair
    _,i,bound2,forward_budget = evaluate(forward)
    return i,bound2,forward_budget,back_budget


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,default=1)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for path in sorted(RECORD.parent.glob('bounce_frame_q0_u???.json.gz')):
            rows = list(pool.map(check,paired_jobs(path),chunksize=4))
            i,sq,_,bb = max(rows,key=lambda r:r[1]/r[3]**2)
            results.append({'source':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),
                            'matched_curves_and_frames':len(rows),
                            'own_backward_budget_passes':sum(s <= b*b for _,s,_,b in rows),
                            'strictly_smaller_backward_budget':sum(b < f for _,_,f,b in rows),
                            'worst_slab':i,'worst_bound_squared':str(sq),'worst_budget':str(bb),
                            'worst_ratio_approx':sqrt(sq)/float(bb)})
    out = json.dumps(results,indent=2)+'\n'
    if args.output:
        args.output.write_text(out)
    print(out,end='')
