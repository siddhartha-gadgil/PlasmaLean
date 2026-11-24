"""Test the four endpoint row-length inequalities for the actual backward Euclidean trial ball."""
import argparse
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from math import sqrt
from pathlib import Path

from bounce_phase_frame import FRAME_SCALE
from emit_sparse_taylor_slab import RECORD
from screen_reflected_reference import paired_jobs


def screen(path):
    # Also establish reflection of the physical polynomial centers and endpoints.
    pairs = list(paired_jobs(path))
    raw = json.loads(gzip.decompress(path.read_bytes()))
    back, forward = [trace['steps'] for trace in raw['traces']]
    ratios = []
    for i, (job, _) in enumerate(pairs):
        trial = back[i]['frame_trial_radius']
        radius = forward[i]['physical_trial_radius']
        value = max(x*x+y*y for m in (job[4],job[5]) for x,y in m)
        # Off-diagonal sign reversals preserve both row lengths.
        ratios.append(Fraction(value*trial**2,(radius*FRAME_SCALE)**2))
    worst = max(range(len(ratios)),key=ratios.__getitem__)
    return {'source':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),
            'rows':len(ratios),'fits_original_forward_box':sum(q <= 1 for q in ratios),
            'worst_index':worst,'worst_squared_ratio':str(ratios[worst]),
            'worst_ratio_approx':sqrt(ratios[worst])}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--check',type=Path)
    args = parser.parse_args()
    records = [screen(p) for p in sorted(RECORD.parent.glob('bounce_frame_q0_u???.json.gz'))]
    out = json.dumps(records,indent=2)+'\n'
    if args.check and args.check.read_text() != out:
        raise SystemExit('projection report differs from fresh exact replay')
    if args.output:
        args.output.write_text(out)
    print(out,end='')
