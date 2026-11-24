"""Cover both signed QA2R trial ellipses by one rectangle about the forward reference."""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from pathlib import Path

from bounce_phase_frame import FRAME_SCALE
from emit_sparse_taylor_slab import RECORD
from screen_projected_jacobians import projected_radii
from screen_reflected_reference import conjugate


@dataclass(frozen=True)
class TrialPair:
    index: int
    forward_left: list
    forward: dict
    backward_left: list
    backward: dict
    forward_radii: tuple
    backward_radii: tuple
    center_gap: tuple
    common_radii: tuple
    common_rate: Fraction


def paired_rows(path, lo=0, hi=7):
    with gzip.open(path, 'rt') as src:
        packet = json.load(src)
    traces = {trace['direction']: trace['steps'] for trace in packet['traces']}
    if set(traces) != {-1, 1} or not 0 <= lo <= hi < min(map(len, traces.values())):
        raise ValueError(f'{path}: wrong direction or index range')
    identity = [[FRAME_SCALE, 0], [0, FRAME_SCALE]]
    for index in range(lo, hi+1):
        f, b = traces[1][index], traces[-1][index]
        lf = traces[1][index-1]['frame_end'] if index else identity
        lb = traces[-1][index-1]['frame_end'] if index else identity
        if conjugate(lb) != lf or conjugate(b['frame_end']) != f['frame_end']:
            raise ValueError(f'{path.name} row {index}: frames do not conjugate')
        fr = projected_radii(lf, f['frame_end'], f['frame_trial_radius'])
        br = projected_radii(lb, b['frame_end'], b['frame_trial_radius'])
        # Radius is invariant; height changes sign. Each monomial has magnitude ≤ 1.
        gap = tuple(sum(abs(a - sign*c) for a,c in zip(fp,bp,strict=True))
                    for sign,fp,bp in zip((1,-1),f['coefficients'],b['coefficients'],strict=True))
        radii = tuple(max(own, other+delta) for own,other,delta in zip(fr,br,gap,strict=True))
        rate = min(Fraction(f['log_norm_upper']), Fraction(b['log_norm_upper']))
        yield TrialPair(index, lf, f, lb, b, fr, br, gap, radii, rate)


def report(path, lo, hi):
    rows = []
    for p in paired_rows(path,lo,hi):
        rows.append({'index':p.index,'forward_projected_radii':p.forward_radii,
                     'backward_projected_radii':p.backward_radii,'center_gap':p.center_gap,
                     'common_radii':p.common_radii,'common_rate':str(p.common_rate),
                     'forward_rate_fits_backward':Fraction(p.forward['log_norm_upper'])
                                                   <= Fraction(p.backward['log_norm_upper'])})
    return {'packet':path.name,'packet_sha256':sha256(path.read_bytes()).hexdigest(),'rows':rows}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--range',type=int,nargs=2,default=(0,7),metavar=('FIRST','LAST'))
    parser.add_argument('--output',type=Path)
    parser.add_argument('--check',type=Path)
    args = parser.parse_args()
    paths = sorted(RECORD.parent.glob('bounce_frame_q?_u???.json.gz'))
    out = json.dumps([report(path,*args.range) for path in paths],indent=2)+'\n'
    if args.check and args.check.read_text() != out:
        raise SystemExit('reflected trial report differs from an exact replay')
    if args.output:
        args.output.write_text(out)
    else:
        print(out,end='')
