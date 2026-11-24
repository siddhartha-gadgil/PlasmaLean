"""Screen spatial Hessian transfer of a central Jacobian on archived QA2R trace slabs.

All acceptance comparisons use rational arithmetic. A coarse cell contains each
spatial segment from the reference center to the target tube at its physical angle.
"""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
import json
from math import ceil, floor, isqrt
from pathlib import Path

from bounce_mirror_pilot import Model, R0M, SCALE, ZERO, angle_models
from bounce_phase_frame import affine_frame
from emit_sparse_jacobian import derivative
from emit_sparse_taylor_slab import DATA, RECORD, models
from interface_arc import Interval
from screen_sparse_jacobians import field_jet, jobs, symmetric_models
from screen_sparse_reference_defects import bounds


SAMPLE = (0, 42, 69, 97, 171, 195, 226, 293, 316, 324, 390)
PAIRS = {'478': '470', '531': '523', '464': '456', '517': '509'}


def sqrt_upper(x):
    a, b = x.numerator, x.denominator
    n = isqrt(a*b)
    return Q(n + (n*n < a*b), b)


def tiled_interval(resolution, *columns):
    intervals = [m.bound() for m in columns]
    return (floor(resolution * min(lo for lo, _ in intervals)),
            ceil(resolution * max(hi for _, hi in intervals)), resolution)


def tile_model(cell):
    lo, hi, q = cell
    # Resolutions divide SCALE/2, so midpoint and half-width are exact.
    return Model([(lo+hi)*SCALE//(2*q)], (hi-lo)*SCALE//(2*q))


@lru_cache(maxsize=None)
def hessian_bound(cell):
    """Frobenius bound of the physical second derivative tensor on one spatial-trigonometric box."""
    columns = [tile_model(c) for c in cell]
    tensors = []
    for p, pu, pz in field_jet():
        fields = (p, pu, pz, derivative(pu, 0), derivative(pu, 1), derivative(pz, 1))
        tensors.append([Interval(*sum(models(g, columns), ZERO).bound()) if g else Interval(Q(0), Q(0))
                        for g in fields])
    d = tensors[0]
    if d[0].lo <= 0:
        return None
    inv = Interval(1 / d[0].hi, 1 / d[0].lo)
    sum_of_squares = Q(0)
    for n in tensors[1:]:
        value = n[0] * inv
        grad = [(n[j] - value*d[j])*inv for j in (1, 2)]
        for u, v, k, multiplicity in ((0, 0, 3, 1), (0, 1, 4, 2), (1, 1, 5, 1)):
            h = (n[k] - value*d[k] - grad[u]*d[v+1] - grad[v]*d[u+1])*inv
            sum_of_squares += multiplicity * max(abs(h.lo), abs(h.hi))**2
    return sqrt_upper(sum_of_squares)


def central_growth(section, direction, i, frame, step, center):
    den, a, b, c = symmetric_models(section, direction, i, frame, step, *center)
    upper = []
    for d, tr, diff, off in zip(*(bounds(m, 8) for m in (den, a+b, a-b, c)), strict=True):
        if d[0] <= 0:
            raise ArithmeticError('the central frame denominator includes zero')
        delta = sqrt_upper(Q(max(map(abs, diff))**2 + max(map(abs, off))**2))
        numer = tr[1]+delta
        upper.append(numer / (2*(d[0] if numer >= 0 else d[1])))
    return max(upper)


def screen(job, reference, grid, time_panels):
    section, direction, i, frame, step, _, _ = job
    center = [Model(p) for p in reference['coefficients']]
    target = [Model(p) for p in step['coefficients']]
    trial = [Model(m.a, step['physical_trial_radius']) for m in target]
    mu = central_growth(section, direction, i, frame, step, center)
    _, _, _, determinant, operator = affine_frame(frame, step['frame_end'], Q(1, 64))
    # In two dimensions the largest singular value of the adjugate equals the largest of M.
    det_lower = determinant.bound()[0]
    if det_lower <= 0:
        raise ArithmeticError('the frame determinant includes zero')
    condition = operator**2 / det_lower
    shift = sqrt_upper(sum(max(map(abs, (x-y).bound()))**2 for x, y in zip(target, center, strict=True)))
    radius = Q(step['physical_trial_radius'], SCALE) + shift
    permissible = (Q(step['log_norm_upper'])-mu) / (condition*radius)
    angle = angle_models(Q(direction*(2*i+1), 128), Q(direction, 128), Q(0))
    c, s = (m.integer((-1)**section) for m in (angle[2], angle[1]))
    cells = []
    for k in range(time_panels):
        lo, hi = Q(2*k, time_panels)-1, Q(2*(k+1), time_panels)-1
        def tile(q, *cols):
            if time_panels > 1:
                cols = [m.restrict(lo, hi) for m in cols]
            return tiled_interval(q, *cols)
        cells.append((tile(grid, trial[0]-R0M, center[0]-R0M), tile(grid, trial[1], center[1]),
                      tile(grid//4, c), tile(grid//4, s)))
    estimates = [hessian_bound(cell) for cell in cells]
    bound = max(estimates) if all(h is not None for h in estimates) else None
    return {'direction': direction, 'index': i, 'cells': cells, 'pass': bound is not None and bound < permissible,
            'central_growth': str(mu), 'center_separation': str(shift),
            'permissible_hessian': str(permissible), 'hessian_upper': str(bound) if bound is not None else None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--grid', type=int, default=128, help='dyadic spatial resolution (angular resolution is one quarter)')
    parser.add_argument('--time-panels', type=int, default=1)
    parser.add_argument('--neighbor', action='store_true', help='reuse the nearest archived center in each launch pair')
    parser.add_argument('--indices', type=int, nargs='+', default=SAMPLE)
    parser.add_argument('--all', action='store_true', help='include all 391 slab indices')
    parser.add_argument('--expect', type=int, nargs=2, metavar=('PASSES','ROWS'),
                        help='check the pass count and total on replay')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    g = args.grid
    if g < 4 or g & (g-1) or SCALE % (2*g) or args.time_panels < 1:
        parser.error('expected a dyadic grid dividing 2^79 and positive time panel count')
    indices = set(range(391) if args.all else args.indices)
    if not indices <= set(range(391)):
        parser.error('slab indices must lie between 0 and 390')
    reports = []
    for path in sorted(RECORD.parent.glob('bounce_frame_q?_u???.json.gz')):
        label = path.name.split('_u')[1][:3]
        if args.neighbor and label not in PAIRS:
            continue
        src = path.with_name(path.name.replace('_u'+label, '_u'+PAIRS[label])) if args.neighbor else path
        central = {(j[1], j[2]): j[4] for j in jobs(src, 8, False, 1) if j[2] in indices}
        rows = [screen(j, central[j[1], j[2]], g, args.time_panels)
                for j in jobs(path, 8, False, 1) if j[2] in indices]
        reports.append({'source': path.name, 'source_sha256': sha256(path.read_bytes()).hexdigest(),
                        'center': src.name, 'center_sha256': sha256(src.read_bytes()).hexdigest(), 'rows': rows})
        print(f"{path.name} {sum(r['pass'] for r in rows)}/{len(rows)}", flush=True)
    all_rows = [row for record in reports for row in record['rows']]
    counts = sum(r['pass'] for r in all_rows), len(all_rows)
    if args.expect and counts != tuple(args.expect):
        raise ValueError(f'expected {args.expect[0]}/{args.expect[1]}, obtained {counts[0]}/{counts[1]}')
    tiles = len({c for r in all_rows for c in r['cells']})
    print(f'{counts[0]}/{counts[1]} passed across {tiles} distinct cells', flush=True)
    if args.output:
        report = {'field_sha256': sha256(DATA.read_bytes()).hexdigest(), 'grid': g, 'panels': args.time_panels,
                  'passes': counts[0], 'rows': counts[1], 'cells': tiles, 'records': reports}
        args.output.write_text(json.dumps(report)+'\n')


if __name__ == '__main__':
    main()
