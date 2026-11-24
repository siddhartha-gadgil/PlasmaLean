"""Compare sparse-polynomial moving-frame residual bounds with the archived budgets.

Each comparison is over the complete normalized time interval. All arithmetic
used for acceptance is rational. This is an arithmetic feasibility screen for
producing Lean certificates.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from functools import lru_cache
import gzip
from hashlib import sha256
import json
from math import comb, sqrt
from pathlib import Path

from bounce_mirror_pilot import Model, ORDER, R0M, SCALE, ZERO, angle_models
from bounce_phase_frame import FRAME_SCALE, affine_frame
from emit_sparse_taylor_slab import DATA, RECORD, coefficients, models


@lru_cache(maxsize=None)
def horner_weights(count, degree):
    """Translate s = (-n + 2*i + 2*x)/n, x in [0,1], over denominator n^degree."""
    return [[[(comb(k, j) * (-count+2*i)**(k-j) * 2**j * count**(degree-k))
              for k in range(j, degree+1)] for j in range(degree+1)] for i in range(count)]


def bounds(model, count):
    """Integer lower and upper Horner bounds, in units 1/(SCALE * count^ORDER)."""
    coeffs = model.a + [0]*(ORDER+1-len(model.a))
    error = model.e*count**ORDER
    for weights in horner_weights(count, ORDER):
        lower = upper = 0
        for j in reversed(range(ORDER+1)):
            shifted = sum(a*w for a, w in zip(coeffs[j:], weights[j], strict=True))
            lower = shifted + min(lower, 0)
            upper = shifted + max(upper, 0)
        yield lower-error, upper+error


@lru_cache(maxsize=1)
def sparse_fields():
    source = DATA.read_text()
    return [coefficients(source, name) for name in ('dD', 'dnR', 'dnZ')]


def residual_models(section, sign, index, coords, begin, end):
    r, z = (Model(series) for series in coords)
    angles = angle_models(Fraction(sign*(2*index+1),128), Fraction(sign,128), Fraction(0))
    harmonic_sign = (-1)**section
    columns = [r-R0M, z, angles[2].integer(harmonic_sign), angles[1].integer(harmonic_sign)]
    d, nr, nz = [sum(models(terms, columns), ZERO) for terms in sparse_fields()]
    def slope(p):
        return Model([128*(i+1)*a for i, a in enumerate(p.a[1:])])
    res_r = nr.integer(sign) - slope(r)*d
    res_z = nz.integer(sign) - slope(z)*d
    _, _, adj, det, _ = affine_frame(begin, end, Fraction(1,64))
    transformed = [a*res_r + b*res_z for a, b in adj]
    return transformed, det*d


def enclosing_box(transformed, denominator, count):
    """Independent dyadic bounds for both numerators and the positive denominator."""
    scale = count**ORDER
    x, y = [max(max(map(abs, interval)) for interval in bounds(component, count))
            for component in transformed]
    lo = min(lower for lower, _ in bounds(denominator, count))
    return -(x//-scale), -(y//-scale), lo//scale


def evaluate(job):
    section, sign, index, coords, begin, end, budget, count = job
    transformed, denominator = residual_models(section, sign, index, coords, begin, end)
    x, y, lo = enclosing_box(transformed, denominator, count)
    if lo <= 0:
        raise ArithmeticError(f'nonpositive denominator at slab {index} direction {sign}')
    bound_square = Fraction(x*x + y*y, lo*lo)
    budget = Fraction(budget)
    if budget <= 0:
        raise ValueError('expected a strictly positive submitted defect budget')
    return sign, index, bound_square, budget


def jobs(path, count, sample):
    with gzip.open(path, 'rt') as fp:
        packet = json.load(fp)
    if (packet['format'] != 'DommaschkN60Frame/v1' or packet['slabs_per_direction'] != 391
            or [part['direction'] for part in packet['traces']] != [-1, 1]
            or packet['section_in_half_pi'] not in (0,1) or packet['coordinate_denominator'] != SCALE
            or packet['frame_denominator'] != FRAME_SCALE or packet['step'] != '1/64'
            or packet['order'] != ORDER or count < 1):
        raise ValueError('unexpected trace format or subdivision count')
    for trace in packet['traces']:
        sign = trace['direction']
        if len(trace['steps']) != packet['slabs_per_direction']:
            raise ValueError('incomplete directed trace')
        begin = [[FRAME_SCALE, 0], [0, FRAME_SCALE]]
        for i, row in enumerate(trace['steps']):
            if i != row['index'] or any(len(s) != ORDER+1 for s in row['coefficients']):
                raise ValueError('malformed central reference curve')
            if not sample or i in (0, len(trace['steps'])-1):
                yield (packet['section_in_half_pi'], sign, i, row['coefficients'], begin,
                       row['frame_end'], row['defect_upper'], count)
            begin = row['frame_end']


def report(group):
    worst = max(group, key=lambda r: r[2]/r[3]**2)
    sign, index, square, budget = worst
    return {'passed': sum(sq <= b*b for _,_,sq,b in group), 'total': len(group),
            'worst_direction': sign, 'worst_slab': index, 'worst_bound_squared': str(square),
            'worst_budget': str(budget), 'worst_ratio_approx': sqrt(square)/float(budget)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, nargs='+', default=[RECORD])
    parser.add_argument('--workers', type=int, default=1)
    parser.add_argument('--pieces', type=int, default=8)
    parser.add_argument('--sample', action='store_true', help='check the first and last slab of each direction')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path, help='compare a saved summary with a fresh exact replay')
    args = parser.parse_args()
    summaries = []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for path in args.record:
            results = list(pool.map(evaluate, jobs(path, args.pieces, args.sample), chunksize=2))
            summary = {'source': path.name, 'sha256': sha256(path.read_bytes()).hexdigest(),
                       'pieces': args.pieces}
            for sign in (-1, 1):
                subset = [r for r in results if r[0] == sign]
                summary[str(sign)] = report(subset)
            summaries.append(summary)
            if args.sample:
                for sign, index, square, budget in results:
                    print(f'{path.name} direction {sign:+d}, slab {index}: residual <= {sqrt(square):.12g}, '
                          f'budget {float(budget):.12g}, ratio {sqrt(square)/float(budget):.9f}, '
                          f'passes {square <= budget**2}')
    text = json.dumps({'sparse_source': DATA.name, 'sparse_sha256': sha256(DATA.read_bytes()).hexdigest(),
                       'records': summaries}, indent=2) + '\n'
    if args.check and text != args.check.read_text():
        raise SystemExit('saved summary differs from exact replay')
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
