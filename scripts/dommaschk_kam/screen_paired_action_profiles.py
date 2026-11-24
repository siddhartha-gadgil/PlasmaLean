"""Exact Taylor-model feasibility screen for the finite 470-to-478 action comparison."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb
from pathlib import Path

from bounce_launch_box import R0
from bounce_mirror_pilot import HEIGHTS, Model, SCALE, ZERO
from emit_sparse_taylor_slab import models
from screen_sparse_reference_defects import sparse_fields
from verify_physical_trace_slabs import digest
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import joint_row


HEIGHT_SHIFT = F(1, 18000)
DENSITY_RATIO = F(3999, 4000)
STRENGTH_CEILING = F(17, 16)


@lru_cache(maxsize=1)
def shifted_coefficients():
    """Remove the reference times R^7 symbolically before enclosing the remainder."""
    terms = {}
    for coefficient, powers in sparse_fields()[0]:
        terms[tuple(powers)] = terms.get(tuple(powers), 0) + coefficient
    for k in range(8):
        powers = (k, 0, 0, 0)
        terms[powers] = terms.get(powers, 0) - HEIGHTS[0] * comb(7, k) * R0 ** (7-k)
    return [(c, powers) for powers, c in sorted(terms.items()) if c]


def gradient(terms, axis):
    result = []
    for coefficient, powers in terms:
        if powers[axis]:
            index = list(powers)
            index[axis] -= 1
            result.append((coefficient * powers[axis], tuple(index)))
    return result


def observables(r, columns):
    den, nr, nz = [sum(models(terms, columns), ZERO) for terms in sparse_fields()]
    diff = sum(models(shifted_coefficients(), columns), ZERO)
    if min(r.bound()[0], den.bound()[0]) <= 0:
        raise ValueError('nonpositive radius or angular denominator')
    r2 = r * r
    r4 = r2 * r2
    r8 = r4 * r4
    transverse = nr * nr + nz * nz
    gap = r2 * diff * (den.integer(2) - diff) + transverse
    return r, r8 * r8, gap, den * den, transverse, (den, diff, nr, nz)


def strength_error(radius, columns, obs):
    """Spatial mean-value bound for the squared strength on the entire radial/axial box."""
    r, p, _, _, transverse, (den, diff, nr, nz) = obs
    bounds = []
    for axis in (0, 1):
        dd, dr, dz = [sum(models(gradient(poly, axis), columns), ZERO)
                      for poly in (shifted_coefficients(), *sparse_fields()[1:])]
        dq = (nr * dr + nz * dz).integer(2)
        if axis == 0:
            num = ((r * r) * den * (r * dd - diff.integer(7))).integer(2) + r*dq - transverse.integer(16)
            divisor = p * r
        else:
            num = ((r * r) * den * dd).integer(2) + dq
            divisor = p
        lower = divisor.bound()[0]
        if lower <= 0:
            raise ValueError('gradient denominator enclosure meets zero')
        bounds.append(max(map(abs, num.bound())) / lower)
    return radius * sum(bounds)


def pair_inputs(index, traces):
    r, columns, _ = joint_row(index, traces)
    u, z, c, sn = columns
    if r.e != u.e or r.e != z.e:
        raise ValueError('expected the same spatial box radius on both coordinate axes')
    outer = observables(r, columns)
    center = observables(Model(r.a), (Model(u.a), Model(z.a), c, sn))
    err = strength_error(F(r.e, SCALE), columns, outer)
    return outer[:5], center[1:3], err


def margins(index, inner, outer):
    """Rows use a common normalized clock. The final field comparison uses centered gradients."""
    (r,p,e,d,a), (p0,e0), err0 = pair_inputs(index, inner)
    (R,P,E,D,A), (p1,e1), err1 = pair_inputs(index, outer)
    shift = Model.rational(2 * STRENGTH_CEILING * HEIGHT_SHIFT)
    ratio = Model.rational(DENSITY_RATIO ** 2)
    loss = Model.rational(1 - DENSITY_RATIO ** 2)
    high = Model.rational(STRENGTH_CEILING ** 2 - HEIGHTS[0] ** 2)
    field_gap = e * P - E * p - shift * (p * P)
    shifted = shift + Model.rational(err0 + err1)
    centered_gap = e0 * p1 - e1 * p0 - shifted * (p0 * p1)
    weight_gap = ((R-r) * (R+r) + loss * (r*r)) * (d*D) + A*d - ratio*(a*D)
    return [x.bound()[0] for x in (high*p-e, high*P-E, field_gap, centered_gap, weight_gap)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rows', type=int, default=325)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not 1 <= args.rows <= 391:
        parser.error('the archived trajectories each span 391 rows')
    records = [load(radius) for radius in (470, 478)]
    columns = list(zip(*(margins(i, records[0][2], records[1][2]) for i in range(args.rows)),
                       strict=True))
    tests = {}
    for name, values in zip(('inner_ceiling', 'outer_ceiling', 'direct_field_drop',
                             'centered_field_drop', 'density_ratio'),
                            columns, strict=True):
        worst = min(range(args.rows), key=values.__getitem__)
        tests[name] = dict(min_margin=str(values[worst]), worst_row=worst,
                           failed_rows=[i for i, v in enumerate(values) if v <= 0])
    report = dict(status='external exact arithmetic on original reflected tubes',
                  rows_each_way=args.rows, packets={r[0]: digest(r[1]) for r in records},
                  strength_ceiling=str(STRENGTH_CEILING), height_shift=str(HEIGHT_SHIFT),
                  density_ratio=str(DENSITY_RATIO), tests=tests)
    data = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(data)
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
