"""Validated longitudinal action at two heights on the mirror pilot's launch cell.

In each direction integrate only up to the first certified outward crossing's upper
bracket end. The positive part of h-|B| contributes exactly zero between the root
and that end. Every panel encloses the full continuous-time integrand, including
panels that straddle a root. The reported j is the single integral between mirror
points in the dimensionless convention of bounce_screen.py.
"""
import argparse
import json
from fractions import Fraction as F
from itertools import islice, tee
from math import ceil, isqrt


import bounce_mirror_pilot as pilot
from bounce_launch_box import Box, S


TARGET = F("1.3599221876644974")
ZERO = Box(0, 0)


class PanelPolynomial:
    """Dyadic coefficients and an absolute remainder, evaluated by interval Horner."""

    def __init__(self, model):
        self.coefficients = [Box.rational(F(v, pilot.SCALE)) for v in model.a]
        error = ceil(F(S * model.e, pilot.SCALE))
        self.remainder = Box(-error, error)

    def on(self, time):
        value = self.coefficients[-1]
        for coefficient in reversed(self.coefficients[:-1]):
            value = value*time + coefficient
        return value + self.remainder


def sqrt_nonnegative(box):
    """Use nonnegativity of the underlying radicand when the lower bound is negative."""
    if box.hi < 0:
        raise ArithmeticError('whole enclosure of a nonnegative radicand is negative')
    upper = isqrt(box.hi*S)
    return Box(isqrt(max(0, box.lo)*S), upper + int(upper**2 < box.hi*S))


def panel_integrand(h, density, field_norm, radius16, gap_numerator):
    # The positive part is used deliberately, including on panels beyond the first root.
    positive_gap = Box(max(0, gap_numerator.lo), max(0, gap_numerator.hi))
    gap = positive_gap / (radius16 * (Box.rational(h) + field_norm))
    return density * sqrt_nonnegative(Box(2*S, 2*S) * gap)


def integrate_segment(radius, fields, heights, splits, gap_numerators=None):
    den, nr, nz = fields
    radius2 = radius*radius
    radius4 = radius2*radius2
    radius8 = radius4*radius4
    radius16 = radius8*radius8
    toroidal = radius*den
    strength_num = toroidal*toroidal + nr*nr + nz*nz
    if gap_numerators is None:
        gap_numerators = [radius16*pilot.Model.rational(h*h)-strength_num for h in heights]
    nums = [PanelPolynomial(num) for num in gap_numerators]
    den, r8, r16, strength = map(PanelPolynomial, (den, radius8, radius16, strength_num))
    totals = [ZERO for _ in heights]
    for n in range(splits):
        left = Box.rational(F(2*n, splits) - 1)
        right = Box.rational(F(2*(n+1), splits) - 1)
        time = Box(left.lo, right.hi)
        root = sqrt_nonnegative(strength.on(time))
        norm = root / r8.on(time)
        density = root / den.on(time)
        radial_factor = r16.on(time)
        for j, (h, num) in enumerate(zip(heights, nums, strict=True)):
            totals[j] += panel_integrand(h, density, norm, radial_factor, num.on(time))
    return totals


def check_constant():
    # R=D=1 and nR=nZ=0 give |B|=1 and ds/dφ=1. For h=3/2 the integrand equals 1.
    sample = integrate_segment(pilot.ONE, (pilot.ONE, pilot.ZERO, pilot.ZERO),
                               [F(3, 2), F(1), F(1, 2)], 4)
    if not (sample[0].lo <= 4*S <= sample[0].hi and sample[1] == sample[2] == ZERO):
        raise ArithmeticError('constant field and threshold checks failed')


def enclose_action(inputs, dt, splits, trace_phase_width, limit, strength=None, origin=(),
                   *, segment_builder=pilot.certified_segments):
    """Integrate from the first mirror on each side of the supplied section."""
    if dt <= 0 or splits < 1:
        raise ValueError('positive integration step and panel count required')
    check_constant()
    data = inputs[0]
    geometry = pilot.geometry if strength is None else strength.geometry
    heights = pilot.HEIGHTS
    total = [ZERO for _ in heights]
    counts = []
    crossings = []
    for sign in (-1, 1):
        trace = segment_builder(*inputs, sign, dt, ceil(limit/dt), trace_phase_width, origin)
        check, segments = tee(trace)
        result = pilot.check_crossings(data, check, geometry)
        if not result['success']:
            raise ArithmeticError(f'first mirror enclosures failed in direction {sign}: {result}')
        crossings.append(result)
        ends = [F(end) for _, end in result['brackets']]
        counts.append([str(end) for end in ends])
        for segment in islice(segments,result['steps']):
            start = dt * segment.index
            selected = [j for j, end in enumerate(ends) if start < end]
            if not selected:
                break
            tube, angles, fields = segment.fields(data)
            if len(selected) != len(heights):
                # A common terminal bracket lets us invert height on one fixed interval.
                # Require every discarded cap to be forbidden for its completed height.
                gaps, _ = geometry(data, angles, tube, fields, None, sign, False)
                if any(gaps[j][0] < 0 for j in range(len(heights)) if j not in selected):
                    raise ArithmeticError('a discarded cap can contribute to the clipped action')
            selected_heights = [heights[j] for j in selected]
            nums = None if strength is None else [
                -gap for gap in strength.numerators(tube,angles,fields,selected_heights)]
            values = integrate_segment(tube[0], fields, selected_heights, splits, nums)
            for j, value in zip(selected, values, strict=True):
                total[j] += value
    scale = dt / (S*splits)
    bounds = [(t.lo*scale, t.hi*scale) for t in total]
    return dict(step=str(dt), panels_per_step=splits, crossings=crossings, trajectory_denominator=pilot.SCALE,
                target=str(TARGET), heights=list(map(str, heights)),
                cutoff_abs_phi=counts, action_bounds=[[str(lo), str(hi)] for lo, hi in bounds],
                straddles=bounds[0][1] < TARGET < bounds[1][0])


def run(dt, splits, alpha_width, u_width, common_section=False):
    trace_phase_width = alpha_width
    if common_section:
        from bounce_common_section import common_section_inputs
        inputs, _ = common_section_inputs(alpha_width, u_width)
        trace_phase_width = F(0)
    else:
        inputs = pilot.pilot_inputs(alpha_width, u_width)
    result = enclose_action(inputs, dt, splits, trace_phase_width, F(21, 4))
    result.update(common_section=common_section, alpha_half_width=str(alpha_width),
                  u_half_width=str(u_width))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--common-section', action='store_true',
                        help='transfer launches to absolute azimuth zero before the long trace')
    parser.add_argument('--step', type=F)
    parser.add_argument('--panels', type=int, default=8)
    parser.add_argument('--alpha-half-width', type=F)
    parser.add_argument('--u-half-width', type=F, default=pilot.U_WIDTH)
    args = parser.parse_args()
    from bounce_common_section import PHASE_WIDTH
    if args.step is None:
        args.step = F(1, 64) if args.common_section else F(1, 32)
    if args.alpha_half_width is None:
        args.alpha_half_width = PHASE_WIDTH if args.common_section else pilot.ALPHA_WIDTH
    result = run(args.step, args.panels, args.alpha_half_width, args.u_half_width,
                 args.common_section)
    print(json.dumps(result, indent=2))
    if not result['straddles']:
        raise SystemExit('action intervals do not separate the prescribed action')
