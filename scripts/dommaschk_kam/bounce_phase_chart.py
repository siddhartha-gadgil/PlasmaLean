"""Enclose both radial action faces at an arbitrary rational phase-chart centre.

In quadrant q the geometric birth angle is q*pi/4 + atan(t), 0 <= t <= 1.
The checker uses rational coordinates of exp(2i*angle) for the seed, field and
all its spatial derivatives. Only the floating proposal uses the angle itself.
The phase half-width is in geometric radians. Since d(angle)/dt <= 1, it also
covers a t-interval of that half-width within the chart.
"""
import argparse
import json
from fractions import Fraction as F
from math import atan, ceil, pi

import numpy as np

from bounce_action_pilot import TARGET, check_constant, enclose_action, integrate_segment
from bounce_common_section import transfer_at
from bounce_launch_box import Box, S, harmonics, profile_coefficients
from bounce_mirror_pilot import (
    HEIGHTS, SCALE, angle_models, certified_segments, check_arithmetic, load_inputs, polynomial_data,
    seed_cut,
)
from bounce_phase_strength import ShiftedStrength, check_shifted_strength


def launch_anchor(profiles, cs, sn, u):
    """Evaluate both packed profiles on the exact section, including the Q-16 errors."""
    seed = []
    for key in ('R', 'z'):
        cut = []
        for profile in profiles:
            kind, weights, error = profile[key, False]
            trigs = cs if kind == 'cos' else sn
            radius = ceil(error*S)
            value = Box(-radius, radius)
            for weight, trig in zip(weights, trigs, strict=True):
                value += Box.rational(weight)*trig
            cut.append(value)
        seed.append(Box.rational(1-u)*cut[0] + Box.rational(u)*cut[1])
    return seed


def check_origin():
    """At the 3-4-5 phase, independently test the signs and ordering of three harmonics."""
    cs, sn = harmonics(F(1, 2), 0, 3)
    origin = tuple(zip(cs[1:], sn[1:], strict=True))
    angles = angle_models(F(0), F(0), F(0), origin)
    c, s = F(1), F(0)
    for k in range(1, 4):
        c, s = (3*c-4*s)/5, (4*c+3*s)/5
        for model, exact in ((angles[2*k-1], s), (angles[2*k], c)):
            low, high = model.bound()
            if not low <= exact <= high:
                raise ArithmeticError('wrong angular origin in the field polynomial')


def enclose_face(inputs, u, dt, panels, limit, strength, origin, segment_builder):
    """Bound the launch-connected action without imposing an orientation at the roots.

    For the lower estimate integrate only a contiguous fully accessible core.
    For the upper estimate include every positive contribution up to a forbidden
    cap in each direction, even if another well occurs before the cap.
    """
    if dt <= 0 or limit <= 0 or panels < 1:
        raise ValueError('positive integration step, horizon and panel count required')
    check_constant()
    inner = u == F(11, 25)
    index = 1 if inner else 0
    height = HEIGHTS[index]
    total = 0
    extents = []
    for sign in (-1, 1):
        in_core = True
        core_end = F(0)
        for segment in segment_builder(*inputs, sign, dt, ceil(limit/dt), F(0), origin):
            tube, angles, fields = segment.fields(inputs[0])
            # Positive squared gap here means the field exceeds the requested height.
            gaps = strength.numerators(tube, angles, fields, HEIGHTS)
            if gaps[0].bound()[1] >= 0:
                in_core = False
            if segment.index == 0 and not in_core:
                raise ArithmeticError('first whole step must be accessible at the lower height')
            if gaps[1].bound()[0] > 0:
                extents.append(dict(direction=sign, accessible_core_end=str(core_end),
                                    forbidden_cap=str(dt*segment.index)))
                break
            if in_core:
                core_end = dt*(segment.index+1)
            if inner or in_core:
                value, = integrate_segment(tube[0], fields, [height], panels, [-gaps[index]])
                total += value.hi if inner else value.lo
        else:
            raise ArithmeticError('missing strictly forbidden end cap')
    bound = F(total, S*panels)*dt
    margin = TARGET-bound if inner else bound-TARGET
    return dict(action_upper_bound=str(bound) if inner else None,
                action_lower_bound=None if inner else str(bound),
                strict_face_margin=str(margin), heights=list(map(str, HEIGHTS)), target=str(TARGET),
                step=str(dt), panels_per_step=panels, extents=extents)


def run(quadrant, t, width, dt, panels, limit, framed=False, face_only=False):
    if quadrant not in range(4) or not 0 <= t <= 1:
        raise ValueError('expected a unit-circle chart and a centre in [0,1]')
    check_arithmetic()
    check_origin()
    check_shifted_strength()
    profiles = [profile_coefficients(tag) for tag in ('C', 'A')]
    degree = len(profiles[0]['R', False][1])-1
    cs, sn = harmonics(t, quadrant, degree)
    origin = tuple(zip(cs[1:4], sn[1:4], strict=True))
    data = polynomial_data()
    strength = ShiftedStrength(data)
    builder = certified_segments
    if framed:
        from bounce_phase_frame import check_frame, framed_segments
        check_frame()
        builder = framed_segments
    ev, seeds = load_inputs()
    angle = quadrant*pi/4 + atan(float(t))
    c, a = [seed_cut(*seed, np.array([angle]))[0][:, 0] for seed in seeds]

    class Proposer:
        def rhs(self, tau, radius, z):
            return ev.rhs(angle+tau, radius, z)

    faces = []
    for u in (F(11, 25), F(27, 50)):
        anchor = launch_anchor(profiles, cs, sn, u)
        seed, transfer = transfer_at(cs, sn, anchor, width, F(0), u)
        inputs = (data, seed, Proposer(), c + float(u)*(a-c))
        if face_only:
            result = enclose_face(inputs, u, dt, panels, limit, strength, origin, builder)
        else:
            result = enclose_action(inputs, dt, panels, F(0), limit, strength, origin,
                                    segment_builder=builder)
            inner, outer = result['action_bounds'][1][1], result['action_bounds'][0][0]
            margin = TARGET-F(inner) if u == F(11, 25) else F(outer)-TARGET
            result['strict_face_margin'] = str(margin)
            result.pop('straddles', None)
        result.update(face_u=str(u), transfer=transfer)
        faces.append(result)
    return dict(quadrant=quadrant, chart_center=str(t), phase_half_width=str(width), framed=framed,
                face_only=face_only, trace_limit=str(limit), trajectory_denominator=SCALE, faces=faces)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrant', type=int, choices=range(4), default=0)
    parser.add_argument('--center', type=F, default=F(1, 2))
    parser.add_argument('--alpha-half-width', type=F, default=F(1, 2**14))
    parser.add_argument('--step', type=F, default=F(1, 64))
    parser.add_argument('--panels', type=int, default=8)
    parser.add_argument('--limit', type=F, default=F(49, 8))
    parser.add_argument('--framed', action='store_true', help='control trajectory error in a moving frame')
    parser.add_argument('--face-only', action='store_true',
                        help='use an accessible core and forbidden caps for one-sided face bounds')
    args = parser.parse_args()
    out = run(args.quadrant, args.center, args.alpha_half_width, args.step,
              args.panels, args.limit, args.framed, args.face_only)
    print(json.dumps(out, indent=2))
    if any(F(face['strict_face_margin']) <= 0 for face in out['faces']):
        raise SystemExit('strict face ordering unresolved')
