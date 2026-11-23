"""Validate the fixed-action radial face inequalities at either symmetry section.

With section in {0,1}, every birth at |alpha-section*pi/2| <= phase_width
is transferred to that common section inside the central allowed component.
The trace variable is the geometric azimuth measured from the common section.
The expected face inequalities compare the prescribed one-way action to two
endpoint heights, extending to the intervening height window by monotonicity.
"""
import argparse
import json
from fractions import Fraction as F

from bounce_action_pilot import TARGET, enclose_action
from bounce_common_section import PHASE_WIDTH, common_section_inputs
from bounce_phase_strength import ShiftedStrength, check_shifted_strength


def run(section, u, phase_width, dt, panels, limit, compensated, framed=False):
    inputs, transfer = common_section_inputs(phase_width, F(0), u, section)
    if compensated:
        check_shifted_strength()
    strength = ShiftedStrength(inputs[0]) if compensated else None
    if framed:
        from bounce_phase_frame import check_frame, framed_segments
        check_frame()
        result = enclose_action(inputs, dt, panels, F(0), limit, strength, segment_builder=framed_segments)
    else:
        result = enclose_action(inputs, dt, panels, F(0), limit, strength)
    result.pop('straddles')
    lower_height, upper_height = [[F(x) for x in row] for row in result['action_bounds']]
    if u == F(11,25):
        margin = TARGET-upper_height[1]
    elif u == F(27,50):
        margin = lower_height[0]-TARGET
    else:
        raise ValueError('expected the inner or outer face of the deep strip')
    result.update(section_in_half_pi=section, face_u=str(u), compensated=compensated, framed=framed,
                  defect_coordinates='moving frame' if framed else 'physical coordinates',
                  phase_half_width=str(phase_width), transfer=transfer,
                  strict_face_margin=str(margin))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--section', type=int, choices=[0,1], required=True)
    parser.add_argument('--u', type=F, choices=[F(11,25), F(27,50)], required=True)
    parser.add_argument('--alpha-half-width', type=F, default=PHASE_WIDTH)
    parser.add_argument('--step', type=F, default=F(1,64))
    parser.add_argument('--panels', type=int, default=8)
    parser.add_argument('--limit', type=F, default=F(6))
    parser.add_argument('--compensated', action='store_true',
                        help='cancel the leading toroidal field term in squared-strength gaps')
    parser.add_argument('--framed', action='store_true',
                        help='validate line errors in a moving variational frame')
    args = parser.parse_args()
    result = run(args.section, args.u, args.alpha_half_width, args.step, args.panels, args.limit,
                 args.compensated, args.framed)
    print(json.dumps(result, indent=2))
    if F(result['strict_face_margin']) <= 0:
        raise SystemExit('strict face ordering unresolved')
