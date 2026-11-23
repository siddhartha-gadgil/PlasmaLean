"""Common-section pilot for the C+u(A-C) deep launch strip at theta=0.

Run OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_common_section.py.
The declared cell is |alpha| <= 2^-16 and |u-.49| <= 2^-22. Let L(phi,u)
denote the same seed chart evaluated on the interval between alpha and zero.
The physical line x starts at x(alpha)=L(alpha,u). For e=x-L, the differential
equation is e'=F(phi,L+e)-dL/dphi and e(alpha)=0. The transfer checks a
strict rectangular first-exit inclusion for e, in either time direction.
The pilot then uses only absolute geometric angle with the pulled-back
section x(0). Both launch and section point belong to the allowed component.
Reported brackets are in |phi| from the section. Widen each end by 2^-16
for brackets in |phi-alpha| from the original birth.
"""
import argparse
import json
from fractions import Fraction as F
from math import ceil, floor

import numpy as np

from bounce_collar import field_on, shifted_polynomials, trig_slab
from bounce_launch_box import Box, S, angular_box, harmonics, launch_model, profile_coefficients
from bounce_mirror_pilot import (
    HEIGHTS, SCALE, Model, U_WIDTH, certified_segments, check_arithmetic, check_crossings,
    load_inputs, polynomial_data, seed_cut,
)


PHASE_WIDTH = F(1,2**16)


def section_at_zero(u_width):
    """Use all packed Fourier coefficients at the exact section, with the Q-16 error."""
    C,A = profile_coefficients('C'),profile_coefficients('A')
    result = []
    off = Box(-ceil(u_width*S),ceil(u_width*S))
    for key in ('R','z'):
        points = []
        for profile in (C,A):
            kind,coeffs,error = profile[key,False]
            mid = sum(coeffs) if kind=='cos' else F(0)
            points.append(Box(floor((mid-error)*S),ceil((mid+error)*S)))
        c,a = points
        delta = a-c
        result.append(c+(Box.rational(F(49,100))+off)*delta)
    return result


def transfer(alpha_width=PHASE_WIDTH, u_width=U_WIDTH):
    """Return a fixed-absolute-phase seed enclosure and the integer transfer bounds."""
    if not (0<alpha_width<=F(1,2) and 0<u_width<=F(1,20)):
        raise ValueError('birth cell lies outside the deep strip')
    modes = launch_model(floor(1/(2*alpha_width)))
    cs,sn = harmonics(F(0),0,24)
    off = Box(-ceil(S*u_width),ceil(S*u_width))
    def chart(derivative):
        values = []
        for k in ('R','z'):
            center,delta = [angular_box(m,cs,sn) for m in modes[k,derivative]]
            values.append(center+off*delta)
        return values
    launch_chart,derivative = chart(False),chart(True)
    half_phase = ceil(2*alpha_width*S)
    rotations = [(Box(S,S),Box(0,0))]*3
    angles = trig_slab(cs,sn,rotations,half_phase)
    p = shifted_polynomials()
    trial = [ceil(alpha_width*S/100)]*2
    for _ in range(8):
        tube = [x+Box(-r,r) for x,r in zip(launch_chart,trial)]
        velocity,mag,bp = field_on(p,angles,*tube)
        residual = [(v-d).abs_upper() for v,d in zip(velocity,derivative)]
        end = [ceil(alpha_width*r) for r in residual]
        if all(m<t for m,t in zip(end,trial)):
            break
        trial = [max(t,ceil(F(5,4)*m)+2) for t,m in zip(trial,end)]
    else:
        raise ArithmeticError('the transfer first-exit inclusion did not close')
    if F(mag,S)>=HEIGHTS[0] or bp<=0:
        raise ArithmeticError('transfer reaches the low mirror height or loses angular orientation')
    anchor = section_at_zero(u_width)
    pulled = [Model.box(x+Box(-r,r)) for x,r in zip(anchor,end)]
    summary = dict(denominator=S,trial_numerators=trial,residual_numerators=residual,
                   transfer_error_numerators=end,B_upper_numerator=mag,Bphi_lower_numerator=bp)
    return pulled,summary


def common_section_inputs(alpha_width=PHASE_WIDTH,u_width=U_WIDTH):
    """Return ((data,seed,ev,init), transfer_report). Use alpha_width=0 in certified_segments."""
    check_arithmetic()
    seed,summary = transfer(alpha_width,u_width)
    ev,seeds = load_inputs()
    c,a = [seed_cut(*s,np.array([0.]))[0][:,0] for s in seeds]
    return (polynomial_data(),seed,ev,c+0.49*(a-c)),summary


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--step',type=F,default=F(1,64))
    parser.add_argument('--limit',type=F,default=F(21,4))
    args = parser.parse_args()
    inputs,transfer_report = common_section_inputs()
    runs = [check_crossings(inputs[0],certified_segments(
        *inputs,sign,args.step,ceil(args.limit/args.step),F(0))) for sign in (-1,1)]
    print(json.dumps(dict(alpha_half_width=str(PHASE_WIDTH),u_half_width=str(U_WIDTH),
                          step=str(args.step),bracket_coordinate='absolute |phi| from section 0',
                          transfer=transfer_report,trajectory_denominator=SCALE,runs=runs),indent=2))
    if not all(x['success'] for x in runs):
        raise SystemExit('common-section pilot did not verify the full regular mirror window')
