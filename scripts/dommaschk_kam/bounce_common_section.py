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


def section_seed(u, u_width, section):
    """Enclose the Q-16 launch at phi=section*pi/2 using every packed mode."""
    C,A = profile_coefficients('C'),profile_coefficients('A')
    result = []
    off = Box(-ceil(u_width*S),ceil(u_width*S))
    for key in ('R','z'):
        points = []
        for profile in (C,A):
            kind,coeffs,error = profile[key,False]
            mid = sum(c*(-1)**(section*j) for j,c in enumerate(coeffs)) if kind=='cos' else F(0)
            points.append(Box(floor((mid-error)*S),ceil((mid+error)*S)))
        c,a = points
        result.append(Box.rational(1-u)*c+Box.rational(u)*a+off*(a-c))
    return result


def transfer(alpha_width=PHASE_WIDTH, u_width=U_WIDTH, u=F(49,100), section=0):
    """Transfer births near a symmetry section to its exact azimuth."""
    if section not in (0,1):
        raise ValueError('section must be 0 or 1 in units of pi/2')
    cs,sn = harmonics(F(0),2*section,24)
    return transfer_at(cs,sn,section_seed(u,u_width,section),alpha_width,u_width,u)


def transfer_at(cs,sn,anchor,alpha_width,u_width,u):
    """Transfer any phase cell to an anchor enclosing the launch chart at its centre.

    cs[j], sn[j] enclose cos(2j*centre), sin(2j*centre) for j=0,...,24.
    The two boxes in anchor enclose the profile at that exact phase for all
    radii in [u-u_width,u+u_width].
    """
    if not (0<alpha_width<=F(1,2) and 0<=u_width and F(11,25)<=u-u_width<=u+u_width<=F(27,50)):
        raise ValueError('birth cell lies outside the deep strip')
    modes = launch_model(floor(1/(2*alpha_width)))
    off = Box.rational(u-F(49,100))+Box(-ceil(S*u_width),ceil(S*u_width))
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
    pulled = [Model.box(x+Box(-r,r)) for x,r in zip(anchor,end)]
    summary = dict(denominator=S,trial_numerators=trial,residual_numerators=residual,
                   transfer_error_numerators=end,B_upper_numerator=mag,Bphi_lower_numerator=bp)
    return pulled,summary


def common_section_inputs(alpha_width=PHASE_WIDTH,u_width=U_WIDTH,u=F(49,100),section=0):
    """Return ((data,seed,ev,init), transfer_report). Use alpha_width=0 in certified_segments."""
    check_arithmetic()
    seed,summary = transfer(alpha_width,u_width,u,section)
    ev,seeds = load_inputs()
    section_angle = section*np.pi/2
    c,a = [seed_cut(*s,np.array([section_angle]))[0][:,0] for s in seeds]
    data = polynomial_data()
    if section:
        # sin and cos at 2k*(pi/2+tau) both acquire the factor (-1)^k.
        # The same change applies to every spatial derivative in the Jacobian.
        data = [[{i:[[v.integer((-1)**((i+1)//2)) for v in row] for row in rows]
                       for i,rows in p.items()} for p in group] for group in data]
        class ShiftedProposer:
            def rhs(self, t, r, z):
                return ev.rhs(section_angle+t,r,z)
        proposer = ShiftedProposer()
    else:
        proposer = ev
    return (data,seed,proposer,c+float(u)*(a-c)),summary


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
