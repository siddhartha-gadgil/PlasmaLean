"""Outward-rounded radial variational tube on Dommaschk fixed-action launch cells.

The physical field-line tube is checked by bounce_mirror_pilot. On each
certified segment, enclose J=D_xF along every trajectory, bound the defect of
a proposed radial tangent against v'=sign*J v, and propagate its Euclidean
error with the logarithmic norm of sign*J. The initial tangent is A-C from
the same two Q-16 Fourier profiles. All acceptance tests use dyadic integers
or exact rationals. With --framed, both error bounds are propagated in moving
coordinates. With --common-section the short, allowed transfer bounds the
initial tangent at fixed azimuth. The concrete certificate and its ODE
interpretation are external. --tile-reports groups compatible cell reports and
checks exact coverage of the two proposed root brackets at their common section.
"""
import argparse
import json
from fractions import Fraction as F
from math import ceil, floor, isqrt
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

import bounce_mirror_pilot as pilot
from bounce_common_section import PHASE_WIDTH, common_section_inputs
from bounce_launch_box import Box, R0, S, angular_box, harmonics, launch_model
from bounce_phase_strength import ShiftedStrength
from bounce_screen import FIELD_FILE_SHA, SEEDS, load_inputs, seed_cut


def tangent_seed(alpha_width, section=0):
    modes = launch_model(floor(1/(2*alpha_width)))
    cs, sn = harmonics(F(0), 2*section, 24)
    return [pilot.Model.box(angular_box(modes[key, False][1], cs, sn)) for key in ('R', 'z')]


def transfer_tangent(data, alpha_width, u_width, u, section, transfer):
    """Enclose dx/du at the common section from the actual launch derivative.

    The transfer certificate bounds x-L(phi,u) by its two trial radii for the
    full transfer. For L_J>=sup ||D_xF||_infty and d=|alpha|, integration
    gives sup|v| <= |v_birth|/(1-d L_J), in either time direction.
    """
    modes = launch_model(floor(1/(2*alpha_width)))
    cs, sn = harmonics(F(0), 2*section, 24)
    off = Box.rational(u-F(49,100))+Box(-ceil(S*u_width),ceil(S*u_width))
    chart = []
    for k in ('R','z'):
        mid, delta = [angular_box(m,cs,sn) for m in modes[k,False]]
        chart.append(pilot.Model.box(mid+off*delta))
    trial = transfer['trial_numerators']
    tube = [x+pilot.Model.box(Box(-e, e)) for x, e in zip(chart, trial)]
    angles = pilot.angle_models(F(0), F(0), alpha_width)
    den, *nums = [pilot.evaluate(g[0], tube, angles)[0] for g in data]
    grads = [[pilot.evaluate(p, tube, angles)[0] for p in g[1:]] for g in data]
    den2 = den*den
    row_sums = [sum(max(map(abs, pilot.quotient_range(grads[i+1][j]*den-num*grads[0][j], den2)))
                    for j in (0, 1)) for i, num in enumerate(nums)]
    growth = alpha_width*max(row_sums)
    if growth >= 1:
        raise ArithmeticError('common-section tangent transfer does not close')
    v0 = tangent_seed(alpha_width, section)
    start = max(max(map(abs, x.bound())) for x in v0)
    err = ceil(start*growth/(1-growth)*pilot.SCALE)
    return [pilot.Model(x.a, x.e+err) for x in v0], err


def proposals(ev, initial, tangent, sign, step, count):
    """Untrusted continuous polynomial proposals for dx/du."""
    eps = 1e-24

    def rhs(t, state):
        r, z, vr, vz = state
        fr, fz = ev.rhs(sign*t, r+1j*eps*vr, z+1j*eps*vz)
        return sign*np.array([fr.real, fz.real, fr.imag/eps, fz.imag/eps])

    sol = solve_ivp(rhs, (0., float(step*count)), np.r_[initial, tangent],
                    method='DOP853', rtol=3e-14, atol=1e-15, max_step=float(step), dense_output=True)
    if not sol.success:
        raise ArithmeticError(sol.message)
    nodes = np.cos(np.arange(pilot.ORDER+1)*np.pi/pilot.ORDER)
    powers = np.polynomial.polynomial.polyvander(nodes, pilot.ORDER)
    for i in range(count):
        samples = sol.sol((i+(nodes+1)/2)*float(step))[2:]
        coefficients = np.linalg.solve(powers, samples.T).T
        yield [pilot.Model([round(float(v)*pilot.SCALE) for v in row]) for row in coefficients]


def tangent_radius(fields, gradients, nominal, radius, dt, sign, frame_start=None, *, record=None):
    den, *nums = fields
    den2 = den*den
    # J_ij is sign*(grad(n_i)*D - n_i*grad(D))/D².
    jac = [[(gradients[i+1][j]*den-num*gradients[0][j]).integer(sign)
            for j in (0, 1)] for i, num in enumerate(nums)]
    residual = []
    for i, q in enumerate(nominal):
        slope = pilot.Model([j*q.a[j] for j in range(1, len(q.a))])*pilot.Model.rational(2/dt)
        residual.append(jac[i][0]*nominal[0]+jac[i][1]*nominal[1]-slope*den2)
    if frame_start is not None:
        from bounce_phase_frame import affine_frame, linear_step_in_frame, propose_frame
        frame_end = propose_frame(frame_start, jac, den2, dt)
        frame = affine_frame(frame_start, frame_end, dt)
        final, defect = linear_step_in_frame(jac, den2, radius, dt, frame, residual, den2,
                                            record=record)
        return final, defect, frame[-1], frame_end
    diagonal = max(pilot.quotient_range(jac[i][i], den2)[1] for i in (0, 1))
    off = pilot.quotient_range(jac[0][1]+jac[1][0], den2.integer(2))
    mu = diagonal+max(map(abs, off))
    errors = [ceil(max(map(abs, pilot.quotient_range(e, den2)))*pilot.SCALE) for e in residual]
    defect = F(isqrt(sum(x*x for x in errors))+1, pilot.SCALE)
    # v'=J(t)v is linear in v. J is already enclosed on the physical trajectory
    # tube. The logarithmic norm and forcing bound hold for arbitrary tangent error.
    return pilot.radius_step(radius, defect, mu, dt), defect, 1, None


def observables(tube, fields, gradients, tangent, shifted, angles):
    """Differentiate B²=D²/R^14+(nR²+nZ²)/R^16 and A²=R²+(nR²+nZ²)/D².

    Form each spatial derivative before multiplying by the uncertain tangent.
    In R*d_R D-7D, the term h0*R^7 cancels exactly in the spatial
    coefficients. This keeps the far ends of the tube narrow.
    """
    r = tube[0]
    r2 = r*r
    r4 = r2*r2
    r8 = r4*r4
    r16 = r8*r8
    den, nr, nz = fields
    vr, vz = tangent
    transverse = nr*nr+nz*nz
    den2 = den*den
    den3 = den2*den
    diff, diff_r = [pilot.evaluate(p,tube,angles)[0] for p in shifted.diff[:2]]
    grad_q = [(nr*gradients[1][i]+nz*gradients[2][i]).integer(2) for i in (0,1)]
    br = (r2*den*(r*diff_r-diff.integer(7))).integer(2)+r*grad_q[0]-transverse.integer(16)
    bz = (r*r2*den*gradients[0][1]).integer(2)+r*grad_q[1]
    ar = (r*den3).integer(2)+den*grad_q[0]-(transverse*gradients[0][0]).integer(2)
    az = den*grad_q[1]-(transverse*gradients[0][1]).integer(2)
    gaps, _ = shifted.calculate(tube,angles,fields,[shifted.reference])
    return dict(B2=tuple(shifted.reference**2+x for x in pilot.quotient_range(gaps[0], r16)),
                A2=tuple(x+y for x,y in zip(r2.bound(),pilot.quotient_range(transverse,den2))),
                B2_u=pilot.quotient_range(br*vr+bz*vz,r*r16),
                A2_u=pilot.quotient_range(ar*vr+az*vz,den3))


def sanity():
    # D=1 and nR=nZ=0 give B²=R^-14, A²=R². At R=vR=1 the
    # expected radial derivatives are -14 and +2.
    one, zero = pilot.ONE, pilot.ZERO
    grad = [[zero, zero]]*3
    data = [[{0:[[v]]},{},{}] for v in (one,zero,zero)]
    shifted = ShiftedStrength(data)
    obs = observables([one, zero], [one, zero, zero], grad, [one, zero], shifted, [one])
    if any(not obs[k][0] <= c <= obs[k][1]
           for k, c in [('B2', 1), ('A2', 1), ('B2_u', -14), ('A2_u', 2)]):
        raise ArithmeticError('constant-field differentiation failed')
    # D=1+R+z, nR=z, nZ=R exercises both gradient columns, both
    # transverse components and both differentiated denominators.
    rat = pilot.Model.rational
    data = [[{0:[[rat(b)], [rat(a), rat(c+a*R0)]]},
             {0:[[rat(a)]]}, {0:[[rat(b)]]}] for a,b,c in [(1,1,1), (0,1,0), (1,0,0)]]
    r, z, vr, vz = F(7,8), F(-1,4), F(1,3), F(-2,7)
    den, q = 1+r+z, r*r+z*z
    dden, dq = vr+vz, 2*(r*vr+z*vz)
    exact = dict(B2=den**2/r**14+q/r**16, A2=r*r+q/den**2,
                 B2_u=2*den*dden/r**14-14*vr*den**2/r**15+dq/r**16-16*vr*q/r**17,
                 A2_u=2*r*vr+dq/den**2-2*q*dden/den**3)
    grad = [[one,one], [zero,one], [one,zero]]
    obs = observables([rat(r),rat(z)], [rat(den),rat(z),rat(r)], grad, [rat(vr),rat(vz)],
                      ShiftedStrength(data), [one])
    if any(not obs[k][0] <= c <= obs[k][1] for k, c in exact.items()):
        raise ArithmeticError('affine-field differentiation failed')
    # A constant tangent manufactured solution with nonzero Jacobian:
    # J=[[1,-1],[-2,2]] and v=(1,1) give v'=0 for either orientation.
    grad = [[zero, zero], [one, -one], [one.integer(-2), one.integer(2)]]
    constant = pilot.Model([pilot.SCALE, 0])
    for sign in [-1, 1]:
        size, defect, _, _ = tangent_radius([one, zero, zero], grad, [constant, constant],
                                            0, F(1, 32), sign)
        if size > 2 or defect > F(1, pilot.SCALE):
            raise ArithmeticError('manufactured tangent defect failed')


def root_bounds(y):
    if y < 0:
        raise ArithmeticError('cannot bound the real square root of a negative value')
    scale = pilot.SCALE
    lower = isqrt(floor(y*scale**2))
    exact = F(lower**2, scale**2) == y
    return F(lower, scale), F(lower+int(not exact), scale)


def core_slope(bounds, height):
    """One unit of core length where the clipped square root never vanishes.

    A_u >= 0 and B_u <= 0 throughout the full trace give pointwise
    monotonicity. On the core P=2 A²(h-B) satisfies P_u >= k where
    k = -min(A²) max((B²)_u)/max(B). If sqrt(P)<=M throughout, its
    secant is at least k/(2M) by rationalization.
    """
    b_low = root_bounds(bounds['B2'][0])[0]
    b_high = root_bounds(bounds['B2'][1])[1]
    action_upper = root_bounds(2*bounds['A2'][1]*(height-b_low))[1]
    squared_slope = bounds['A2'][0]*(-bounds['B2_u'][1])/b_high
    return squared_slope/(2*action_upper)


def directed(data, seed, ev, initial, v0, tangent, sign, dt, limit, alpha_width, framed, *, record=None):
    count = ceil(limit/dt)
    refs = proposals(ev, initial, tangent, sign, dt, count)
    build, frame_start = pilot.certified_segments, None
    if framed:
        from bounce_phase_frame import FRAME_SCALE, framed_segments, shifted_jump
        build = framed_segments
        frame_start = [[FRAME_SCALE,0],[0,FRAME_SCALE]]
    paths = build(data, seed, ev, initial, sign, dt, count, alpha_width)
    previous = [x.a[0] for x in v0]
    radius = isqrt(sum(x.e*x.e for x in v0))+1
    extremes = {}
    max_error = 0
    max_defect = F(0)
    max_core = None
    min_last = None
    min_orientation = None
    shifted = ShiftedStrength(data)
    for segment, nominal in zip(paths, refs, strict=True):
        jumps = [x.endpoint(-1)-old for x, old in zip(nominal, previous)]
        jump = shifted_jump(frame_start, jumps) if framed else isqrt(sum(x*x for x in jumps))+1
        tube, angles, fields = segment.fields(data)
        gradients = [[pilot.evaluate(p, tube, angles)[0] for p in g[1:]] for g in data]
        incoming = radius
        norms = []
        radius, defect, op, frame_start = tangent_radius(fields, gradients, nominal, radius+jump,
                                                        dt, sign, frame_start,
                                                        record=norms.append if record else None)
        physical_error = ceil(op*radius)
        enclosed = [pilot.Model(x.a, physical_error) for x in nominal]
        obs = observables(tube, fields, gradients, enclosed, shifted, angles)
        for key, (low, high) in obs.items():
            oldlo, oldhi = extremes.get(key, (low, high))
            extremes[key] = min(oldlo, low), max(oldhi, high)
        # If a step straddles |t|=1, include the entire step in the core bound.
        if segment.index*dt < 1:
            upper = obs['B2'][1]
            max_core = upper if max_core is None else max(max_core, upper)
        if segment.index*dt < limit <= (segment.index+1)*dt:
            min_last = obs['B2'][0]
        slope = None
        if obs['B2'][1] >= pilot.HEIGHTS[0]**2 and obs['B2'][0] <= pilot.HEIGHTS[1]**2:
            _, slope = shifted.geometry(data, angles, tube, fields, gradients, sign, True)
            min_orientation = slope[0] if min_orientation is None else min(min_orientation, slope[0])
        if record is not None:
            record(segment.index, incoming, jump, radius, defect, op, physical_error, norms[0],
                   obs, slope)
        max_error = max(max_error, physical_error)
        max_defect = max(max_defect, defect)
        previous = [x.endpoint(1) for x in nominal]
    low, high = pilot.HEIGHTS
    compare = (max_core < low*low and extremes['B2_u'][1] < 0 < extremes['A2_u'][0]
               and extremes['A2'][0] > 0 and extremes['B2'][0] > 0)
    regular = (max_core < low*low and min_last > high*high
               and min_orientation is not None and min_orientation > 0)
    scale = pilot.SCALE
    rounded = {k: [floor(lo*scale), ceil(hi*scale)] for k, (lo, hi) in extremes.items()}
    boundary = {k: [F(lo,scale), F(hi,scale)] for k,(lo,hi) in rounded.items()}
    return dict(direction=sign, steps=count, success=compare and regular,
                clipped_comparison=compare, regular_mirror=regular, max_tangent_error_numerator=max_error,
                max_tangent_defect_numerator=ceil(max_defect*scale),
                core_B2_upper_numerator=ceil(max_core*scale), end_B2_lower_numerator=floor(min_last*scale),
                core_radial_action_slope_lower_numerator=(
                    floor(core_slope(boundary, high)*scale) if compare else None),
                outward_B2_slope_lower_numerator=(floor(min_orientation*scale)
                                                  if min_orientation is not None else None),
                bounds=rounded)


def merge_tiles(paths):
    return merge_tile_rows([json.loads(Path(p).read_text()) for p in paths])


def merge_tile_rows(rows):
    """Check exact radial endpoints and both oriented traces before taking minima."""
    from bounce_local_graph import BRACKETS
    if not rows:
        raise ValueError('empty radial tile cover')
    common = ['scale', 'section_in_half_pi', 'common_section', 'alpha_half_width',
              'core_limit', 'limit', 'heights']
    spec = {k: rows[0][k] for k in common}
    section = spec['section_in_half_pi']
    if (not spec['common_section'] or section not in (0, 1) or spec['scale'] != pilot.SCALE or
            F(spec['core_limit']) != 1 or F(spec['alpha_half_width']) <= 0 or
            list(map(F, spec['heights'])) != list(pilot.HEIGHTS) or
            any(any(row[k] != spec[k] for k in common) for row in rows)):
        raise ValueError('incompatible well heights, trace windows, or sections')
    ordered = []
    for raw in rows:
        row = dict(raw, runs=[dict(run) for run in raw['runs']])
        u, w = F(row['u_center']), F(row['u_half_width'])
        if w <= 0 or [run['direction'] for run in row['runs']] != [-1, 1]:
            raise ValueError('degenerate tile or missing oriented trace')
        if (not all(run['success'] for run in row['runs'])
                or not row['radial_action_secant_lower_numerator'] > 0):
            raise ValueError('missing physical radial slope or mirror certificate')
        low, high = pilot.HEIGHTS
        scale = spec['scale']
        for run in row['runs']:
            bounds = {k: [F(lo,scale), F(hi,scale)] for k,(lo,hi) in run['bounds'].items()}
            if not (all(lo <= hi for lo,hi in bounds.values()) and
                    0 < bounds['B2'][0] and 0 < bounds['A2'][0] and
                    bounds['B2_u'][1] < 0 < bounds['A2_u'][0] and
                    run['steps'] == ceil(F(spec['limit']) / F(row['step'])) and
                    F(run['core_B2_upper_numerator'],scale) < low**2 and
                    high**2 < F(run['end_B2_lower_numerator'],scale) and
                    run['outward_B2_slope_lower_numerator'] > 0):
                raise ValueError('dyadic sign or trace extent does not support the physical slope')
            # Recompute the conservative secant from the exported dyadic bounds;
            # the in-memory rational expressions can be sharper by a few ulps.
            slope = floor(core_slope(bounds, high)*scale)
            if slope <= 0:
                raise ValueError('rounded core slope is nonpositive')
            run['core_radial_action_slope_lower_numerator'] = slope
        total = sum(run['core_radial_action_slope_lower_numerator'] for run in row['runs'])
        row['clipped_action_secant_lower_numerator'] = total
        row['radial_action_secant_lower_numerator'] = total
        ordered.append((u-w,u+w,row))
    ordered.sort(key=lambda item: item[0])
    brackets = []
    for index, (lo, hi) in sorted(enumerate(BRACKETS[section]), key=lambda item: item[1][0]):
        pos = lo
        tiles = []
        while pos < hi:
            if not ordered:
                raise ValueError('missing radial tile')
            start, stop, row = ordered.pop(0)
            if not start == pos < stop <= hi:
                raise ValueError('radial tile gap, overlap, or surplus')
            tiles.append(row)
            pos = stop
        minimum = min(row['radial_action_secant_lower_numerator'] for row in tiles)
        brackets.append(dict(height_index=index, u=[str(lo), str(hi)],
                             radial_action_secant_lower=str(F(minimum,spec['scale'])), tiles=tiles))
    if ordered:
        raise ValueError('surplus radial tiles')
    return dict(status='externally checked interval tubes', field_file_sha256=FIELD_FILE_SHA,
                seed_sha256={k:v[1] for k,v in SEEDS.items()}, **spec,
                brackets=sorted(brackets,key=lambda item: item['height_index']))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--step', type=F, default=F(1, 32))
    ap.add_argument('--limit', type=F, default=F(61, 10))
    ap.add_argument('--alpha-half-width', type=F)
    ap.add_argument('--common-section', action='store_true')
    ap.add_argument('--section', type=int, choices=[0, 1], default=0,
                    help='common section in multiples of pi/2')
    ap.add_argument('--u-center', type=F, default=F(49,100))
    ap.add_argument('--framed', action='store_true',
                    help='bound both physical trajectory and radial tangent errors in moving frames')
    ap.add_argument('--u-half-width', type=F, default=pilot.U_WIDTH)
    ap.add_argument('--tile-reports', nargs='+', metavar='JSON',
                    help='check the exact local root-bracket cover from previously generated tiles')
    args = ap.parse_args()
    if args.tile_reports:
        print(json.dumps(merge_tiles(args.tile_reports), indent=2))
        return
    if not 0 < args.step <= 1 or args.limit <= 1:
        ap.error('step must be in (0,1] and the trace must extend beyond the core')
    if not args.common_section and (args.section or args.u_center != F(49,100)):
        ap.error('shifting the launch centre requires --common-section')
    sanity()
    if args.framed:
        from bounce_phase_frame import check_frame
        check_frame()
    if args.alpha_half_width is None:
        args.alpha_half_width = PHASE_WIDTH if args.common_section else pilot.ALPHA_WIDTH
    if args.common_section:
        inputs, transfer = common_section_inputs(args.alpha_half_width, args.u_half_width,
                                                 args.u_center, args.section)
        data, seed, ev, initial = inputs
        v0, transfer_error = transfer_tangent(data, args.alpha_half_width, args.u_half_width,
                                              args.u_center, args.section, transfer)
        trace_width = F(0)
    else:
        data, seed, ev, initial = pilot.pilot_inputs(args.alpha_half_width, args.u_half_width)
        v0 = tangent_seed(args.alpha_half_width)
        trace_width, transfer_error = args.alpha_half_width, None
    _, seeds = load_inputs()
    c, a = [seed_cut(*s, np.array([args.section*np.pi/2]))[0][:, 0] for s in seeds]
    runs = [directed(data, seed, ev, initial, v0, a-c, sign, args.step, args.limit,
                     trace_width, args.framed) for sign in (-1, 1)]
    slope = (sum(row['core_radial_action_slope_lower_numerator'] for row in runs)
             if all(row['clipped_comparison'] for row in runs) else None)
    print(json.dumps(dict(scale=pilot.SCALE, u_center=str(args.u_center), section_in_half_pi=args.section,
                          common_section=args.common_section, framed=args.framed,
                          transfer_tangent_error_numerator=transfer_error,
                          alpha_half_width=str(args.alpha_half_width),
                          u_half_width=str(args.u_half_width), step=str(args.step),
                          limit=str(args.limit), core_limit='1', heights=list(map(str, pilot.HEIGHTS)),
                          clipped_action_secant_lower_numerator=slope,
                          radial_action_secant_lower_numerator=(slope if all(row['success'] for row in runs)
                                                               else None), runs=runs), indent=2))
    if not all(row['success'] for row in runs):
        raise SystemExit('the requested variational or mirror inequalities did not close')


if __name__ == '__main__':
    main()
