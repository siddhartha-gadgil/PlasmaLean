"""Screen the radial derivative of the one-leg action on the N-54 deep strip.

Use the geometric angle relative to each launch, at fixed alpha and height.
Propagate the radial tangent of the physical field line with its variational
equation. The two turning points delimit the accessible component containing
the launch. All results use floating point and finite samples in alpha and u.

    OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_radial_variation.py
"""
import argparse
import json

import numpy as np
import scipy
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline

from bounce_action_pilot import TARGET
from bounce_mirror_pilot import HEIGHTS
from bounce_screen import FIELD_FILE_SHA, SEEDS, extent, leg, load_inputs, seed_cut, trace


WINDOW = 6.1
RADII = (0.44, 0.54)
HEIGHT = np.asarray(HEIGHTS, dtype=float)
IMAG_STEP = 1e-24
COLUMNS = ('left', 'right', 'outward_slope', 'action', 'radial_derivative',
           'arclength_term', 'strength_term', 'negative_mass', 'max_strength_u',
           'min_strength_u')


def variation_trace(ev, seeds, us, phases, nstep, tol):
    """Integrate x'=F and v'=D_x F v with v(0)=A-C at fixed geometric phase."""
    inner, outer = [seed_cut(*seed, phases)[0] for seed in seeds]
    offset = outer - inner
    start = inner[:, None, :] + us[None, :, None]*offset[:, None, :]
    tangent = np.broadcast_to(offset[:, None, :], start.shape)
    initial = np.concatenate([start, tangent])

    def rhs(t, state):
        r, z, vr, vz = state.reshape(initial.shape)
        # F is rational analytic in (R,z). Complex-step differentiation computes
        # the directional derivative without subtracting nearly equal strengths.
        fr, fz = ev.rhs(phases+t, r + 1j*IMAG_STEP*vr, z + 1j*IMAG_STEP*vz)
        return np.array([fr.real, fz.real, fr.imag/IMAG_STEP, fz.imag/IMAG_STEP]).ravel()

    positive = np.linspace(0., WINDOW, nstep+1)
    paths = []
    for sign in (-1, 1):
        sol = solve_ivp(rhs, (0., sign*WINDOW), initial.ravel(), t_eval=sign*positive,
                        method='DOP853', atol=tol, rtol=tol, max_step=0.2)
        if not sol.success:
            raise RuntimeError(sol.message)
        states = sol.y.reshape((*initial.shape, -1))
        paths.append(states[..., :0:-1] if sign < 0 else states)
    r, z, vr, vz = np.concatenate(paths, axis=-1)
    t = np.r_[-positive[:0:-1], positive]
    phi = phases[:, None]+t
    # Work one radius at a time to bound transient field arrays.
    signals = []
    for rr, zz, tr, tz in zip(r, z, vr, vz):
        rc = rr + 1j*IMAG_STEP*tr
        br, bp, bz = ev.B_cyl(rc, phi, zz + 1j*IMAG_STEP*tz)
        if np.min(bp.real) <= 0:
            raise ValueError('the geometric angle loses orientation')
        b = np.sqrt(br*br+bp*bp+bz*bz)
        speed = rc*b/bp
        signals.append(np.stack((b.real, speed.real, b.imag/IMAG_STEP, speed.imag/IMAG_STEP),
                                axis=-1))
    return t, np.asarray(signals)


def theta_rule(panels, order):
    """Composite Gauss rule after t=left+(right-left) sin(theta)^2."""
    nodes, weights = leggauss(order)
    width = np.pi/(2*panels)
    theta = (np.arange(panels)[:, None]+(nodes+1)/2)*width
    return theta.ravel(), np.tile(weights*width/2, panels)


def curve_extent(t, curve, limit):
    """Extrema of this cubic interpolant on the fixed closed angle window."""
    if limit > min(-t[0], t[-1]):
        raise ValueError('requested window exceeds the sampled trace')
    critical = curve.derivative().roots(extrapolate=False)
    # A constant piece can produce NaN roots. Its value is attained at a knot.
    knots = t[np.abs(t) < limit]
    where = np.r_[-limit, knots, critical[np.abs(critical) < limit], limit]
    return extent(curve(where))


def actions(t, signals, heights, rule):
    # At fixed t the last two columns are partial_u |B| and partial_u(ds/dphi).
    profile = CubicSpline(t, signals[:, 0])
    other = CubicSpline(t, signals[:, 1:])
    critical = profile.derivative().roots(extrapolate=False)
    # On the interpolant, absence of a critical value in the entire closed
    # height window prevents a fold between the two requested mirror heights.
    low, high = min(heights), max(heights)
    if min(profile(t[0]), profile(t[-1])) <= high or profile(0.) >= low:
        raise ValueError('the birth and both trace ends do not bracket the mirror heights')
    values = profile(critical)
    critical_gap = min(np.maximum(low-values, values-high), default=np.inf)
    if critical_gap <= 0:
        raise ValueError('critical value enters the closed mirror-height window')
    theta, weights = rule
    rows = []
    for h in heights:
        roots = profile.solve(h, extrapolate=False)
        left, right = max(roots[roots < 0]), min(roots[roots > 0])
        length = right-left
        times = left + length*np.sin(theta)**2
        speed, b_u, speed_u = other(times).T
        parallel2 = 2*(h-profile(times))
        if np.min(parallel2) <= 0 or np.min(speed) <= 0:
            raise ValueError('quadrature left the regular well')
        parallel = np.sqrt(parallel2)
        dt = weights*length*np.sin(2*theta)
        arclength_term = speed_u*parallel
        strength_term = -speed*b_u/parallel
        derivative = arclength_term + strength_term
        rows.append([left, right, min(-profile(left, 1), profile(right, 1)),
                     dt@(speed*parallel), dt@derivative, dt@arclength_term,
                     dt@strength_term, dt@np.maximum(-derivative, 0.),
                     max(b_u), min(b_u)])
    return rows, critical_gap


def fixed_window_bounds(t, signals):
    # Independent extrema on the full trace also test the clipped-integrand
    # comparison on forbidden end caps. The core gives a fixed allowed interval.
    return [curve_extent(t, CubicSpline(t, signals[:, i]), limit)
            for i, limit in [(0, WINDOW), (1, WINDOW), (2, WINDOW), (3, WINDOW), (0, 1.)]]


def grid(ev, seeds, nrad, nphase, nstep, panels, order, tol):
    us = np.linspace(*RADII, nrad)
    phases = np.linspace(0., np.pi, nphase+1)
    rule = theta_rule(panels, order)
    values = np.empty((nrad, len(phases), len(HEIGHT), len(COLUMNS)))
    bounds = []
    smallest_gap = np.inf
    for start in range(0, len(phases), 32):
        group = phases[start:start+32]
        t, signals = variation_trace(ev, seeds, us, group, nstep, tol)
        for i, lines in enumerate(signals):
            for k, line in enumerate(lines):
                rows, gap = actions(t, line, HEIGHT, rule)
                values[i, start+k] = rows
                smallest_gap = min(smallest_gap, gap)
                bounds.append(fixed_window_bounds(t, line))
    summaries = []
    for k, height in enumerate(HEIGHT):
        col = dict(zip(COLUMNS, values[:, :, k].transpose(2, 0, 1)))
        grad = col['radial_derivative']
        imin = np.unravel_index(np.argmin(grad), grad.shape)
        summaries.append(dict(height=height, action_at_inner_face=extent(col['action'][0]),
                              action_at_outer_face=extent(col['action'][-1]),
                              inner_margin=float(TARGET)-col['action'][0].max(),
                              outer_margin=col['action'][-1].min()-float(TARGET),
                              radial_derivative=extent(grad),
                              min_derivative_launch=[us[imin[0]], phases[imin[1]]],
                              arclength_term=extent(col['arclength_term']),
                              strength_term=extent(col['strength_term']),
                              negative_part_of_derivative_integral=extent(col['negative_mass']),
                              sampled_strength_u=[col['min_strength_u'].min(), col['max_strength_u'].max()],
                              smallest_outward_slope=col['outward_slope'].min(),
                              left_mirror=extent(col['left']), right_mirror=extent(col['right']),
                              largest_adjacent_mirror_step=np.abs(np.diff(values[:, :, k, :2], axis=1)).max()))
    seam = np.abs(values[:, 0]-values[:, -1]).max(axis=(0, 1))
    full_bounds = {key: extent(np.asarray(bounds)[:, i]) for i, key in enumerate(
        ['strength', 'arclength_density', 'strength_u', 'arclength_density_u', 'core_strength'])}
    return values, dict(nrad=nrad, nphase_intervals=nphase, half_trace_steps=nstep, panels=panels,
                        gauss_order=order, ode_tol=tol, heights=summaries,
                        fixed_window_interpolants=full_bounds, core_angle_half_width=1.,
                        smallest_critical_value_gap=smallest_gap,
                        seam_difference={name: seam[i] for i, name in enumerate(COLUMNS[:5])})


def analytic_fixture():
    # Moving, asymmetrically displaced endpoints and a radius-dependent arclength density.
    u = .2
    t = np.linspace(-2., 2., 65)
    rel = t-.4*u
    b = 1+rel**2-.2*u
    speed = np.full_like(t, 1+.3*u)
    line = np.column_stack((b, speed, -.8*rel-.2, np.full_like(t, .3)))
    rows, _ = actions(t, line, [2.], theta_rule(8, 12))
    expected = np.pi/np.sqrt(2)*np.array([(1+.3*u)*(1+.2*u), .3*(1+.2*u)+.2*(1+.3*u)])
    np.testing.assert_allclose(rows[0][3:5], expected, atol=5e-11, rtol=5e-11)


def secant_check(ev, seeds, u0, alpha, delta):
    """Independent centered difference using the pre-existing physical action routine."""
    t, b, speed, _, _ = trace(ev, seeds, np.array([[u0-delta], [u0+delta]]), np.array([alpha]),
                              2048, 2e-13)
    js = np.array([leg(t, line[0], arclength[0], HEIGHT, leggauss(16))[:, 4]
                   for line, arclength in zip(b, speed)])
    return (js[1]-js[0])/(2*delta)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phases', type=int, default=64, help='coarse angular mesh intervals')
    parser.add_argument('--radii', type=int, default=5, help='coarse radial mesh points')
    args = parser.parse_args()
    if args.phases < 4 or args.radii < 3 or args.radii % 2 == 0:
        parser.error('select at least four phase intervals and an odd number of radii >=3')
    analytic_fixture()
    ev, seeds = load_inputs()
    coarse, cs = grid(ev, seeds, args.radii, args.phases, 256, 8, 12, 2e-10)
    fine, fs = grid(ev, seeds, 2*args.radii-1, 2*args.phases, 512, 16, 16, 2e-12)
    matching = np.abs(coarse-fine[::2, ::2]).max(axis=(0, 1, 2))
    # Include a nonsymmetric phase and a face as well as a launch at phase zero.
    checks = []
    for i, k in [(args.radii-1, 0), (0, args.phases//2), (-1, args.phases//3)]:
        us = np.linspace(*RADII, 2*args.radii-1)
        alpha = k*np.pi/(2*args.phases)
        variational = fine[i, k, :, 4]
        coarse_secant, fine_secant = [secant_check(ev, seeds, us[i], alpha, d) for d in [1e-4, 5e-5]]
        checks.append(dict(u=us[i], alpha=alpha, variational=variational.tolist(),
                           secant_at_1e_minus4=coarse_secant.tolist(),
                           secant_at_5e_minus5=fine_secant.tolist(),
                           max_abs_difference=np.abs(fine_secant-variational).max()))
    print(json.dumps(dict(status='floating-point finite sampling of the connected launch well',
                          field_file_sha256=FIELD_FILE_SHA, seed_sha256={k: v[1] for k, v in SEEDS.items()},
                          numpy=np.__version__, scipy=scipy.__version__, target=str(TARGET), u=RADII,
                          alpha=[0., np.pi], half_trace_window=WINDOW, coarse=cs, fine=fs,
                          max_abs_shared_launch_change=dict(zip(COLUMNS, matching)),
                          independent_secants=checks), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()
