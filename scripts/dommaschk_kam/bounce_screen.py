"""Untrusted two-turning-point bounce screen on the N-53 Dommaschk vacuum field.

Run from the repository root with
    OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_screen.py

The launch surface interpolates the outboard symmetry cuts of the C and A Fourier
seeds. Every intermediate launch is traced by the physical field-line ODE. Its
coordinate u is a launch interpolation fraction. The phase alpha is the geometric
toroidal launch angle modulo pi in the two-field-period quotient. Both length
and field strength use the candidate's normalized units. The reported
flux density is the magnetic two-form on the launch surface (charge excluded).

For h=E/mu the Burby--MacKay--Naik one-leg scaled action is
j = integral sqrt(2*(h-|B|)) ds. Its derivative j_h is the scaled half-period.
In consistent dimensional units the full parallel bounce time is 2*sqrt(m/mu)*j_h.
See https://arxiv.org/html/2211.13367#S2.SS1 for these conventions. We test the connected
well containing the launch point and report sampled data for the leading
parallel-motion model. A missing or ambiguous branch is a failure of this test.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline

from dfield import Evaluator, ExactField, TARGET

HERE = Path(__file__).resolve().parent
FIELD_FILE_SHA = '9bd100ec63244c0980856a3633188f7bebcbb28b7a96417e2931210583bcb646'
SEEDS = {
    'C': ('20261101T015838Z', 'ef91ae1b34333fd4b43ffbfb1d73ceda500ac3fecae1eb4cde320319497276c2'),
    'A': ('20261101T111958Z', 'b2524e61c865759436434df012a2727febd5bc73347c0412c493efc73404c5ac'),
}
# Use the same h on every line. Determine the physical field-strength window
# from the two reference lines at alpha=0 (launch value and first half-turn range).
FRACTIONS = (0.195, 0.2, 0.205, 0.35, 0.495, 0.5, 0.505, 0.65)
SCREENS = ((0.495, 0.5, 0.505), (0.195, 0.2, 0.205))


def seed_cut(seed, theta, alpha):
    """Evaluate (R,z) and their phi derivatives on a constant-theta cut."""
    result, derivatives = [], []
    for key, coeff, trig, dtrig in [('R', 'a', np.cos, lambda x: -np.sin(x)),
                                    ('z', 'b', np.sin, np.cos)]:
        k, m = np.asarray(seed['idx_' + key]).T
        c = np.asarray(seed[coeff], dtype=float)
        phase = k[:, None] * theta + 2 * m[:, None] * alpha
        result.append(c @ trig(phase))
        derivatives.append((2*m*c) @ dtrig(phase))
    return np.array(result), np.array(derivatives)


def load_inputs():
    if hashlib.sha256(Path(TARGET).read_bytes()).hexdigest() != FIELD_FILE_SHA:
        raise ValueError('candidate file digest changed')
    field = ExactField()
    ev = Evaluator(field)
    seeds = []
    for tag, (stamp, digest) in SEEDS.items():
        source = HERE / 'results' / stamp / f'torus_{tag}_N96_M80.json'
        raw = source.read_bytes()
        seed = json.loads(raw)
        if hashlib.sha256(raw).hexdigest() != digest or seed['candidate_sha256'] != field.sha:
            raise ValueError(f'wrong candidate or torus file for {tag}')
        # Outboard selects the theta=0 or pi symmetry cut with larger R at phi=0.
        theta = max((0., np.pi), key=lambda th: seed_cut(seed, th, np.array([0.]))[0][0, 0])
        seeds.append((seed, theta))
    return ev, seeds


def trace(ev, seeds, u, alpha, nstep, tol):
    """Trace both toroidal directions from an entire 2-D strip of launches."""
    c, dc = seed_cut(*seeds[0], alpha)
    a, da = seed_cut(*seeds[1], alpha)
    origin = c[:, None, :] + u * (a-c)[:, None, :]
    tangent = dc[:, None, :] + u * (da-dc)[:, None, :]
    R, z = origin
    BR, BP, BZ = ev.B_cyl(R, alpha, z)
    dR, dz = a-c
    # beta(du,dalpha) = B dot (X_u cross X_alpha) in physical cylindrical basis.
    flux = -BR*dz*R + BP*(dz*tangent[0] - dR*tangent[1]) + BZ*dR*R
    if np.min(flux) <= 0 <= np.max(flux):
        raise ValueError('sampled launch strip has a tangent or orientation change')
    # At least a half poloidal turn in both directions for either boundary seed.
    stop = np.pi / min(abs(float(seed['iota'])) for seed, _ in seeds)
    grid = np.linspace(-stop, stop, 2*nstep + 1)
    def rhs(t, state):
        rr, zz = state.reshape(origin.shape)
        return np.array(ev.rhs(t + alpha, rr, zz)).ravel()

    paths = []
    for sign in (-1, 1):
        times = sign * grid[nstep:]
        sol = solve_ivp(rhs, (0., sign*stop), origin.ravel(), method='DOP853',
                        t_eval=times, atol=tol, rtol=tol, max_step=0.3)
        if not sol.success:
            raise RuntimeError(sol.message)
        values = sol.y.reshape((*origin.shape, nstep + 1))
        paths.append(values[..., :0:-1] if sign == -1 else values)
    rr, zz = np.concatenate(paths, axis=-1)
    phi = alpha[:, None] + grid
    field_values, lengths = [], []
    for rline, zline in zip(rr, zz):
        br, bp, bz = ev.B_cyl(rline, phi, zline)
        if np.any(bp <= 0):
            raise ValueError('field-line time phi ceases to be oriented')
        mag = np.sqrt(br*br + bp*bp + bz*bz)
        field_values.append(mag)
        lengths.append(rline * mag / bp)
    return grid, np.array(field_values), np.array(lengths), flux, origin


def leg(t, b, length, heights, quadrature):
    """Turning points and sine-substitution Gauss integrals on the central component."""
    mid = len(t)//2
    profile = CubicSpline(t, b)
    speed = CubicSpline(t, length)
    critical = profile.derivative().roots(extrapolate=False)
    nodes, weights = quadrature
    y = nodes*np.pi/2
    results = []
    for h in heights:
        if b[mid] >= h:
            raise ValueError(f'launch above mirror h={h}')
        roots = profile.solve(h, extrapolate=False)
        left, right = roots[roots < 0], roots[roots > 0]
        if not len(left) or not len(right):
            raise ValueError(f'missing turning point at h={h}')
        l, r = left[-1], right[0]
        # Split at extrema and also at regular angular intervals. Cluster quadrature
        # nodes at each endpoint, including near-grazing interior local maxima.
        edges = np.unique(np.r_[l, np.arange(l+0.5, r, 0.5),
                                critical[(critical > l) & (critical < r)], r])
        half = np.diff(edges)[:, None]/2
        tq = (edges[1:]+edges[:-1])[:, None]/2 + half*np.sin(y)
        w = weights * np.pi/2 * half * np.cos(y) * speed(tq)
        parallel = np.sqrt(2*(h-profile(tq)))
        if not np.all(parallel > 0):
            raise ValueError('quadrature entered the forbidden region')
        # Test where branch transitions could occur on this finite trace.
        gap = np.min(np.abs(profile(critical)-h)) if len(critical) else np.inf
        near = min(abs(profile(l, 1)), abs(profile(r, 1)))
        results.append((l, r, gap, near, np.sum(w*parallel), np.sum(w/parallel)))
    return np.array(results)


def resolution(ev, seeds, u, nphase, nstep, ng, tol, heights=None):
    alpha = np.arange(nphase) * np.pi/nphase
    t, b, ds, flux, origin = trace(ev, seeds, u, alpha, nstep, tol)
    if heights is None:
        ref = b[[0, -1], 0]
        low = ref[:, nstep].max()
        high = min(ref[:, :nstep].max(axis=1).min(), ref[:, nstep+1:].max(axis=1).min())
        if high <= low:
            raise ValueError('no common reference mirror window')
        heights = low + np.array(FRACTIONS) * (high-low)
    quadrature = leggauss(ng)
    vals = np.array([[leg(t, b[i,k], ds[i,k], heights, quadrature)
                      for k in range(nphase)] for i in range(len(u))])
    return heights, vals, flux, origin


def extent(x):
    return [float(np.min(x)), float(np.max(x))]


def summarize(heights, values, flux, origin):
    rows = []
    for h, level in zip(heights, values.transpose(2, 0, 1, 3)):
        l, r, gap, slope, j, jh = level.transpose(2, 0, 1)
        rows.append(dict(h=float(h), left_phi=extent(l), right_phi=extent(r),
                         nearest_critical_height_gap=float(gap.min()),
                         min_mirror_slope=float(slope.min()), j_inner=extent(j[0]),
                         j_outer=extent(j[-1]), jh=extent(jh)))
    return dict(mirrors=rows, launch_flux_density=extent(flux),
                radial_cut_lengths=extent(np.linalg.norm(origin[:, -1]-origin[:, 0], axis=0)))


def trace_contours(ev, seeds, heights, values, fractions, nphase):
    """Retrace simultaneous fixed-action levels and refine the steepest mirror on each."""
    u = np.linspace(0., 1., len(values))
    low, center, high = fractions
    mid = values[:, :, FRACTIONS.index(center), 4]
    direction = np.sign(np.mean(mid[-1])-np.mean(mid[0]))
    target = (max(direction*mid[0]) + min(direction*mid[-1]))/2
    indices = [FRACTIONS.index(low), FRACTIONS.index(high)]
    starts, gradients = [], []
    for k in indices:
        action = direction * values[:, :, k, 4]
        if not (np.all(np.diff(action, axis=0) > 0) and np.all(action[0] < target)
                and np.all(action[-1] > target)):
            return dict(fractions=fractions, status='target fails sampled monotonicity or bracketing')
        ray_u, radial_gradients = [], []
        for ray in action.T:
            n = np.searchsorted(ray, target)
            ray_u.append(np.interp(target, ray, u))
            radial_gradients.append((ray[n]-ray[n-1])/(u[n]-u[n-1]))
        starts.append(ray_u)
        gradients.append(radial_gradients)
    base_phases = np.arange(values.shape[1])*np.pi/values.shape[1]

    def retrace(alpha):
        guess = np.array([np.interp(alpha, base_phases, row, period=np.pi) for row in starts])
        djdu = np.array([np.interp(alpha, base_phases, row, period=np.pi) for row in gradients])
        # The action can jump when a ripple well splits. Keep the final residual
        # even if the requested action cannot be reached by this branch.
        for iteration in range(6):
            if np.min(guess) < 0 or np.max(guess) > 1:
                raise ValueError('a fixed-action root leaves the tested strip')
            t, b, ds, _, origin = trace(ev, seeds, guess, alpha, 1024, 3e-13)
            q = leggauss(12)
            v = np.array([[leg(t, bb, ll, [heights[k]], q)[0]
                           for bb, ll in zip(b[i], ds[i])] for i, k in enumerate(indices)])
            residual = v[..., 4]*direction - target
            if np.max(np.abs(residual)) < 1e-8 or iteration == 5:
                break
            guess -= residual / djdu
        return guess, v, residual, origin

    width = np.pi/nphase
    phase = np.arange(nphase)*width
    guess, v, residual, origin = retrace(phase)
    jumps = np.abs(v[..., :2] - np.roll(v[..., :2], 1, axis=1))
    regularity = []
    for i in range(2):
        highest, end = np.unravel_index(np.argmax(jumps[i]), jumps[i].shape)
        left, right = phase[highest]-width, phase[highest]
        zooms = []
        for _ in range(2):
            zphase = np.linspace(left, right, 17)
            zu, zv, zr, _ = retrace(zphase)
            step = np.abs(np.diff(zv[i, :, end]))
            k = step.argmax()
            left, right = zphase[k:k+2]
            zooms.append(dict(phase_interval=[float(left), float(right)],
                              max_mirror_jump=float(step[k]), u=extent(zu[i, k:k+2]),
                              mirror_phi=zv[i, k:k+2, end].tolist(),
                              j_residual=extent(zr[i, k:k+2])))
        regularity.append(dict(side=['left', 'right'][end], initial_jump=float(jumps[i].max()),
                               zooms=zooms))
    return dict(fractions=fractions, energies=heights[indices].tolist(),
                fixed_j=float(direction*target), max_j_residual=float(np.max(np.abs(residual))),
                phases=nphase, u_ranges=[extent(g) for g in guess],
                min_u_separation=float(np.min(np.abs(guess[0]-guess[1]))),
                min_launch_chord=float(np.min(np.linalg.norm(origin[:, 0]-origin[:, 1], axis=0))),
                min_mirror_slopes=np.min(v[..., 3], axis=1).tolist(),
                min_critical_height_gaps=np.min(v[..., 2], axis=1).tolist(),
                mirror_refinement=regularity,
                scaled_half_periods=[extent(v[i, :, 5]) for i in range(2)])


def ripple_crossing(ev, seeds, h, target, alpha, u0, mirror, nstep):
    """Probe opposite sides of a local field-strength maximum found by the phase zoom."""
    phase = np.array([alpha])

    def sample(us):
        t, b, ds, _, _ = trace(ev, seeds, us[:, None], phase, nstep, 3e-13)
        return t, b[:, 0], ds[:, 0]

    def local_max(t, bb):
        profile = CubicSpline(t, bb)
        roots = profile.derivative().roots(extrapolate=False)
        maxima = roots[profile(roots, 2) < 0]
        near = maxima[np.argmin(np.abs(maxima-mirror))]
        if abs(near-mirror) > 0.1:
            raise ValueError('could not track the same local maximum')
        return near, profile(near)-h

    us = np.linspace(u0-0.008, u0+0.008, 33)
    t, b, _ = sample(us)
    differences = np.array([local_max(t, line)[1] for line in b])
    crossings = np.flatnonzero(differences[:-1]*differences[1:] < 0)
    if len(crossings) != 1:
        raise ValueError('local maximum does not cross the selected mirror height once')
    k = crossings[0]
    fold_u = us[k]-differences[k]*(us[k+1]-us[k])/(differences[k+1]-differences[k])
    # Signed samples, deliberately wider than numerical uncertainty. This does
    # not bound the continuum or prove global absence of some other level.
    us = fold_u + np.array([-1e-6, 1e-6])
    t, b, ds = sample(us)
    sides = []
    for u, line, length in zip(us, b, ds):
        critical_phi, difference = local_max(t, line)
        v = leg(t, line, length, [h], leggauss(16))[0]
        sides.append(dict(u=float(u), critical_phi=float(critical_phi),
                          critical_minus_h=float(difference), j_minus_target=float(v[4]-target),
                          mirror_phi=float(v[1 if mirror > 0 else 0])))
    return dict(fold_u=float(fold_u), sides=sides)


def local_patch(ev, seeds, heights, nrad, nphase, nstep):
    """Test simple roots throughout the central mirror-height interval on a local launch patch.

    Uniform sign conditions use extrema of each fitted cubic over closed time intervals.
    Radial and phase dependence and the underlying field-line ODE are sampled.
    """
    u = np.linspace(0.45, 0.53, nrad)[:, None]
    alpha = np.linspace(-np.pi/64, np.pi/64, nphase)
    t, b, _, _, _ = trace(ev, seeds, u, alpha, nstep, 1e-12)
    inner, outer = 7.416, 7.590
    low, high = heights
    margins = []
    for line in b.reshape(-1, len(t)):
        p = CubicSpline(t, line)
        extrema = p.derivative().roots(extrapolate=False)
        stationary_slopes = p.derivative(2).roots(extrapolate=False)
        center = np.r_[-inner, extrema[np.abs(extrema) < inner], inner]
        right = np.r_[inner, stationary_slopes[(inner < stationary_slopes)
                                                & (stationary_slopes < outer)], outer]
        left = np.r_[-outer, stationary_slopes[(-outer < stationary_slopes)
                                               & (stationary_slopes < -inner)], -inner]
        margins.append([low-max(p(center)), min(p(-outer), p(outer))-high,
                        min(-p(left, 1)), min(p(right, 1))])
    names = ['center_below_h', 'outside_above_h', 'left_decrease', 'right_increase']
    return dict(zip(names, np.min(margins, axis=0).tolist()))


def deep_strip(ev, seeds, heights, target, nrad, nphase, nstep):
    """Check oriented crossings and radial action differences across the whole deep strip."""
    us = np.linspace(0.44, 0.54, nrad)
    alpha = np.arange(nphase)*np.pi/nphase
    t, fields, arclength, _, _ = trace(ev, seeds, us[:, None], alpha, nstep, 1e-12)
    low, high = heights
    half_width = 6.1
    margins, action = [], np.zeros((nrad, nphase, 2))
    quadrature = leggauss(12)
    for i, section in enumerate(fields):
        for k, line in enumerate(section):
            p = CubicSpline(t, line)
            # Extrema of the signed slope subject to low <= |B| <= high occur at
            # threshold crossings, stationary slopes, or the trace endpoints.
            crossings = np.r_[p.solve(low, extrapolate=False), p.solve(high, extrapolate=False)]
            extrema = p.derivative(2).roots(extrapolate=False)
            extra = np.r_[extrema, -half_width, 0., half_width]
            extra = extra[(low <= p(extra)) & (p(extra) <= high)]
            candidates = np.r_[crossings, extra]
            left = candidates[(-half_width <= candidates) & (candidates < 0)]
            right = candidates[(0 < candidates) & (candidates <= half_width)]
            if not len(left) or not len(right):
                raise ValueError('deep-strip energy window has an unbracketed mirror')
            margins.append([low-p(0), min(p(-half_width), p(half_width))-high,
                            min(-p(left, 1)), min(p(right, 1))])
            action[i, k] = leg(t, line, arclength[i, k], heights, quadrature)[:, 4]
    names = ['launch_below_h', 'both_ends_above_h', 'left_decrease', 'right_increase']
    result = dict(zip(names, np.min(margins, axis=0).tolist()))
    result.update(min_radial_action_secant=float(np.min(np.diff(action, axis=0))/np.diff(us)[0]),
                  min_inner_action_margin=float(target-np.max(action[0])),
                  min_outer_action_margin=float(np.min(action[-1])-target))
    return result


def check_parabolic_well():
    """Parabolic |B|=1+t^2 with unit arclength has known mirrors, action and period."""
    t = np.linspace(-2., 2., 65)
    v = leg(t, 1+t*t, np.ones_like(t), [2.], leggauss(16))[0]
    np.testing.assert_allclose(v[[0, 1, 4, 5]], [-1, 1, np.pi/np.sqrt(2), np.pi/np.sqrt(2)],
                               rtol=1e-10, atol=1e-10)


def main():
    check_parabolic_well()
    ev, seeds = load_inputs()
    # Both resolutions use the same physical heights and the same root-selection rules.
    h, coarse, _, _ = resolution(ev, seeds, np.linspace(0., 1., 5)[:, None],
                                 16, 384, 8, 1e-10)
    _, fine, flux, origin = resolution(ev, seeds, np.linspace(0., 1., 9)[:, None],
                                       32, 768, 12, 1e-12, h)
    result = summarize(h, fine, flux, origin)
    delta = np.max(np.abs(coarse - fine[::2, ::2]), axis=(0, 1, 2))
    result['comparison'] = dict(max_abs_left=float(delta[0]), max_abs_right=float(delta[1]),
                                max_abs_j=float(delta[4]), max_abs_jh=float(delta[5]))
    screens = [trace_contours(ev, seeds, h, fine, fractions, 128) for fractions in SCREENS]
    result['fixed_action_screens'] = screens
    # Reproducible witness rays selected after localizing the first two mirror jumps.
    witnesses = [(0.495, 2.8108, 0.519, 7.4), (0.505, 0.36725, 0.454, -7.44)]
    result['ripple_crossings'] = []
    for fraction, alpha, u0, mirror in witnesses:
        height = h[FRACTIONS.index(fraction)]
        case = dict(h=float(height), alpha=alpha, refinements=[
            ripple_crossing(ev, seeds, height, screens[0]['fixed_j'], alpha, u0, mirror, nstep)
            for nstep in (1024, 2048)])
        result['ripple_crossings'].append(case)
    hs = h[[FRACTIONS.index(.495), FRACTIONS.index(.505)]]
    result['local_patch'] = dict(u=[.45, .53], alpha=[-np.pi/64, np.pi/64],
                                 absolute_mirror_bracket=[7.416, 7.590], h=hs.tolist(),
                                 grids=[[5, 9, 768], [9, 17, 1536]], refinements=[
                                     local_patch(ev, seeds, hs, *grid)
                                     for grid in [(5, 9, 768), (9, 17, 1536)]])
    hs = h[[FRACTIONS.index(.195), FRACTIONS.index(.205)]]
    result['deep_strip'] = dict(u=[.44, .54], alpha_period=np.pi, half_trace_window=6.1,
                                h=hs.tolist(), grids=[[5, 64, 768], [9, 128, 1536]],
                                refinements=[deep_strip(ev, seeds, hs, screens[1]['fixed_j'], *grid)
                                             for grid in [(5, 64, 768), (9, 128, 1536)]])
    result['method'] = dict(status='untrusted floating-point screen',
                            numpy=np.__version__, scipy=scipy.__version__,
                            mirror_height_fractions=FRACTIONS, screen_order=SCREENS,
                            full_grids_radial_phase_half_trace=[[5, 16, 384], [9, 32, 768]])
    result['field_file_sha256'] = FIELD_FILE_SHA
    result['seeds'] = {tag: dict(seed_sha256=digest, theta_launch=float(theta))
                       for (tag, (_, digest)), (_, theta) in zip(SEEDS.items(), seeds)}
    print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == '__main__':
    main()
