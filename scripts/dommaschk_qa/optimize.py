"""UNTRUSTED numerics (Q-16, N-31).  Quasi-axisymmetric (QA) fit of a Dommaschk vacuum field.

    B = grad(phi + sum_k a_k V_k),  V_k the stellarator-symmetric Dommaschk potentials of basis.py
    (exactly harmonic: the candidate is a vacuum field, J = 0, zero net toroidal current, by
    construction; C1 of the stellarator contract then reduces to iota >= iota_min).

Two least-squares stages per start (scipy least_squares, trust-region reflective, Jacobian by
forward differences with all columns integrated in ONE batched run):

Stage A (cheap, axis only):
    w_iota max(0, 1.2 iota_min - |iota_axis|)^2/(1.2 iota_min)^2      on-axis transform (monodromy)
  + w_axis max(0, z_min - zrms_axis)^2/z_min^2                         non-planar axis
  + w_bax sum (|B|_axis/mean - 1)^2                                    |B| constant on the axis
  + regularisation (below).
Stage B (full objective), on the flux surfaces launched at distances r_j (--surfaces) outboard of
the magnetic axis on the plane phi = 0:
    sum_j  sum_{(m,n), n != 0} |2 c_mn / c_00|^2 / max(|iota_j|, iota_min)^2   QA defect relative to iota
  + w_iota sum_j max(0, iota_min - |iota_j|)^2 / iota_min^2                     iota >= iota_min
  + the stage-A axis terms (iota_axis, non-planarity)
  + w_conv sum_j min(birkhoff_err_j / 1e-6, 100)^2                            regular (non-chaotic) lines
  + lam sum_k s_k^2 (a_k - a_seed_k)^2                                        regularisation
  [+ w_window sum (dist(|iota|, [lo, hi]) / (hi - lo))^2 over the axis and all surfaces, with
     --iota-window lo,hi (off by default): keeps the whole transform profile inside a window
     free of low-order rationals iota = NFP k/m, so that no low-order island chain crosses the
     target surfaces (N-31 sections 8-9); also applied to the axis in stage A]
A lost or undefined surface contributes a constant penalty (the other surfaces stay live).

c_mn: Boozer coefficients of |B| (fieldeval.py, exact vacuum Boozer angles phi_B = Phi), modes
0 <= m <= --mmax, |n| <= --nmodes (n in units of NFP).  The first term is the Q-16 ratio
(defect / |iota|) squared when |iota_j| >= iota_min.  The sign of iota depends on the orientation
(mirror images have opposite signs), so constraints use |iota|.  s_k = RMS of |grad V_k| near the
seed axis, so perturbations, trust region and regularisation are measured in field units.  For a
stellarator-symmetric field with NFP >= 2 the axis is planar iff z_axis = 0, so zrms_axis measures
non-planarity.

Seed (documented choice): the target magnetic axis of the near-axis QA example of Landreman,
Sengupta, Plunk, J. Plasma Phys. 85 (2019) 905850103, section 5.1 ("r1"):
    R_t(phi) = 1 + Delta cos(NFP phi),  z_t(phi) = -Delta sin(NFP phi),  Delta = 0.045, NFP = 2
(their example has iota ~ 0.42 at eta-bar 0.9).  The seed solves the LINEAR least-squares problem
"B parallel to the target axis and |B| constant on it" for the coefficients (B is linear in a);
random starts add field-scaled random perturbations (scale --sigma) and re-project on the same
axis conditions.  Start 0 is the unperturbed seed.

Warm start (--init FILE): instead of the seed, start from an earlier field. FILE is a
candidate.json (coefficients matched to this basis by name, so a smaller basis embeds into a
larger one; exact rational coefficients are used) or a work-directory start_NNN.json (same basis
size required).  Start 0 is the initial field itself, start k >= 1 adds a field-scaled random
perturbation of size --init-sigma (no re-projection on the seed's axis conditions).  Warm starts
skip stage A (the axis-only objective would undo a good field), regularise towards the initial
field instead of the seed, and use its magnetic axis as the first axis guess.

Restartable: everything lives in --work (one directory per parameter set); finished starts are
skipped, interrupted starts resume from their checkpoint.  Parallel over starts with --jobs.
The final candidate (best start) is rounded to exact decimal rationals and passed to
diagnostics.py, which recomputes everything on the ROUNDED field and writes --results.

usage: python optimize.py --work DIR --results DIR [--nmax 2 --lmax 4 --starts 8 --jobs 8 ...]
"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, argparse, hashlib, traceback
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.optimize import least_squares

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from basis import basis                     # noqa: E402
import fieldeval as fe                      # noqa: E402

FAIL = 1.0


def parse(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--work', required=True)
    ap.add_argument('--results', default=None, help='results directory (diagnostics); none = skip')
    ap.add_argument('--nfp', type=int, default=2)
    ap.add_argument('--nmax', type=int, default=2, help='Dommaschk order: m = NFP*i, i <= nmax')
    ap.add_argument('--lmax', type=int, default=None, help='max z-degree l (default nmax + 2)')
    ap.add_argument('--starts', type=int, default=4)
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--iota-min', type=float, default=0.2)
    ap.add_argument('--surfaces', default='0.02,0.04,0.06', help='launch distances from the axis')
    ap.add_argument('--axis-delta', type=float, default=0.045)
    ap.add_argument('--zmin', type=float, default=0.01, help='minimum RMS z of the axis')
    ap.add_argument('--sigma', type=float, default=0.005, help='random start scale (field units)')
    ap.add_argument('--lam', type=float, default=1e-4)
    ap.add_argument('--w-iota', type=float, default=1.0)
    ap.add_argument('--w-axis', type=float, default=1.0)
    ap.add_argument('--w-conv', type=float, default=0.002)
    ap.add_argument('--w-bax', type=float, default=0.3, help='stage A: |B| constant on the axis')
    ap.add_argument('--mmax', type=int, default=4)
    ap.add_argument('--nmodes', type=int, default=6)
    ap.add_argument('--ns', type=int, default=48, help='RK4 steps per field period (optimiser)')
    ap.add_argument('--nper', type=int, default=200, help='field periods traced (optimiser)')
    ap.add_argument('--max-nfev', type=int, default=40)
    ap.add_argument('--time-limit', type=float, default=3600.0, help='seconds per start')
    ap.add_argument('--seed', type=int, default=12345)
    ap.add_argument('--decimals', type=int, default=10, help='rounding of exported coefficients')
    ap.add_argument('--diag-ns', type=int, default=96)
    ap.add_argument('--diag-nper', type=int, default=600)
    ap.add_argument('--diag-lines', type=int, default=12)
    ap.add_argument('--eps-transits', type=int, default=100)
    ap.add_argument('--init', default=None,
                    help='warm start: candidate.json or start_NNN.json of an earlier run')
    ap.add_argument('--init-sigma', type=float, default=0.001,
                    help='warm start: random perturbation scale (field units)')
    ap.add_argument('--iota-window', default=None,
                    help='lo,hi: keep |iota| on the axis and all surfaces in [lo, hi] (off by default)')
    ap.add_argument('--w-window', type=float, default=1.0)
    ap.add_argument('--force', action='store_true', help='reuse --work even if parameters changed')
    a = ap.parse_args(argv)
    if a.lmax is None:
        a.lmax = a.nmax + 2
    a.surfaces = [float(s) for s in a.surfaces.split(',')]
    if a.iota_window is not None:
        a.iota_window = [float(s) for s in a.iota_window.split(',')]
        assert len(a.iota_window) == 2 and 0 <= a.iota_window[0] < a.iota_window[1]
    return a


OPT_KEYS = ('nfp', 'nmax', 'lmax', 'iota_min', 'surfaces', 'axis_delta', 'zmin', 'sigma', 'lam',
            'w_iota', 'w_axis', 'w_conv', 'w_bax', 'mmax', 'nmodes', 'ns', 'nper', 'max_nfev', 'seed')
WINDOW_KEYS = ('iota_window', 'w_window')   # in the configuration only when --iota-window is set
INIT_KEYS = ('init', 'init_sha256', 'init_sigma')   # only when --init is set


def load_init(path, b):
    """Initial coefficients for basis b and the initial axis guess, from candidate.json (matched
    by basis name; exact rationals) or start_NNN.json (same size)."""
    d = json.load(open(path))
    if 'basis' in d:
        names = [bk['name'] for bk in d['basis']]
        coef = dict(zip(names, (float(Fraction(c)) for c in d['coefficients'])))
        mine = {bk['name'] for bk in b}
        extra = [n for n, v in coef.items() if n not in mine and v != 0]
        if extra:
            sys.exit(f'--init: {len(extra)} nonzero coefficients not in this basis, e.g. {extra[0]}')
        x = np.array([coef.get(bk['name'], 0.0) for bk in b])
        m = d.get('optimiser_metrics', {})
    else:
        x = np.array(d['x'], dtype=float)
        if len(x) != len(b):
            sys.exit(f'--init: {len(x)} coefficients, this basis has {len(b)}')
        m = d.get('metrics', {})
    axis = (m['axis_R'], m['axis_z']) if 'axis_R' in m else None
    return x, axis


def window_dist(cfg, aiota):
    """(distance of |iota| from the window) / (window width); 0 inside or without a window."""
    w = cfg.get('iota_window')
    if not w:
        return 0.0
    return (max(0.0, w[0] - aiota) + max(0.0, aiota - w[1]))/(w[1] - w[0])


# ---------------------------------------------------------------- problem
class Problem:
    def __init__(self, cfg):
        self.cfg = cfg
        self.b = basis(cfg['nfp'], cfg['nmax'], cfg['lmax'])
        self.tab = fe.Tables(self.b, cfg['nfp'])
        self.nb = len(self.b)
        self.rs = np.array(cfg['surfaces'])
        self.axis_guess = (1.0 + cfg['axis_delta'], 0.0)
        self._seed_system()
        self.x_init = None
        if cfg.get('init'):
            self.x_init, ax = load_init(cfg['init'], self.b)
            self.x_seed = self.x_init.copy()     # regularise towards the initial field
            if ax is not None:
                self.axis_guess = ax

    # ---- seed: linear conditions on the target axis
    def _target_axis(self, n=64):
        N, D = self.cfg['nfp'], self.cfg['axis_delta']
        ph = 2*np.pi/N*np.arange(n)/n
        R = 1 + D*np.cos(N*ph); z = -D*np.sin(N*ph)
        dR = -N*D*np.sin(N*ph); dz = -N*D*np.cos(N*ph)
        t = np.array([dR, R, dz]); t /= np.sqrt((t**2).sum(0))
        return ph, R, z, t

    def _grad_basis(self, ph, R, z):
        """grad V_k at points (one phi per point): (3, nb, npts); and base grad phi (3, npts)."""
        G = np.zeros((3, self.nb, len(ph)))
        W = np.transpose(self.tab.A, (0, 1, 2))          # (4, nf, nb): configurations = basis
        for i in range(len(ph)):
            G[:, :, i] = self.tab.eval(W, np.full((self.nb, 1), R[i]), ph[i],
                                       np.full((self.nb, 1), z[i]))[:, :, 0]
        base = np.array([0*R, 1/R, 0*R])
        return G, base

    def _seed_system(self):
        ph, R, z, t = self._target_axis()
        G, base = self._grad_basis(ph, R, z)
        # B x t = 0 (3 eqs) and B.t - B0 = 0 with B0 unknown: unknowns (a, B0)
        rows, rhs = [], []
        cr = lambda u, v: np.array([u[1]*v[2] - u[2]*v[1], u[2]*v[0] - u[0]*v[2], u[0]*v[1] - u[1]*v[0]])
        Gx = cr(G, t[:, None, :])                        # (3, nb, npts)
        bx = cr(base, t)                                 # (3, npts)
        for c in range(3):
            rows.append(np.hstack([Gx[c].T, np.zeros((len(ph), 1))])); rhs.append(-bx[c])
        Gt = (G*t[:, None, :]).sum(0); bt = (base*t).sum(0)
        rows.append(np.hstack([Gt.T, -np.ones((len(ph), 1))])); rhs.append(-bt)
        self.E = np.vstack(rows); self.e = np.concatenate(rhs)
        # field scale s_k: RMS |grad V_k| on a torus of radius 0.1 about the target axis
        th = np.linspace(0, 2*np.pi, 8, endpoint=False)
        PH = np.repeat(ph[::8], len(th)); TH = np.tile(th, len(ph[::8]))
        Rr = np.repeat(R[::8], len(th)) + 0.1*np.cos(TH); zz = np.repeat(z[::8], len(th)) + 0.1*np.sin(TH)
        Gs, _ = self._grad_basis(PH, Rr, zz)
        self.s = np.sqrt((Gs**2).sum(0).mean(1)) + 1e-12
        self.x_seed = self.project(np.zeros(self.nb), mu=1e-6)

    def project(self, target, mu):
        """argmin |E (a, B0) - e|^2 + mu |s (a - target)|^2."""
        S = np.hstack([np.diag(self.s), np.zeros((self.nb, 1))])
        A = np.vstack([self.E, np.sqrt(mu)*S]); r = np.concatenate([self.e, np.sqrt(mu)*self.s*target])
        sol, *_ = np.linalg.lstsq(A, r, rcond=None)
        return sol[:self.nb]

    def start_point(self, k):
        if self.x_init is not None:
            if k == 0:
                return self.x_init.copy()
            rng = np.random.default_rng(self.cfg['seed'] + 7919*k)
            return self.x_init + self.cfg['init_sigma']*rng.standard_normal(self.nb)/self.s
        if k == 0:
            return self.x_seed.copy()
        rng = np.random.default_rng(self.cfg['seed'] + 7919*k)
        tgt = self.x_seed + self.cfg['sigma']*rng.standard_normal(self.nb)/self.s
        return self.project(tgt, mu=1e-2)

    # ---- evaluation of many configurations at once
    def _axis(self, W, nc, ns, axis_guess):
        c = self.cfg
        g = axis_guess or self.axis_guess
        Ra, za, ok, M = fe.find_axis(self.tab, W, np.full(nc, g[0]), np.full(nc, g[1]), ns)
        ph, Rc, zc = fe.axis_curve(self.tab, W, Ra, za, ns)
        zrms = np.sqrt((zc**2).mean(1)); zmax = np.abs(zc).max(1)
        # |iota| on the axis from the monodromy: eigenvalues exp(+-2 pi i iota / NFP)
        tr = M[:, 0, 0] + M[:, 1, 1]
        iota_ax = c['nfp']/(2*np.pi)*np.arccos(np.clip(tr/2, -1, 1))
        Bax = np.array([np.sqrt((self.tab.eval(W, Rc[:, [j]], ph[j], zc[:, [j]])**2).sum(0))[:, 0]
                        for j in range(0, len(ph), 4)]).T
        Bvar = (Bax - Bax.mean(1, keepdims=True))/Bax.mean(1, keepdims=True)
        return dict(Ra=Ra, za=za, ok=ok, zrms=zrms, zmax=zmax, iota_ax=iota_ax, Bvar=Bvar)

    def _r_axis(self, ax, i):
        c = self.cfg
        tgt = 1.2*c['iota_min']
        r = [c['w_iota']*max(0.0, tgt - ax['iota_ax'][i])/tgt if ax['ok'][i] else FAIL,
             c['w_axis']*max(0.0, c['zmin'] - ax['zrms'][i])/c['zmin']]
        if c.get('iota_window'):
            r.append(c['w_window']*window_dist(c, ax['iota_ax'][i]) if ax['ok'][i] else FAIL)
        return r

    def evaluate_axis(self, X, axis_guess=None):
        """Stage A residuals (cheap, axis only): |iota_axis| >= 1.2 iota_min, non-planar axis,
        |B| constant on the axis (first-order QA requirement), regularisation."""
        c = self.cfg
        X = np.atleast_2d(X); nc = X.shape[0]
        ax = self._axis(self.tab.weights(X), nc, c['ns'], axis_guess)
        res = []
        for i in range(nc):
            r = np.concatenate([self._r_axis(ax, i), c['w_bax']*ax['Bvar'][i] if ax['ok'][i]
                                else np.full(ax['Bvar'].shape[1], FAIL),
                                np.sqrt(c['lam'])*self.s*(X[i] - self.x_seed)])
            res.append(np.nan_to_num(r, nan=FAIL, posinf=FAIL, neginf=-FAIL))
        return np.array(res), ax

    def evaluate(self, X, ns=None, nper=None, axis_guess=None):
        """Stage B residuals (full objective, see the module docstring) and metrics."""
        c = self.cfg
        ns = ns or c['ns']; nper = nper or c['nper']
        X = np.atleast_2d(X); nc = X.shape[0]
        W = self.tab.weights(X)
        ax = self._axis(W, nc, ns, axis_guess)
        Ra, za = ax['Ra'], ax['za']
        R0 = Ra[:, None] + self.rs[None]; z0 = np.repeat(za[:, None], len(self.rs), 1)
        sec, Bm, Jac, Phi, lost = fe.trace_surfaces(self.tab, W, R0, z0, ns, nper)
        io, err = fe.iota_from_sections(sec, Ra, za, c['nfp'])   # signed (orientation-dependent)
        cm, jm = fe.boozer_coeffs(Bm, Jac, Phi, io, c['nfp'], c['mmax'], c['nmodes'])
        bad = fe.qa_bad_modes(cm, c['nmodes'])                      # (nc, nsurf, nbad)
        gs = ax['ok'][:, None] & ~lost & np.isfinite(bad).all(2) & np.isfinite(io)   # per surface
        good = gs.all(1)
        aio = np.abs(io)
        defect = np.sqrt((np.abs(bad)**2).sum(-1))     # sqrt(sum_{n != 0} A_mn^2)/B00 (boozer.qs_defect)
        win = bool(c.get('iota_window'))
        res = []
        for i in range(nc):
            parts = []
            for j in range(len(self.rs)):
                if gs[i, j]:
                    r_qs = bad[i, j]/max(aio[i, j], c['iota_min'])
                    parts += [np.real(r_qs), np.imag(r_qs),
                              [c['w_iota']*max(0.0, c['iota_min'] - aio[i, j])/c['iota_min'],
                               c['w_conv']*min(err[i, j]/1e-6, 100.0)]]
                    if win:
                        parts.append([c['w_window']*window_dist(c, aio[i, j])])
                else:   # lost or undefined surface: constant penalty (other surfaces stay live)
                    parts.append(np.full(2*bad.shape[2] + 2 + win, FAIL))
            parts += [self._r_axis(ax, i), np.sqrt(c['lam'])*self.s*(X[i] - self.x_seed)]
            r = np.concatenate([np.ravel(v) for v in parts])
            res.append(np.nan_to_num(r, nan=FAIL, posinf=FAIL, neginf=-FAIL))
        info = dict(ok=good, axis=(Ra, za), zrms=ax['zrms'], zmax=ax['zmax'], iota_axis=ax['iota_ax'],
                    iota=io, err=err, defect=defect, ratio=defect/np.maximum(aio, 1e-9), meanjac=jm)
        return np.array(res), info


def metrics_of(info, i=0):
    return dict(ok=bool(info['ok'][i]), axis_R=float(info['axis'][0][i]), axis_z=float(info['axis'][1][i]),
                axis_zrms=float(info['zrms'][i]), axis_zmax=float(info['zmax'][i]),
                iota_axis_abs=float(info['iota_axis'][i]),
                iota=info['iota'][i].tolist(), birkhoff_err=info['err'][i].tolist(),
                qa_defect=info['defect'][i].tolist(), defect_over_iota=info['ratio'][i].tolist(),
                mean_jacobian=info['meanjac'][i].tolist())


# ---------------------------------------------------------------- one start (worker)
class Timeout(Exception):
    pass


def run_start(args):
    """Stage A (axis: iota, non-planarity, constant |B| on axis), then stage B (full QA objective).
    Restartable: checkpoints every 30 s; a finished start is never redone."""
    cfg, work, k, time_limit = args
    done = os.path.join(work, f'start_{k:03d}.json')
    if os.path.exists(done):
        return json.load(open(done))
    ck = os.path.join(work, f'start_{k:03d}.ckpt.json')
    P = Problem(cfg)
    x0 = P.start_point(k)
    stage0, resumed, axis0 = ('B' if cfg.get('init') else 'A'), False, None
    if os.path.exists(ck):
        d = json.load(open(ck)); x0 = np.array(d['x']); stage0 = d['stage']; resumed = True
        axis0 = tuple(d['axis']) if d.get('axis') else None
    t0 = time.time()
    log = []

    def solve(stage, x0, max_nfev, axis0):
        ev = P.evaluate_axis if stage == 'A' else P.evaluate
        st = dict(best=np.inf, xbest=x0.copy(), last_x=None, last_r=None, nfev=0, tck=0.0, axis=axis0, axis_best=axis0)

        def note(x, r):
            cost = 0.5*float(r @ r)
            if cost < st['best']:
                st['best'] = cost; st['xbest'] = x.copy(); st['axis_best'] = st['axis']
            if time.time() - st['tck'] > 30:
                json.dump(dict(x=st['xbest'].tolist(), cost=st['best'], stage=stage, axis=st['axis_best']),
                          open(ck + '.tmp', 'w'))
                os.replace(ck + '.tmp', ck); st['tck'] = time.time()
            if time.time() - t0 > time_limit:
                raise Timeout()

        def fun(x):
            r, info = ev(x[None], axis_guess=st['axis'])
            okk = info['ok'][0]
            if okk:
                Ra, za = (info['Ra'], info['za']) if stage == 'A' else info['axis']
                st['axis'] = (float(Ra[0]), float(za[0]))
            st['last_x'] = x.copy(); st['last_r'] = r[0]; st['nfev'] += 1
            note(x, r[0])
            return r[0]

        def jac(x):
            h = 1e-6*(1 + np.abs(x))*np.median(P.s)/P.s
            if st['last_x'] is None or not np.array_equal(st['last_x'], x):
                fun(x)
            r, _ = ev(x[None] + np.diag(h), axis_guess=st['axis'])
            note(x, st['last_r'])
            return ((r - st['last_r'][None])/h[:, None]).T

        r0 = fun(x0)
        cost0 = 0.5*float(r0 @ r0)
        status = 'ok'
        try:
            sol = least_squares(fun, x0, jac=jac, method='trf', x_scale=0.01/P.s, max_nfev=max_nfev,
                                ftol=1e-10, xtol=1e-10, gtol=1e-10)
            msg = sol.message
        except Timeout:
            msg, status = 'time limit reached; best point kept', 'timeout'
        log.append(dict(stage=stage, status=status, message=str(msg), nfev=st['nfev'], cost0=cost0,
                        cost=st['best']))
        return st['xbest'], status, st['axis_best']

    status = 'ok'
    try:
        x = x0
        if stage0 == 'A':
            x, status, axis0 = solve('A', x, 4*cfg['max_nfev'], axis0)
        if status == 'ok':
            x, status, axis0 = solve('B', x, cfg['max_nfev'], axis0)
    except Exception as ex:  # a failed start must not kill the others
        status = 'error'; log.append(dict(error=repr(ex)))
        traceback.print_exc()
        x = x0
    _, info = P.evaluate(x[None], axis_guess=axis0)
    out = dict(start=k, status=status, resumed=resumed, log=log, seconds=time.time() - t0,
               cost=log[-1].get('cost', np.inf) if log else np.inf, x=list(map(float, x)),
               metrics=metrics_of(info))
    json.dump(out, open(done + '.tmp', 'w'), indent=1)
    os.replace(done + '.tmp', done)
    m = out['metrics']
    print(f"[start {k}] {status} {[(l.get('stage'), l.get('nfev'), '%.3g -> %.3g' % (l.get('cost0', np.nan), l.get('cost', np.nan))) for l in log]}; "
          f"ok={m['ok']} |iota_axis| {m['iota_axis_abs']:.4f} iota {np.round(m['iota'], 4).tolist()} "
          f"defect/|iota| {np.round(m['defect_over_iota'], 4).tolist()} axis zrms {m['axis_zrms']:.4f} "
          f"({out['seconds']:.0f} s)", flush=True)
    return out


def merit(out, cfg):
    """Selection: feasible (ok, iota >= iota_min on all surfaces, axis non-planar) first, then the
    worst defect/iota; infeasible ones by cost."""
    m = out['metrics']
    feas = m['ok'] and min(np.abs(m['iota'])) >= cfg['iota_min'] and m['axis_zrms'] >= cfg['zmin']
    feas = feas and all(window_dist(cfg, abs(v)) == 0 for v in m['iota'] + [m['iota_axis_abs']])
    return (0, max(m['defect_over_iota'])) if feas else (1, out['cost'])


def to_rational(x, decimals):
    return [Fraction(int(round(v*10**decimals)), 10**decimals) for v in x]


def main(argv=None):
    a = parse(argv)
    cfg = {k: getattr(a, k) for k in OPT_KEYS}
    if a.iota_window is not None:
        cfg.update({k: getattr(a, k) for k in WINDOW_KEYS})
    if a.init is not None:
        a.init_sha256 = hashlib.sha256(open(a.init, 'rb').read()).hexdigest()
        cfg.update({k: getattr(a, k) for k in INIT_KEYS})
    os.makedirs(a.work, exist_ok=True)
    cpath = os.path.join(a.work, 'config.json')
    if os.path.exists(cpath) and not a.force:
        old = json.load(open(cpath))
        if old != json.loads(json.dumps(cfg)):
            sys.exit(f"{cpath} has different parameters; use another --work or --force")
    json.dump(cfg, open(cpath, 'w'), indent=1)
    P = Problem(cfg)
    print(f"Dommaschk QA fit: NFP={a.nfp} nmax={a.nmax} lmax={a.lmax}: {P.nb} coefficients, "
          f"{a.starts} starts, {a.jobs} jobs; surfaces {a.surfaces}; iota_min {a.iota_min}"
          + (f"; iota window {a.iota_window}" if a.iota_window else '')
          + (f"; warm start from {a.init} (sigma {a.init_sigma})" if a.init else ''), flush=True)
    t0 = time.time()
    jobs = [(cfg, a.work, k, a.time_limit) for k in range(a.starts)]
    if a.jobs > 1 and a.starts > 1:
        with ProcessPoolExecutor(max_workers=min(a.jobs, a.starts)) as ex:
            outs = list(ex.map(run_start, jobs))
    else:
        outs = [run_start(j) for j in jobs]
    outs.sort(key=lambda o: merit(o, cfg))
    best = outs[0]
    print(f"best start {best['start']} ({time.time() - t0:.0f} s for the starts)", flush=True)
    q = to_rational(best['x'], a.decimals)
    cand = dict(
        description='Dommaschk vacuum field B = grad(phi + sum_k a_k V_k), cylindrical (R, phi, z), '
                    'R0 = B0R0 = 1; V_k = trig(m phi) * (D or N)_{m,l}(R, z), each a sum of exact '
                    'terms c R^p (ln R)^q z^j (basis.py, Dommaschk 1986 structure). UNTRUSTED fit.',
        nfp=a.nfp, nmax=a.nmax, lmax=a.lmax, decimals=a.decimals,
        basis=[dict(name=bk['name'], kind=bk['kind'], m=bk['m'], l=bk['l'], trig=bk['trig'],
                    terms=[[str(c), p, qq, j] for c, p, qq, j in bk['terms']]) for bk in P.b],
        coefficients=[str(v) for v in q],
        coefficients_float=best['x'], start=best['start'], optimiser_metrics=best['metrics'])
    cand['sha256'] = hashlib.sha256(json.dumps([cand['coefficients'], cand['basis']]).encode()).hexdigest()
    json.dump(cand, open(os.path.join(a.work, 'candidate.json'), 'w'), indent=1)
    json.dump([{k: v for k, v in o.items() if k != 'x'} for o in outs],
              open(os.path.join(a.work, 'starts.json'), 'w'), indent=1)
    if a.results:
        import diagnostics
        diagnostics.run(os.path.join(a.work, 'candidate.json'), a.results, cfg=cfg, args=a,
                        starts=os.path.join(a.work, 'starts.json'))


if __name__ == '__main__':
    main()
