"""UNTRUSTED numerics (Q-16, N-31).  Diagnostics of a Dommaschk QA candidate, recomputed on the
ROUNDED (exact rational) coefficients that are exported for the certificate stage.

  1. the field rebuilt independently in sympy from the exact basis terms; the fast evaluator is
     checked against it at random points;
  2. magnetic axis (Newton on the period map), its curvature and torsion, non-planarity
     (stellarator symmetry + NFP >= 2: planar <=> z_axis = 0);
  3. Poincare sections at phi = 0 and phi = pi/NFP; nested-surface check: no line lost, Birkhoff
     rotation number converged (first/second half agree to --nest-tol), section areas increasing;
  4. iota profile;
  5. Boozer spectrum of |B| (exact vacuum Boozer angles, fieldeval.py) and the quasisymmetry defect
     for every helicity of scripts/c2_diagnostics/boozer.py (qs_defect, amplitudes, derivative_sup
     reused), the Lean-form QA defect delta = sup|d_phiB B| and kappa = 2 delta/(B_min |iota|) of the
     per-bounce bridge (N-29);
  6. eps_eff by Nemov's formula (scripts/c2_diagnostics/nemov.py, validated there on the classical
     stellarator limit), lines started on the section conjugacy K(alpha) with tangent K'(alpha);
  7. the Q-16 ratio defect/|iota| and a verdict;
  8. PNG plots (Poincare, profiles, |B| in Boozer angles), summary.json.

usage: python diagnostics.py CANDIDATE.json RESULTS_DIR [--surfaces ... --iota-min ...]
"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, shutil, argparse
from fractions import Fraction
import numpy as np
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'c2_diagnostics'))
import fieldeval as fe                                  # noqa: E402
import boozer as c2b                                    # noqa: E402  (imports the Q-19 field module)
from tori import conjugacy, K_eval, rk4                 # noqa: E402
from nemov import nemov_sums, eps_eff_from              # noqa: E402

# Proposed numerical tiers for the decided (qualitative) Q-16 criterion "defect small relative to
# iota"; see notes/theory/dommaschk-qa.md.  The rational field of Q-19 has defect/iota = 0.27.
TIER_STRONG = 0.01
TIER_MODERATE = 0.05
NEST_TOL = 1e-6


# ---------------------------------------------------------------- exact field (sympy)
def sympy_field(cand):
    R = sp.symbols('R', positive=True)
    ph, z = sp.symbols('phi z', real=True)
    Phi = ph
    for bk, a in zip(cand['basis'], cand['coefficients']):
        a = sp.Rational(Fraction(a).numerator, Fraction(a).denominator)
        if a == 0:
            continue
        rz = sum(sp.Rational(Fraction(c).numerator, Fraction(c).denominator)*R**p*sp.log(R)**q*z**j
                 for c, p, q, j in bk['terms'])
        Phi += a*(sp.cos if bk['trig'] == 'cos' else sp.sin)(bk['m']*ph)*rz
    BR = sp.diff(Phi, R); BP = sp.diff(Phi, ph)/R; BZ = sp.diff(Phi, z)
    Bm = sp.sqrt(BR**2 + BP**2 + BZ**2)
    dBm = [sp.diff(Bm, R), sp.diff(Bm, ph)/R, sp.diff(Bm, z)]
    FR = R*BR/BP; FZ = R*BZ/BP
    J2 = [sp.diff(FR, R), sp.diff(FR, z), sp.diff(FZ, R), sp.diff(FZ, z)]
    a = (R, ph, z)
    L = lambda e: sp.lambdify(a, e, 'numpy', cse=True)
    return dict(B=L([BR, BP, BZ]), Bm=L(Bm), dBm=L(dBm), F=L([FR, FZ]), J=L(J2), Phi=Phi)


# ---------------------------------------------------------------- axis geometry
def axis_geometry(phis, Rc, zc, nfp):
    """Curvature and torsion of the closed axis curve, from samples over one field period."""
    n = len(phis)
    ph = np.concatenate([phis + k*2*np.pi/nfp for k in range(nfp)])
    R = np.tile(Rc, nfp); z = np.tile(zc, nfp)
    X = np.array([R*np.cos(ph), R*np.sin(ph), z])
    k = np.fft.fftfreq(len(ph), d=1.0/len(ph))
    D = lambda f, o: np.real(np.fft.ifft((1j*k)**o*np.fft.fft(f)))
    d1 = np.array([D(x, 1) for x in X]); d2 = np.array([D(x, 2) for x in X]); d3 = np.array([D(x, 3) for x in X])
    c = np.cross(d1, d2, axis=0)
    sp_ = np.sqrt((d1**2).sum(0))
    kap = np.sqrt((c**2).sum(0))/sp_**3
    tau = (c*d3).sum(0)/np.maximum((c**2).sum(0), 1e-300)
    ds = sp_*(2*np.pi/len(ph))
    return dict(curvature_min=float(kap.min()), curvature_max=float(kap.max()),
                torsion_mean_over_length=float((tau*ds).sum()/ds.sum()),
                torsion_max_abs=float(np.abs(tau).max()),
                integrated_torsion_over_2pi=float((tau*ds).sum()/(2*np.pi)),
                length=float(ds.sum()), z_max=float(np.abs(zc).max()),
                z_rms=float(np.sqrt((zc**2).mean())),
                R_min=float(Rc.min()), R_max=float(Rc.max()), samples=n)


# ---------------------------------------------------------------- eps_eff
def eps_eff_surfaces(fs, nfp, secs, iotas, ok, ntransits, ns, R0, B0, nlines=8, nb=200):
    """Nemov eps_eff on surfaces given by section points secs[j] (nper+1, 2) and signed iota."""
    alpha = 2*np.pi*np.arange(nlines)/nlines + 0.1
    idx = [j for j in range(len(secs)) if ok[j]]
    if not idx:
        return [None]*len(secs)
    Y0 = []
    for j in idx:
        cR, cZ, _ = conjugacy(secs[j], 2*iotas[j]/nfp, 24)
        Y0.append(np.array([K_eval(cR, alpha), K_eval(cZ, alpha),
                            K_eval(cR, alpha, True), K_eval(cZ, alpha, True)]))
    Y0 = np.concatenate(Y0, axis=1)

    def rhs(phi, y):
        fr, fz = fs['F'](y[0], phi, y[1])
        a, b, c, d = fs['J'](y[0], phi, y[1])
        return np.array([fr, fz, a*y[2] + b*y[3], c*y[2] + d*y[3]])
    nsteps = ntransits*nfp*ns
    dphi = 2*np.pi/nfp/ns
    store = np.empty((nsteps + 1, 4, Y0.shape[1])); kk = [0]

    def cb(p, yy):
        store[kk[0]] = yy; kk[0] += 1
    rk4(rhs, Y0, 0.0, nsteps, dphi, every=1, callback=cb)
    phi = dphi*np.arange(nsteps + 1)
    out = [None]*len(secs)
    for ii, j in enumerate(idx):
        parts_in = []
        for l in range(nlines):
            col = ii*nlines + l
            Rr, zz, dR, dz = store[:, 0, col], store[:, 1, col], store[:, 2, col], store[:, 3, col]
            BR, BP, BZ = fs['B'](Rr, phi, zz)
            B = np.array([BR, BP, BZ]); Bm = np.sqrt((B**2).sum(0))
            gB = np.array(fs['dBm'](Rr, phi, zz))
            gpsi_v = np.cross(np.array([dR, 0*dR, dz]), B, axis=0)
            gpsi = np.sqrt((gpsi_v**2).sum(0))
            gkg = (np.cross(B, gB, axis=0)*gpsi_v).sum(0)/Bm**2
            parts_in.append((Rr/BP, Bm/B0, gpsi, gkg))
        bmin = min(p[1].min() for p in parts_in); bmax = max(p[1].max() for p in parts_in)
        bgrid = np.linspace(bmin, bmax, nb + 2)[1:-1]
        ee, _ = eps_eff_from([nemov_sums(dphi, *p, bgrid) for p in parts_in], bgrid, R0)
        half = len(phi)//2
        eh, _ = eps_eff_from([nemov_sums(dphi, *(x[:half] for x in p), bgrid) for p in parts_in], bgrid, R0)
        out[j] = dict(eps_eff=float(ee), eps_eff_half_length=float(eh), b_min=float(bmin), b_max=float(bmax))
    return out


# ---------------------------------------------------------------- main
def run(cand_path, results, cfg, args, starts=None):
    t0 = time.time()
    os.makedirs(results, exist_ok=True)
    cand = json.load(open(cand_path))
    nfp = cand['nfp']
    import basis as bmod
    b = bmod.basis(nfp, cand['nmax'], cand['lmax'])
    assert [bk['name'] for bk in b] == [bk['name'] for bk in cand['basis']], 'basis mismatch'
    x = np.array([float(Fraction(c)) for c in cand['coefficients']])
    tab = fe.Tables(b, nfp)
    W = tab.weights(x[None])
    ns, nper = args.diag_ns, args.diag_nper
    surfaces = list(cfg['surfaces'])
    iota_min = cfg['iota_min']
    S = dict(candidate_sha256=cand['sha256'], nfp=nfp, nmax=cand['nmax'], lmax=cand['lmax'],
             n_coefficients=len(x), coefficients_decimals=cand['decimals'], start=cand['start'],
             parameters=cfg, resolution=dict(ns=ns, nper=nper, eps_transits=args.eps_transits),
             model='vacuum B = grad(phi + sum a_k V_k), exact by construction (harmonic basis); '
                   'net toroidal current 0 (G = 1)', trust='UNTRUSTED numerics (oracle)')

    # 1. sympy field and evaluator cross-check
    fs = sympy_field(cand)
    rng = np.random.default_rng(1)
    Rr = rng.uniform(0.8, 1.2, 64); pp = rng.uniform(0, 2*np.pi, 64); zz = rng.uniform(-0.2, 0.2, 64)
    fast = np.array([tab.eval(W, Rr[[i]][None], pp[i], zz[[i]][None])[:, 0, 0] for i in range(64)]).T
    S['evaluator_vs_sympy_maxdiff'] = float(np.abs(fast - np.array(fs['B'](Rr, pp, zz))).max())

    # 2. axis
    g = (cand['optimiser_metrics']['axis_R'], cand['optimiser_metrics']['axis_z'])
    Ra, za, ok, M = fe.find_axis(tab, W, np.array([g[0]]), np.array([g[1]]), ns)
    phis, Rc, zc = fe.axis_curve(tab, W, Ra, za, ns)
    tr = M[0, 0, 0] + M[0, 1, 1]
    geo = axis_geometry(phis, Rc[0], zc[0], nfp)
    Bax = np.array([np.sqrt((tab.eval(W, Rc[:, [j]], phis[j], zc[:, [j]])**2).sum(0))[0, 0]
                    for j in range(len(phis))])
    geo.update(found=bool(ok[0]), R_phi0=float(Ra[0]), z_phi0=float(za[0]), monodromy_trace=float(tr),
               iota_axis_abs=float(nfp/(2*np.pi)*np.arccos(np.clip(tr/2, -1, 1))),
               B_axis_mean=float(Bax.mean()), B_axis_rel_variation=float((Bax.max() - Bax.min())/Bax.mean()),
               non_planar=bool(geo['z_max'] > 1e-6))
    S['axis'] = geo
    R0ax, B0 = float(Rc.mean()), float(Bax.mean())

    # 3-5. lines: profile lines + the optimisation surfaces
    rmax = 1.6*max(surfaces)
    rl = np.unique(np.round(np.concatenate([np.linspace(rmax/args.diag_lines, rmax, args.diag_lines),
                                            surfaces]), 12))
    sec, Bm, Jac, Phi, lost, sech = fe.trace_surfaces(tab, W, (Ra[0] + rl)[None], np.full((1, len(rl)), za[0]),
                                                      ns, nper, half=True)
    io, err = fe.iota_from_sections(sec, Ra, za, nfp)
    io, err, lost = io[0], err[0], lost[0]
    cm, jm = fe.boozer_coeffs(Bm, Jac, Phi, io[None], nfp, 8, 8)
    c2b.NFP = nfp      # boozer.derivative_sup/reconstruct read the module-level NFP
    lines = []
    for i, r in enumerate(rl):
        A = c2b.amplitudes(fe.amplitudes_dict(cm[0, i], 8))
        qs = {f"{Mh},{Nh}": [float(v) for v in c2b.qs_defect(A, Mh, Nh)] for Mh, Nh in c2b.HELICITIES}
        best = min(qs.items(), key=lambda kv: kv[1][0])
        cdict = fe.amplitudes_dict(cm[0, i], 8)
        supQA, Bmin, Bmax = c2b.derivative_sup(cdict, 'QA', M=1, N=0, ng=128)
        th = np.linspace(0, 2*np.pi, 801)
        try:
            cR, cZ, cres = conjugacy(sec[:, :, 0, i], 2*io[i]/nfp, 24)
            Rcv, Zcv = K_eval(cR, th), K_eval(cZ, th)
            area = 0.5*abs(np.trapezoid(Rcv*np.gradient(Zcv, th) - Zcv*np.gradient(Rcv, th), th))
        except Exception:
            area, cres = float('nan'), float('nan')
        top = sorted(((a, k) for k, a in A.items() if k != (0, 0)), reverse=True)[:6]
        lines.append(dict(r_launch=float(r), r_eff=float(np.sqrt(area/np.pi)), iota=float(io[i]),
                          birkhoff_err=float(err[i]), lost=bool(lost[i]), conj_fit_res=float(cres),
                          mean_jacobian=float(jm[0, i]), B00=float(A[(0, 0)]),
                          qs=qs, best_helicity=best[0], qa_defect=qs['1,0'][0],
                          qa_fraction=qs['1,0'][1], defect_over_iota=float(qs['1,0'][0]/max(abs(io[i]), 1e-12)),
                          lean_qa_delta=float(supQA), kappa=float(2*supQA/(Bmin*max(abs(io[i]), 1e-12))),
                          top_modes=[[list(k), float(a/A[(0, 0)])] for a, k in top],
                          optimised_surface=bool(np.any(np.isclose(r, surfaces)))))
    regular = [(not l['lost']) and l['birkhoff_err'] < NEST_TOL for l in lines]
    reff = [l['r_eff'] for l in lines]
    first_bad = next((i for i, g_ in enumerate(regular) if not g_), len(lines))
    nested_r = rl[first_bad - 1] if first_bad > 0 else 0.0
    S['lines'] = lines
    S['nested'] = dict(all_regular=bool(all(regular)), nested_up_to_r_launch=float(nested_r),
                       r_eff_increasing=bool(np.all(np.diff(reff[:first_bad]) > 0)), tol=NEST_TOL)

    # 6. eps_eff on the optimisation surfaces
    sidx = [i for i, l in enumerate(lines) if l['optimised_surface']]
    ee = eps_eff_surfaces(fs, nfp, [sec[:, :, 0, i] for i in sidx], [io[i] for i in sidx],
                          [regular[i] for i in sidx], args.eps_transits, min(ns, 64), R0ax, B0)
    for i, e in zip(sidx, ee):
        lines[i]['eps_eff'] = e

    # 7. Q-16 verdict on the optimisation surfaces
    sl = [lines[i] for i in sidx]
    worst = max(l['defect_over_iota'] for l in sl)
    feas = dict(vacuum=True, iota_ge_iota_min=bool(all(abs(l['iota']) >= iota_min for l in sl)),
                nested=bool(all(regular[i] for i in sidx)), non_planar_axis=geo['non_planar'],
                qa_best_helicity=bool(all(l['best_helicity'] == '1,0' for l in sl)))
    tier = ('strong' if worst <= TIER_STRONG else 'moderate' if worst <= TIER_MODERATE else 'not small')
    S['q16'] = dict(criterion='vacuum, nested regular surfaces, |iota| >= iota_min, QA defect small '
                              'relative to iota (defect = sqrt(sum_{n != 0} A_mn^2)/B00)',
                    iota_min=iota_min, checks=feas, worst_defect_over_iota=float(worst),
                    worst_qa_defect=float(max(l['qa_defect'] for l in sl)),
                    min_abs_iota=float(min(abs(l['iota']) for l in sl)),
                    eps_eff=[(l['eps_eff'] or {}).get('eps_eff') for l in sl],
                    tiers=dict(strong=TIER_STRONG, moderate=TIER_MODERATE), tier=tier,
                    candidate_for_certification=bool(all(feas.values()) and tier != 'not small'),
                    reference_rational_field_defect_over_iota=0.27)

    # 8. plots and files
    try:
        plots(results, rl, sec[:, :, 0], sech[:, :, 0], Ra[0], za[0], lines, sidx, cm[0], io, nfp, regular)
        S['plots'] = sorted(f for f in os.listdir(results) if f.endswith('.png'))
    except Exception as ex:   # plotting is optional (matplotlib missing)
        S['plots_error'] = repr(ex)
    S['seconds'] = time.time() - t0
    shutil.copy(cand_path, os.path.join(results, 'candidate.json'))
    if starts and os.path.exists(starts):
        shutil.copy(starts, os.path.join(results, 'starts.json'))
    json.dump(S, open(os.path.join(results, 'summary.json'), 'w'), indent=1, default=float)
    q = S['q16']
    print(f"diagnostics: axis z_max {geo['z_max']:.4f} torsion/len {geo['torsion_mean_over_length']:.3f}; "
          f"nested to r = {nested_r:.3f}; surfaces iota {[round(l['iota'], 4) for l in sl]}, "
          f"QA defect {[round(l['qa_defect'], 5) for l in sl]}, defect/|iota| "
          f"{[round(l['defect_over_iota'], 4) for l in sl]}, eps_eff {q['eps_eff']}; tier {q['tier']}; "
          f"evaluator check {S['evaluator_vs_sympy_maxdiff']:.1e}; {S['seconds']:.0f} s", flush=True)
    return S


def plots(results, rl, sec, sech, Ra, za, lines, sidx, cm, io, nfp, regular):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    ink, muted, blue, orange = '#0b0b0b', '#52514e', '#2a78d6', '#eb6834'
    plt.rcParams.update({'font.size': 9, 'axes.edgecolor': muted, 'axes.labelcolor': ink,
                         'xtick.color': muted, 'ytick.color': muted})
    cmap = plt.get_cmap('Blues')
    # Poincare sections
    fig, axs = plt.subplots(1, 2, figsize=(9, 4.2))
    for ax, S_, title in ((axs[0], sec, 'phi = 0'), (axs[1], sech, f'phi = pi/{nfp}')):
        for i in range(len(rl)):
            col = (orange if i in sidx else cmap(0.35 + 0.6*i/max(len(rl) - 1, 1))) if regular[i] else '#c3c2b7'
            ax.plot(S_[:, 0, i], S_[:, 1, i], '.', ms=1.2, color=col, rasterized=True)
        reg = [i for i in range(len(rl)) if regular[i]] or list(range(len(rl)))
        pts = S_[:, :, reg]
        cR, cz = np.median(pts[:, 0]), np.median(pts[:, 1])
        w = 1.6*max(np.ptp(pts[:, 0]), np.ptp(pts[:, 1]))/2 + 1e-3
        ax.set_xlim(cR - w, cR + w); ax.set_ylim(cz - w, cz + w)
        ax.set_aspect('equal'); ax.set_title(title, color=ink); ax.set_xlabel('R'); ax.set_ylabel('z')
    axs[0].plot([Ra], [za], '+', color=ink, ms=8)
    fig.suptitle('Poincare sections (orange: optimised surfaces; grey: irregular or lost lines)', color=ink)
    fig.tight_layout(); fig.savefig(os.path.join(results, 'poincare.png'), dpi=110); plt.close(fig)
    # profiles: one measure per panel
    lr = [l for l, g in zip(lines, regular) if g]
    r = [l['r_eff'] for l in lr]
    panels = [('|iota|', [abs(l['iota']) for l in lr]),
              ('QA defect / B00', [l['qa_defect'] for l in lr]),
              ('QA defect / |iota|', [l['defect_over_iota'] for l in lr])]
    fig, axs = plt.subplots(1, 4, figsize=(12, 3.2))
    for ax, (lab, v) in zip(axs, panels):
        ax.plot(r, v, '-o', color=blue, lw=2, ms=4)
        ax.set_xlabel('r_eff'); ax.set_title(lab, color=ink)
        if 'defect' in lab:
            ax.set_yscale('log')
    re = [(lines[i]['r_eff'], lines[i]['eps_eff']['eps_eff']) for i in sidx if lines[i].get('eps_eff')]
    if re:
        axs[3].plot(*zip(*re), '-o', color=blue, lw=2, ms=4)
    axs[3].set_xlabel('r_eff'); axs[3].set_title('eps_eff (Nemov)', color=ink)
    for ax in axs:
        ax.grid(alpha=0.25)
    fig.tight_layout(); fig.savefig(os.path.join(results, 'profiles.png'), dpi=110); plt.close(fig)
    # |B| in Boozer angles on the outermost optimised surface
    i = sidx[-1]
    c = fe.amplitudes_dict(cm[i], 8)
    th, ph = np.meshgrid(np.linspace(0, 2*np.pi, 181), np.linspace(0, 2*np.pi/nfp, 91), indexing='ij')
    B = c2b.reconstruct(c, th, ph)
    fig, ax = plt.subplots(figsize=(5, 4))
    cs = ax.contourf(ph, th, B, 24, cmap='Blues')
    ax.contour(ph, th, B, 12, colors=muted, linewidths=0.4)
    fig.colorbar(cs, ax=ax, label='|B|')
    ax.set_xlabel('phi_B'); ax.set_ylabel('theta_B')
    ax.set_title(f"|B| in Boozer angles, r = {lines[i]['r_launch']:.3f} (QA: horizontal contours)",
                 color=ink, fontsize=8)
    fig.tight_layout(); fig.savefig(os.path.join(results, 'boozer_B.png'), dpi=110); plt.close(fig)
    for f in os.listdir(results):
        if f.endswith('.png'):
            assert os.path.getsize(os.path.join(results, f)) <= 1_000_000, f


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('candidate'); ap.add_argument('results')
    ap.add_argument('--surfaces', default=None); ap.add_argument('--iota-min', type=float, default=None)
    ap.add_argument('--diag-ns', type=int, default=96); ap.add_argument('--diag-nper', type=int, default=600)
    ap.add_argument('--diag-lines', type=int, default=12); ap.add_argument('--eps-transits', type=int, default=100)
    a = ap.parse_args()
    cand = json.load(open(a.candidate))
    cfgf = os.path.join(os.path.dirname(os.path.abspath(a.candidate)), 'config.json')
    cfg = json.load(open(cfgf)) if os.path.exists(cfgf) else {}
    if a.surfaces:
        cfg['surfaces'] = [float(s) for s in a.surfaces.split(',')]
    if a.iota_min is not None:
        cfg['iota_min'] = a.iota_min
    run(a.candidate, a.results, cfg, a)
