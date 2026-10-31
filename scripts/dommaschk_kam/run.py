"""UNTRUSTED.  Driver: flow-form KAM torus oracle for the Dommaschk certification target.

For each requested rotation number (dioph.py: A, B, C or cf:a1,a2,...):
  1. field self-test against scripts/dommaschk_qa/fieldeval.py; Diophantine data;
  2. magnetic axis, launch radius with the target iota (bisection on the Birkhoff rotation
     number), initial torus from the section conjugacy;
  3. double-precision Galerkin-Newton with continuation in (N, M);
  4. multiprecision refinement (gmpy2 mpfr, dps digits) at the final (N, M)  [DKAM_DPS > 0];
  5. invariance error on an oversampled grid (sup), its Fourier spectrum by a multiprecision DFT,
     weighted l1 strip norms ||E||_rho and the FHL ratio ||E||_rho/(gamma^4 rho^4);
  6. ELP-S twist constant, shear d iota/d Phi;  majorant sizes of the polynomial data.
Writes RESULTS/summary.json and RESULTS/log.txt; intermediate states go to WORK (restartable:
finished stages are loaded, not recomputed).

usage: python run.py --work DIR --results DIR [--tori A,B] [--N 48 --M 40] [--dps 50] ...
"""
import argparse
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np                                   # noqa: E402
import mpmath                                        # noqa: E402

import dfield                                        # noqa: E402
import dioph                                         # noqa: E402
import torus as T                                    # noqa: E402
import twist as TW                                   # noqa: E402

LOG = None


def log(msg):
    print(msg, flush=True)
    if LOG:
        LOG.write(msg + '\n'); LOG.flush()


def jdump(obj, path):
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(obj, f, indent=1)
    os.replace(tmp, path)


def schedule(N, M, N0=8):
    out, n = [], N0
    while n < N:
        out.append((n, max(4, round(n*M/N))))
        n = int(n*1.5) if n >= 16 else n + 4
    out.append((N, M))
    return out


def run_torus(spec, args, ex, ev, tr, axis):
    tag = spec.replace(':', '').replace(',', '_')
    W = args.work
    t_start = time.time()
    mpmath.mp.dps = max(args.dps, 30) + 20
    iota_mp = -dioph.iota_abs(spec)                      # negative for this field
    iota = float(iota_mp)
    drep = dioph.report(spec)
    gam, gam2 = drep['gamma_period_map'], drep['gamma_k_ge_2']
    log(f"\n=== torus {spec}: iota = {mpmath.nstr(iota_mp, 20)}  (omega = {drep['omega_cf']}), "
        f"gamma = {gam:.4f} (k >= 2: {gam2:.4f}), neighbours {drep['neighbours']}")
    out = dict(spec=spec, iota=mpmath.nstr(iota_mp, 40), iota_float=iota, diophantine=drep)

    # ---- launch radius and initial torus
    Ra, za = axis
    pl = os.path.join(W, f'launch_{tag}.json')
    if os.path.exists(pl):
        L = json.load(open(pl))
    else:
        t0 = time.time()
        r = T.find_launch(tr, Ra, za, iota)
        Rg, zg, io_tr, err, tail = T.initial_torus(tr, Ra, za, r, nper=args.nper_init)
        np.savez(os.path.join(W, f'init_{tag}.npz'), Rg=Rg, zg=zg)
        L = dict(r_launch=r, iota_traced=io_tr, birkhoff_err=err, conj_tail=tail,
                 seconds=time.time() - t0)
        jdump(L, pl)
    log(f"  launch r = {L['r_launch']:.6f} on phi = 0 (axis R = {Ra:.6f}); traced iota "
        f"{L['iota_traced']:.10f} (Birkhoff err {L['birkhoff_err']:.1e}); {L['seconds']:.0f}s")
    out['launch'] = L

    # ---- double Newton with continuation
    stages = []
    a = b = None
    N0 = M0 = None
    for (N, M) in schedule(args.N, args.M):
        pd = os.path.join(W, f'double_{tag}_N{N}_M{M}_f{args.fac}.npz')
        if os.path.exists(pd):
            d = np.load(pd)
            a, b = d['a'], d['b']
            st = json.loads(str(d['info']))
        else:
            t0 = time.time()
            if a is None:
                d = np.load(os.path.join(W, f'init_{tag}.npz'))
                a, b = T.from_grid(d['Rg'], d['zg'], N, M)
            else:
                a, b = T.resize(a, b, N0, M0, N, M)
            g = T.Galerkin(ev, N, M, iota, fac=args.fac)
            a, b, hist = T.newton_double(g, a, b, log=lambda s: None)
            gf = T.Galerkin(ev, N, M, iota, Nt=2*g.Nt, Np=2*g.Np)
            RR, RZ, D = gf.residual_grid(a, b)
            st = dict(N=N, M=M, unknowns=len(a) + len(b), grid=[g.Nt, g.Np], newton=hist,
                      true_sup_double=float(max(np.abs(RR).max(), np.abs(RZ).max())),
                      D_min=float(D.min()), seconds=time.time() - t0)
            np.savez(pd, a=a, b=b, info=json.dumps(st))
        log(f"  double N={N:3d} M={M:3d} ({st['unknowns']} unknowns): Newton |F| {st['newton'][-1]:.1e}, "
            f"true sup (2x grid) {st['true_sup_double']:.2e}, D_min {st['D_min']:.3f}, {st['seconds']:.1f}s")
        stages.append(st)
        N0, M0 = N, M
    out['double_stages'] = stages
    N, M = N0, M0
    dc = T.decay(a, b, N, M)
    out['decay'] = dc
    log(f"  decay: theta rate {dc['rate_theta']:.3f}/mode (strip {dc['strip_theta_turns']:.3f} turns), "
        f"psi rate {dc['rate_psi']:.3f}/mode (strip {dc['strip_phi_turns']:.3f} turns of phi/pi); "
        f"tails {dc['tail_theta']:.1e} / {dc['tail_psi']:.1e}")
    g = T.Galerkin(ev, N, M, iota, fac=args.fac)

    # ---- multiprecision refinement and error
    if args.dps > 0:
        num = T.MPNum(args.dps)
        evmp = dfield.Evaluator(ex, mp=num)
        iota_g = num.mpf(mpmath.nstr(iota_mp, args.dps + 15))
        pm = os.path.join(W, f'mp_{tag}_N{N}_M{M}_f{args.fac}_d{args.dps}.json')
        if os.path.exists(pm):
            Mx = json.load(open(pm))
            am = np.array([num.mpf(x) for x in Mx['a']], dtype=object)
            bm = np.array([num.mpf(x) for x in Mx['b']], dtype=object)
        else:
            t0 = time.time()
            gm = T.GalerkinMP(evmp, num, N, M, iota_g, g.Nt, g.Np)
            am, bm, hist = T.refine_mp(g, gm, T.obj(a, num), T.obj(b, num), steps=args.mp_steps,
                                       log=lambda s: log('  ' + s.strip()))
            Mx = dict(a=[str(x) for x in am],
                      b=[str(x) for x in bm], hist=hist, dps=args.dps, seconds=time.time() - t0)
            jdump(Mx, pm)
        out['mp'] = dict(dps=args.dps, galerkin_history=Mx['hist'], seconds=Mx['seconds'])
        log(f"  mp refinement (dps {args.dps}): |F_galerkin| {Mx['hist'][0]:.1e} -> {Mx['hist'][-1]:.1e}, "
            f"{Mx['seconds']:.0f}s")
        pe = os.path.join(W, f'err_{tag}_N{N}_M{M}_f{args.fac}_d{args.dps}_o{args.over}.json')
        if os.path.exists(pe):
            E = json.load(open(pe))
        else:
            t0 = time.time()
            Ntf = int(round(args.over*g.Nt/2))*2; Npf = int(round(args.over*g.Np/2))*2
            gf = T.GalerkinMP(evmp, num, N, M, iota_g, Ntf, Npf)
            RR, RZ, D = gf.residual_grid(am, bm)
            RRf = np.array(RR, float); RZf = np.array(RZ, float); Df = np.array(D, float)
            AR = T.mp_spectrum(num, RR); AZ = T.mp_spectrum(num, RZ)
            E = dict(grid=[Ntf, Npf], sup_RR=float(np.abs(RRf).max()), sup_RZ=float(np.abs(RZf).max()),
                     sup_flow_error=float(max(np.abs(RRf/Df).max(), np.abs(RZf/Df).max())),
                     D_min=float(Df.min()), D_max=float(Df.max()),
                     strip=T.strip_norms_coeffs(AR, AZ, [gam, gam2]),
                     max_by_k=np.maximum(AR.max(1), AZ.max(1)).tolist(),
                     seconds=time.time() - t0)
            a = np.array([float(x) for x in am]); b = np.array([float(x) for x in bm])
            jdump(E, pe)
        prec = 'mp'
    else:
        Ntf, Npf = 2*g.Nt, 2*g.Np
        gf = T.Galerkin(ev, N, M, iota, Nt=Ntf, Np=Npf)
        RR, RZ, D = gf.residual_grid(a, b)
        AR = T.fft_spectrum(RR); AZ = T.fft_spectrum(RZ)
        E = dict(grid=[Ntf, Npf], sup_RR=float(np.abs(RR).max()), sup_RZ=float(np.abs(RZ).max()),
                 sup_flow_error=float(max(np.abs(RR/D).max(), np.abs(RZ/D).max())),
                 D_min=float(D.min()), D_max=float(D.max()),
                 strip=T.strip_norms_coeffs(AR, AZ, [gam, gam2]),
                 max_by_k=np.maximum(AR.max(1), AZ.max(1)).tolist(), seconds=0.0,
                 note='double precision: spectrum noise floor ~1e-16 max|E|, strip norms at rho > 0 '
                      'are dominated by that floor')
        prec = 'double'
    E['precision'] = prec
    out['error'] = E
    log(f"  invariance error ({prec}, {E['grid'][0]}x{E['grid'][1]} grid): sup|RR| {E['sup_RR']:.2e}, "
        f"sup|RZ| {E['sup_RZ']:.2e}; flow error sup|RR/D, RZ/D| {E['sup_flow_error']:.2e}; "
        f"D in [{E['D_min']:.3f}, {E['D_max']:.3f}]")
    log("   rho    ||E_R||_rho  ||E_Z||_rho  edge-frac  ratio(gamma)  ratio(gamma_k>=2)")
    for row in E['strip']:
        rr = row['ratios']
        log(f"   {row['rho']:.3f}  {row['ER']:.2e}     {row['EZ']:.2e}     {row['edge_fraction']:.1e}"
            + (f"    {rr[0]:.2e}      {rr[1]:.2e}" if rr[0] is not None else ''))
    good = [r for r in E['strip'] if r['rho'] > 0 and r['edge_fraction'] < 1e-2]
    if good:
        best = min(good, key=lambda r: r['ratios'][0])
        best2 = min(good, key=lambda r: r['ratios'][1])
        out['fhl'] = dict(best_rho=best['rho'], best_ratio=best['ratios'][0],
                          C1_tolerance=1/best['ratios'][0], best_rho_k2=best2['rho'],
                          best_ratio_k2=best2['ratios'][1], C1_tolerance_k2=1/best2['ratios'][1],
                          criterion='C1 ||E||_rho / (gamma^4 rho^4) < 1, tau = 1, angles in turns; '
                                    'rows with > 1% weighted mass at the DFT edge excluded')
        log(f"  FHL: best rho {best['rho']}: ratio {best['ratios'][0]:.2e} -> C1 tolerance "
            f"{1/best['ratios'][0]:.1e} (gamma {gam:.3f}); with low divisors exact (gamma {gam2:.3f}): "
            f"{1/best2['ratios'][1]:.1e}")

    # ---- twist and shear (double precision, moderate size)
    t0 = time.time()
    Nw, Mw = min(N, args.twist_N), min(M, args.twist_M)
    aw, bw = T.resize(a, b, N, M, Nw, Mw)
    Tt, Trel, inv, ws = TW.elps_twist(ev, aw, bw, Nw, Mw, iota)
    sh = TW.shear(ev, aw, bw, Nw, Mw, iota)
    out['twist'] = dict(T=Tt, T_rel=Trel, invariance_check=inv, omega_s=ws, N=Nw, M=Mw, **sh,
                        seconds=time.time() - t0)
    log(f"  ELP-S twist T = {Tt:+.4e} (T/|omega_s| = {Trel:+.3e}); invariance check {inv:.1e}; "
        f"flux {sh['flux']:.4e} (r_eff {sh['r_eff']:.4f}); d iota/d Phi = {sh['diota_dflux']:.4e}, "
        f"d iota/d r_eff = {sh['diota_dreff']:.4f}")
    out['seconds'] = time.time() - t_start
    return out


def main():
    global LOG
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True)
    ap.add_argument('--results', required=True)
    ap.add_argument('--candidate', default=dfield.TARGET)
    ap.add_argument('--tori', default='A')
    ap.add_argument('--N', type=int, default=24)
    ap.add_argument('--M', type=int, default=20)
    ap.add_argument('--fac', type=int, default=3, help='Galerkin grid = fac*N+8 x fac*M+8')
    ap.add_argument('--dps', type=int, default=0, help='multiprecision digits (0: double only)')
    ap.add_argument('--mp-steps', type=int, default=5)
    ap.add_argument('--over', type=float, default=2.0, help='oversampling of the error grid')
    ap.add_argument('--nper-init', type=int, default=800)
    ap.add_argument('--twist-N', type=int, default=40)
    ap.add_argument('--twist-M', type=int, default=32)
    args = ap.parse_args()
    os.makedirs(args.work, exist_ok=True); os.makedirs(args.results, exist_ok=True)
    LOG = open(os.path.join(args.results, 'log.txt'), 'a')
    t0 = time.time()
    st = dfield.selftest(args.candidate)
    log(f"field self-test vs fieldeval: rhs {st['rhs_maxdiff']:.1e}, B {st['B_maxdiff']:.1e}; "
        f"degrees s^{st['degree_s']} z^{st['degree_z']}; terms {st['terms']}; target sha ok {st['sha_ok']}")
    assert st['rhs_maxdiff'] < 1e-12 and st['B_maxdiff'] < 1e-12
    ex = dfield.ExactField(args.candidate)
    ev = dfield.Evaluator(ex)
    tr = T.Tracer(ev)
    pa = os.path.join(args.work, 'axis.json')
    if os.path.exists(pa):
        ax = json.load(open(pa))
    else:
        Ra, za, Mo = T.find_axis(tr)
        ax = dict(R=Ra, z=za, monodromy_trace=float(np.trace(Mo)),
                  iota_axis=float(np.arccos(np.trace(Mo)/2)/np.pi))
        jdump(ax, pa)
    log(f"axis on phi = 0: R = {ax['R']:.10f}, z = {ax['z']:.1e}, trace {ax['monodromy_trace']:.6f}, "
        f"|iota_axis| = {ax['iota_axis']:.6f}")
    maj = {f"du{du}": dfield.majorant_report(ex, s0=round(ax['R']**2, 4), zmax=0.1, du=du)
           for du in (0.1, 0.25)}
    summary = dict(
        task='dommaschk-kam', trust='UNTRUSTED numerics (oracle); no Lean',
        candidate=os.path.relpath(args.candidate, dfield.REPO), candidate_sha256=ex.sha,
        field=dict(selftest=st, denominator='D = s^3 (1 + d_phi V) = s^4 B^phi, Ps = s^4 d_s Phi, '
                   'Pz = s^3 d_z Phi; D dR/dphi = 2 R Ps, D dz/dphi = s Pz', majorants=maj),
        parameters=vars(args), axis=ax, tori=[])
    for spec in args.tori.split(','):
        summary['tori'].append(run_torus(spec.strip(), args, ex, ev, tr, (ax['R'], ax['z'])))
        summary['seconds'] = time.time() - t0
        jdump(summary, os.path.join(args.results, 'summary.json'))
    log(f"\ndone in {time.time() - t0:.0f}s; summary in {args.results}/summary.json")


if __name__ == '__main__':
    main()
