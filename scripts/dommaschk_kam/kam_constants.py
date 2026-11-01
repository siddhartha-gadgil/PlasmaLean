"""UNTRUSTED.  Design-study estimates for the Lean KAM certificate of a Dommaschk torus (N-33,
notes/theory/dommaschk-kam-certificate.md).

From a double-precision torus of run.py (cached in --work as double_<tag>_N<N>_M<M>_f3.npz) this
script estimates the constants of the generic KAM step `SC` of PlasmaLean/Design/KamFlowStep.lean
(cK, cL, kap and the smallness condition 32 kap e0 / delta0^4 <= 1), transcribed formula by formula,
for the generalisation that the Dommaschk field needs (N-33 Sec. 3):
  * R = R0 + u with a constant centre R0 (the existing interface has R = 1 + u);
  * the area density w = D / R^k with k = 7 (the existing interface has k = 3), so R^3 -> R^k,
    sR^3 -> sR^k and 3 sR -> k sR in the formulas;
  * the frame vector V0 = K - A(phi) about a trigonometric approximation A of the magnetic axis
    (the existing interface has V0 = (R - 1, z), whose winding form changes sign on this torus).
Strip norms are FFT values on the torus (sharp, as a ball chain would give them); C2 is the crude
polynomial majorant of the second derivatives (as Design/KamTorusAComposition), in u = R - R0.

It also reports: the frame comparison (several choices of V0), the Neumann ratios of D, W0, R, the
modes needed by an approximate inverse of D^3 W0^2, and whether any fixed reference circle is (diagnostic only: since audit fix AR-L4 the
contract measures the poloidal angle about a moving reference curve, so the relevant check is
that each cross-section encloses the axis approximation A(phi))
enclosed by all cross-sections (the PoloidalAngle convention of Theory/Contract/StellaratorContract).

usage: python kam_constants.py --work DIR [--N 40 --M 32] [--tag A]

Generalised constants (`SCG` of Design/KamFlowStepG, N-33 item 7), from an exported refined torus:
  python kam_constants.py --torus results/<stamp>/torus_C_N80_M64.json [--summary .../summary.json]
transcribes `SCG.kη1 ... SCG.kap` (p = 7, R0 = 29/32, the moving centre of emit_torus.py, split
Diophantine data dlow = 0.1208, gamma = 0.2671 of Design/DommaschkKamDioC, delta0 = r/7) and the Taylor
constant from the actual Lean polynomials (DkPoly data parsed from Design/DommaschkKamFieldData.lean,
the majorant second derivative `PolyExpr.majD2` at `avec`, direction `mvec`), for several strips r; it
reports kappa, the required e0 = delta0^4/(32 kappa) and the margin against the exported weighted
residual norm at r (summary.json strip table, interpolated in log).
"""
import argparse
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from dfield import ExactField, Evaluator, trig_values, TRIG     # noqa: E402
import torus as T                                                # noqa: E402
import dioph                                                     # noqa: E402


def wnorm(F, r):
    """Weighted l1 norm sum |F_km| e^{r(|k|+|m|)} of a real grid function (theta x psi)."""
    C = np.fft.fft2(F)/F.size
    k = np.abs(np.fft.fftfreq(F.shape[0], 1/F.shape[0]))[:, None]
    m = np.abs(np.fft.fftfreq(F.shape[1], 1/F.shape[1]))[None, :]
    return float((np.abs(C)*np.exp(r*(k + m))).sum())


def mean(F):
    return float(np.real(np.fft.fft2(F)[0, 0]/F.size))


# ------------------------------------------------------------------ generalised SCG constants (item 7)
def lean_polys():
    """dD, dnR, dnZ of Design/DommaschkKamFieldData.lean as [(q, a, b, c, d)] (u, z, c, s exponents)."""
    import re
    from fractions import Fraction
    src = open(os.path.join(HERE, '..', '..', 'PlasmaLean', 'Design', 'DommaschkKamFieldData.lean')).read()
    out = {}
    for name in ('dD', 'dnR', 'dnZ'):
        i = src.index(f'def {name} : SP := ['); j = src.index(']\n', i)
        ts = re.findall(r'⟨mkRat \((-?\d+)\)\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩', src[i:j])
        out[name] = [(float(Fraction(int(n), int(d))), int(a), int(b), int(c), int(e)) for n, d, a, b, c, e in ts]
    assert [len(out[k]) for k in ('dD', 'dnR', 'dnZ')] == [344, 362, 328]
    return out


def majd(terms, au, az, ac, du, dz):
    """Majorant sum |q| (d/du)^du (d/dz)^dz u^a z^b c^c s^d at (au, az, ac, ac) (`PolyExpr.maj`-type)."""
    tot = 0.0
    for q, a, b, c, d in terms:
        if a < du or b < dz:
            continue
        f = math.prod(range(a - du + 1, a + 1))*math.prod(range(b - dz + 1, b + 1))
        tot += abs(q)*f*au**(a - du)*az**(b - dz)*ac**(c + d)
    return tot


def exported_error(summary, r):
    """Weighted residual norm max(||E_R||, ||E_Z||) at the strip r (radians; the summary uses turns,
    weight e^{2 pi rho (|k| + |m|)}), log-interpolated in the strip table; None beyond the valid rows."""
    rows = [x for x in summary['tori'][0]['error']['strip'] if x['edge_fraction'] < 1e-2]
    rho = r/(2*math.pi)
    for lo, hi in zip(rows, rows[1:]):
        if lo['rho'] <= rho <= hi['rho']:
            el, eh = max(lo['ER'], lo['EZ']), max(hi['ER'], hi['EZ'])
            t = (rho - lo['rho'])/(hi['rho'] - lo['rho'])
            return math.exp((1 - t)*math.log(el) + t*math.log(eh))
    return None


def run_scg(args):
    import json
    import emit_torus as ET
    ex = ExactField(); ev = Evaluator(ex)
    d = json.load(open(args.torus))
    N, M = d['N'], d['M']
    a = np.array([float(x) for x in d['a']]); b = np.array([float(x) for x in d['b']])
    iota = float(d['iota'])
    summary = json.load(open(args.summary)) if args.summary else None
    R0 = float(ET.R0); p = 7
    # split Diophantine data: Design/DommaschkKamDioC (dkIotaC_period_split), Design/DommaschkKamDio
    # (dkIotaA_period_split)
    gam, dlow, Klow = {'C': (0.2671, 0.1208, 1), 'A': (0.3645, 0.1193, 1)}[d['tag']]
    E1 = 2.718
    g = T.Galerkin(ev, N, M, iota, Nt=args.grid, Np=args.grid)
    R, z, Rth, Rps, zth, zps = g.fields(a, b)
    LR = 2*Rps + iota*Rth; LZ = 2*zps + iota*zth
    ps = g.ps[None, :]
    al = [float(x) for x in ET.CENTRE_ALPHA]; be = [float(x) for x in ET.CENTRE_BETA]
    AR = sum(x*np.cos(n*ps) for n, x in enumerate(al)) + 0*ps
    AZ = sum(x*np.sin(n*ps) for n, x in enumerate(be)) + 0*ps
    ARp = sum(-2*n*x*np.sin(n*ps) for n, x in enumerate(al)) + 0*ps     # d/dphi, psi = 2 phi
    AZp = sum(2*n*x*np.cos(n*ps) for n, x in enumerate(be)) + 0*ps
    cf = ev.coeff_fields(trig_values(g.ps)[:, None, :])
    s = R*R
    D, Ps, Pz = ev.DPP(s, z, cf=cf)
    h = 1e-30
    Dc, Psc, Pzc = ev.DPP((R + 1j*h)**2, z + 0j, cf=cf)
    D_R, Ps_R, Pz_R = Dc.imag/h, Psc.imag/h, Pzc.imag/h
    Dc, Psc, Pzc = ev.DPP(s + 0j, z + 1j*h, cf=cf)
    D_z, Ps_z, Pz_z = Dc.imag/h, Psc.imag/h, Pzc.imag/h
    nR = 2*R*Ps; nZ = s*Pz                                   # = the Lean n_R = R^8 B_R, n_z = R^8 B_z
    nR_R = 2*Ps + 2*R*Ps_R; nR_z = 2*R*Ps_z; nZ_R = 2*R*Pz + s*Pz_R; nZ_z = s*Pz_z
    XR = nR/D; XZ = nZ/D; w = D/R**p
    XR_R = (nR_R - XR*D_R)/D; XR_z = (nR_z - XR*D_z)/D
    XZ_R = (nZ_R - XZ*D_R)/D; XZ_z = (nZ_z - XZ*D_z)/D
    V1 = R - AR; V2 = z - AZ
    W0 = Rth*V2 - zth*V1
    Y1 = (XR - ARp) - (XR_R*V1 + XR_z*V2); Y2 = (XZ - AZp) - (XZ_R*V1 + XZ_z*V2)
    T0 = (Y1*V2 - Y2*V1)/(w*W0**2)
    pol = lean_polys()
    print(f"torus {d['tag']} {N}x{M} (SCG, p = {p}, R0 = 29/32, moving centre of emit_torus.py): residual sup "
          f"{np.abs(D*LR - nR).max():.1e}/{np.abs(D*LZ - nZ).max():.1e} (double grid); D in [{D.min():.3f}, "
          f"{D.max():.3f}], W0 in [{W0.min():.3e}, {W0.max():.3e}], <T0> = {mean(T0):.4g}")
    print(f"split Diophantine data: dlow = {dlow}, gamma = {gam}, Klow = {Klow}; E1 = {E1}; safety factor "
          f"{args.slack} on the field, inverse and torsion bounds (item 8); torus norms + 1e-6")
    hdr = ("  r      au    az    avR   avZ   aR    aRt   azt   aLR   aLz   bD    bDu   bDz   sD    sR    sW     "
           "tT     tau    cK       cL       C2       kappa    e0 req   e0 exp   margin")
    print(hdr)
    rows = []
    for r in map(float, args.rs.split(',')):
        sl = args.slack
        V = dict(au=wnorm(R - R0, r), az=wnorm(z, r), avR=wnorm(V1, r), avZ=wnorm(V2, r), aR=wnorm(R, r),
                 aRt=wnorm(Rth, r), azt=wnorm(zth, r), aLR=wnorm(LR, r), aLz=wnorm(LZ, r),
                 bD=wnorm(D, r), bDu=wnorm(D_R, r), bDz=wnorm(D_z, r), bnR=wnorm(nR, r), bnRu=wnorm(nR_R, r),
                 bnRz=wnorm(nR_z, r), bnZ=wnorm(nZ, r), bnZu=wnorm(nZ_R, r), bnZz=wnorm(nZ_z, r),
                 sD=wnorm(1/D, r), sR=wnorm(1/R, r), sW=wnorm(1/W0, r), tT=wnorm(T0, r))
        # torus norms are read off the data (plus mu): no slack; the field, inverse and torsion bounds
        # come from the low-resolution chain (item 8): factor `slack`
        exact = ('au', 'az', 'avR', 'avZ', 'aR', 'aRt', 'azt', 'aLR', 'aLz')
        V = {k: v*(1 + 1e-6 if k in exact else sl) for k, v in V.items()}
        V['tau'] = abs(mean(T0))/sl
        ac = math.exp(r)
        d0 = r/7
        e0x = exported_error(summary, r) if summary else None
        e0 = e0x or 1e-25
        th = e0/d0**4
        # SCG derived constants, formula by formula (Design/KamFlowStepG)
        kE = V['sD']
        keta1 = V['sW']*(V['avZ'] + V['avR'])*kE
        keta2 = V['bD']*V['sR']**p*(V['aRt'] + V['azt'])*kE
        kh = V['aR']**p*V['sD']*V['sW']
        kTc = V['aR']**p*V['sD']*V['sW']**2*(V['avZ'] + V['avR'])*kE
        eM = th*d0**4
        tTot = V['tT'] + kTc*eM; taup = V['tau'] - kTc*eM
        gg = 2*E1*gam
        k20 = keta2/gg; kc = (keta1*d0 + tTot*k20)/taup; k2 = k20 + kc
        k1 = (keta1*d0 + tTot*k2)/gg
        mA = max(V['aRt'], V['azt']); mV = max(V['avR'], V['avZ'])
        cK = k1*mA + k2*d0*kh*mV
        kS = (V['bDu'] + V['bDz'])*V['sD']*kE*d0 + p*V['sR']*kE*d0 + V['sW']*(V['avZ'] + V['avR'])*kE/E1
        kRem = kS*k2*kh*mV*d0 + k1*kE/E1
        XRb = V['bnR']*V['sD']; XZb = V['bnZ']*V['sD']
        kA = max((V['bnRu'] + XRb*V['bDu'])*V['sD'] + (V['bnRz'] + XRb*V['bDz'])*V['sD'],
                 (V['bnZu'] + XZb*V['bDu'])*V['sD'] + (V['bnZz'] + XZb*V['bDz'])*V['sD'])
        cL = kA*cK + kE*d0**2 + kRem*th*d0**3
        # Taylor constant: majD2 of resRp = D wR - nR (resZp) at avec + Tq mvec, direction mvec, halved
        Tq = th*d0**2
        au_, az_ = V['au'] + Tq*cK, V['az'] + Tq*cK
        C2 = 0.0
        for nm, aL in (('dnR', V['aLR']), ('dnZ', V['aLz'])):
            m = lambda P, du, dz: majd(pol[P], au_, az_, ac, du, dz)  # noqa: E731
            C2 = max(C2, 0.5*(cK**2*((m('dD', 2, 0) + 2*m('dD', 1, 1) + m('dD', 0, 2))*(aL + Tq*cL)
                                      + m(nm, 2, 0) + 2*m(nm, 1, 1) + m(nm, 0, 2))
                              + 2*cK*cL*(m('dD', 1, 0) + m('dD', 0, 1))))
        kap = V['bD']*kRem*d0 + (V['bDu'] + V['bDz'])*cK*kE*d0**2 + C2
        ereq = d0**4/(32*kap)
        hlow = math.e*gam*d0 <= dlow
        rows.append(dict(r=r, kap=kap, cK=cK, cL=cL, C2=C2, ereq=ereq, e0x=e0x, hlow=hlow, **V))
        f = lambda x: f'{x:.3g}'.ljust(5)  # noqa: E731
        print(f"  {r:.4f} " + ' '.join(f(V[k]) for k in ('au', 'az', 'avR', 'avZ', 'aR', 'aRt', 'azt', 'aLR', 'aLz',
                                                         'bD', 'bDu', 'bDz', 'sD', 'sR'))
              + f" {V['sW']:.4g}  {V['tT']:.4g}  {V['tau']:.3g}  {cK:.2e} {cL:.2e} {C2:.2e} {kap:.2e} "
              f"{ereq:.2e} " + (f"{e0x:.2e} {ereq/e0x:.2e}" if e0x else "  —") + ('' if hlow else '  (hlow fails)'))
    if args.detail:
        for row in rows:
            print(f"  r = {row['r']}: " + ', '.join(f"{k} {row[k]:.4g}" for k in (
                'au', 'az', 'avR', 'avZ', 'aR', 'aRt', 'azt', 'aLR', 'aLz', 'bD', 'bDu', 'bDz', 'bnR', 'bnRu',
                'bnRz', 'bnZ', 'bnZu', 'bnZz', 'sD', 'sR', 'sW', 'tT', 'tau', 'cK', 'cL', 'C2', 'kap', 'ereq')))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--torus', default='', help='exported torus JSON: generalised SCG constants (item 7)')
    ap.add_argument('--summary', default='', help='summary.json of the run (exported residual strip norms)')
    ap.add_argument('--detail', action='store_true', help='print every SCG bound of each row')
    ap.add_argument('--slack', type=float, default=1.0,
                    help='factor on the field, inverse and torsion bounds (1/factor on tau) for certifiable margins')
    ap.add_argument('--work', default='')
    ap.add_argument('--N', type=int, default=40)
    ap.add_argument('--M', type=int, default=32)
    ap.add_argument('--tag', default='A')
    ap.add_argument('--grid', type=int, default=256)
    ap.add_argument('--k', type=int, default=7)
    ap.add_argument('--rs', default='0.03,0.045,0.0628,0.08,0.1')
    ap.add_argument('--gamma', type=float, default=0.0,
                    help='override the Diophantine constant of iota/2 (e.g. the k >= 2 value, with the '
                         'k = 1 divisor treated exactly)')
    ap.add_argument('--russmann', choices=['crude', 'exact'], default='crude',
                    help="crude: C_R = 1/(e gamma delta) as Theory/KAM/Cohomological.cohSol_estimate; "
                         "exact: C_R = sup e^{-delta(|k|+|m|)}/|m + k omega| (not in Lean yet)")
    args = ap.parse_args()
    if args.torus:
        if args.rs == '0.03,0.045,0.0628,0.08,0.1':
            args.rs = '0.02,0.025,0.03,0.035,0.04,0.045,0.05,0.06'
        run_scg(args)
        return
    ex = ExactField(); ev = Evaluator(ex)
    d = np.load(os.path.join(args.work, f'double_{args.tag}_N{args.N}_M{args.M}_f3.npz'))
    a, b = d['a'], d['b']
    iota = -float(dioph.iota_abs(args.tag))
    gam = args.gamma or dioph.report(args.tag)['gamma_period_map']
    g = T.Galerkin(ev, args.N, args.M, iota, Nt=args.grid, Np=args.grid)
    R, z, Rth, Rps, zth, zps = g.fields(a, b)
    LR = 2*Rps + iota*Rth; LZ = 2*zps + iota*zth
    # axis approximation A(psi) (psi = 2 phi), 4 harmonics of the traced axis
    tr = T.Tracer(ev); Ra, za, _ = T.find_axis(tr)
    phs = np.pi*np.arange(65)/64
    AR, AZ = tr.flow(np.array([Ra]), np.array([za]), phs)
    cR = np.fft.rfft(AR[0, :-1])/64; cZ = np.fft.rfft(AZ[0, :-1])/64
    ps = g.ps[None, :]
    Ax = np.real(cR[0]) + 0*ps; Az = 0*ps; Axp = 0*ps; Azp = 0*ps
    for n in range(1, 5):
        e = np.exp(1j*n*ps)
        Ax = Ax + 2*np.real(cR[n]*e); Az = Az + 2*np.real(cZ[n]*e)
        Axp = Axp + 4*np.real(1j*n*cR[n]*e); Azp = Azp + 4*np.real(1j*n*cZ[n]*e)
    cf = ev.coeff_fields(trig_values(g.ps)[:, None, :])
    s = R*R
    D, Ps, Pz = ev.DPP(s, z, cf=cf)
    h = 1e-30
    Dc, Psc, Pzc = ev.DPP((R + 1j*h)**2, z + 0j, cf=cf)
    D_R, Ps_R, Pz_R = Dc.imag/h, Psc.imag/h, Pzc.imag/h
    Dc, Psc, Pzc = ev.DPP(s + 0j, z + 1j*h, cf=cf)
    D_z, Ps_z, Pz_z = Dc.imag/h, Psc.imag/h, Pzc.imag/h
    nR = 2*R*Ps; nZ = s*Pz
    nR_R = 2*Ps + 2*R*Ps_R; nR_z = 2*R*Ps_z; nZ_R = 2*R*Pz + s*Pz_R; nZ_z = s*Pz_z
    k = args.k
    XR = nR/D; XZ = nZ/D; w = D/R**k
    XR_R = (nR_R - XR*D_R)/D; XR_z = (nR_z - XR*D_z)/D
    XZ_R = (nZ_R - XZ*D_R)/D; XZ_z = (nZ_z - XZ*D_z)/D
    print(f"torus {args.tag} N={args.N} M={args.M}: residual sup {np.abs(D*LR - nR).max():.2e}, "
          f"{np.abs(D*LZ - nZ).max():.2e}; D in [{D.min():.3f}, {D.max():.3f}]; "
          f"R in [{R.min():.4f}, {R.max():.4f}]; gamma(omega = iota/2) = {gam:.4f}")

    def Lop(F):
        C = np.fft.fft2(F)
        kk = np.fft.fftfreq(F.shape[0], 1/F.shape[0])[:, None]
        mm = np.fft.fftfreq(F.shape[1], 1/F.shape[1])[None, :]
        return np.real(np.fft.ifft2(C*1j*(2*mm + iota*kk)))

    def torsion(V1, V2, LV1, LV2):
        W0 = Rth*V2 - zth*V1
        Y1 = LV1 - (XR_R*V1 + XR_z*V2); Y2 = LV2 - (XZ_R*V1 + XZ_z*V2)
        return W0, (Y1*V2 - Y2*V1)/(w*W0**2)

    print("\nframe choices (r = 0.0628): V0, winding form W0, ||1/W0||, ||T0||, <T0>")
    Rc = np.mean(R, axis=0)[None, :]; Zc = np.mean(z, axis=0)[None, :]
    R0 = 0.5*(R.min() + R.max())
    for name, V1, V2 in (('radial from the axis approximation', R - Ax, z - Az),
                         ('radial from the theta-centroid', R - Rc, z - Zc),
                         ('curve normal J dK/dtheta', zth, -Rth),
                         (f'radial from the fixed point ({R0:.3f}, 0)', R - R0, z),
                         ('radial from (1, 0) (existing interface)', R - 1.0, z)):
        W0, T0 = torsion(V1, V2, Lop(V1), Lop(V2))
        print(f"  {name}: W0 in [{W0.min():.3g}, {W0.max():.3g}], sW {wnorm(1/W0, 0.0628):.3g}, "
              f"tT {wnorm(T0, 0.0628):.4g}, <T0> {mean(T0):.4g}")

    # fixed reference circles enclosed by every cross-section
    Rs = np.linspace(R.min(), R.max(), 89); Zs = np.linspace(z.min(), z.max(), 81)
    cnt = np.zeros((len(Rs), len(Zs)), int)
    for j in range(R.shape[1]):
        for i0, r0 in enumerate(Rs):
            ang = np.arctan2(z[None, :, j] - Zs[:, None], R[None, :, j] - r0)
            dd = np.diff(np.concatenate([ang, ang[:, :1]], axis=1), axis=1)
            dd = (dd + np.pi) % (2*np.pi) - np.pi
            cnt[i0, :] += (np.abs(np.round(dd.sum(1)/(2*np.pi))) == 1)
    print(f"\n(old convention, diagnostic) PoloidalAngle about a fixed circle: at most {cnt.max()} of {R.shape[1]} cross-sections "
          f"enclose a common fixed point (all would be needed)")

    V1 = R - Ax; V2 = z - Az
    W0, T0 = torsion(V1, V2, XR - Axp, XZ - Azp)
    print("\nNeumann ratios min_c ||F - c||/|c| (r = 0.0628):")
    for name, F in (('D', D), ('W0', W0), ('R', R), ('D^3 W0^2', D**3*W0**2)):
        best = min((wnorm(F - c, 0.0628)/abs(c), c) for c in np.linspace(F.min(), F.max(), 200))
        print(f"  {name}: {best[0]:.3f} (c = {best[1]:.4g}); ||1/F|| = {wnorm(1/F, 0.0628):.4g}")
    F = 1/(D**3*W0**2); C = np.abs(np.fft.fft2(F)/F.size)
    kk = np.abs(np.fft.fftfreq(F.shape[0], 1/F.shape[0]))[:, None]
    mm = np.abs(np.fft.fftfreq(F.shape[1], 1/F.shape[1]))[None, :]
    Wt = C*np.exp(0.0628*(kk + mm))
    print("  approximate inverse of D^3 W0^2, weighted tail outside the box: " + ", ".join(
        f"{K}x{M}: {Wt[(kk > K) | (mm > M)].sum()/Wt.sum():.1e}" for K, M in ((10, 8), (16, 12), (20, 16), (24, 20))))

    # polynomial majorants in u = R - R0, z (trig factor cos/sin(n psi) weighted by e^{n r})
    P = np.polynomial.polynomial

    def poly_uz(name):
        out = {}
        for (t, i, j), c in ex.polys[name].items():
            pol = P.polypow([R0, 1.0], 2*i)
            if name == 'Ps':
                pol = P.polymul(pol, [2*R0, 2.0])
            if name == 'Pz':
                pol = P.polymul(pol, P.polypow([R0, 1.0], 2))
            for ii, cc in enumerate(pol):
                out[(t, ii, j)] = out.get((t, ii, j), 0.0) + float(c)*cc
        return out
    polys = {'D': poly_uz('D'), 'nR': poly_uz('Ps'), 'nZ': poly_uz('Pz')}

    def maj(pol, au, az, ac, du=0, dz=0):
        tot = 0.0
        for (t, i, j), c in pol.items():
            if i < du or j < dz:
                continue
            f = math.prod(range(i - du + 1, i + 1))*math.prod(range(j - dz + 1, j + 1))
            tot += abs(c)*f*au**(i - du)*az**(j - dz)*ac**TRIG[t][1]
        return tot

    print(f"\nSC constants (generalised KamFlowStep formulas), delta0 = r/7, Russmann constant {args.russmann}:")
    print("  r      au     av     sD     sR     sW      tT     tau    cK       cL       C2       "
          "kappa    e0 needed (margin 1)")
    for r in map(float, args.rs.split(',')):
        au = wnorm(R - R0, r); az = wnorm(z, r); av = wnorm(V1, r); bv = wnorm(V2, r)
        aRt = wnorm(Rth, r); azt = wnorm(zth, r); aLR = wnorm(LR, r); aLz = wnorm(LZ, r)
        ac = math.exp(r)
        bD = wnorm(D, r); bDu = wnorm(D_R, r); bDz = wnorm(D_z, r)
        bnR = wnorm(nR, r); bnRu = wnorm(nR_R, r); bnRz = wnorm(nR_z, r)
        bnZ = wnorm(nZ, r); bnZu = wnorm(nZ_R, r); bnZz = wnorm(nZ_z, r)
        sD = wnorm(1/D, r); sR = wnorm(1/R, r); sW = wnorm(1/W0, r)
        tT = wnorm(T0, r); tau = abs(mean(T0)); Rk = wnorm(R**k, r)
        E1 = 2.718; d0 = r/7
        kE = sD; keta1 = sW*(av + bv)*kE; keta2 = bD*sR**k*(aRt + azt)*kE
        kh = Rk*sD*sW; gg = 2*E1*gam
        if args.russmann == 'exact':
            om = iota/2
            CR = max(math.exp(-d0*(kq + abs(mq)))/abs(mq + kq*om)
                     for kq in range(1, 4000) for mq in (round(-kq*om) - 1, round(-kq*om), round(-kq*om) + 1))
            gg = 2/(d0*CR)
        k20 = keta2/gg; kc = (keta1*d0 + tT*k20)/tau; k2 = k20 + kc
        k1 = (keta1*d0 + tT*k2)/gg
        cK = k1*max(aRt, azt) + k2*d0*kh*max(av, bv)
        kS = (bDu + bDz)*sD*kE*d0 + k*sR*kE*d0 + sW*(av + bv)*kE/E1
        kRem = kS*k2*kh*max(av, bv)*d0 + k1*kE/E1
        XRb = bnR*sD; XZb = bnZ*sD
        kA = max((bnRu + XRb*bDu)*sD + (bnRz + XRb*bDz)*sD, (bnZu + XZb*bDu)*sD + (bnZz + XZb*bDz)*sD)
        cL = kA*cK
        C2 = 0.0
        for nm, aL in (('nR', aLR), ('nZ', aLz)):
            m = lambda p, du, dz: maj(polys[p], au, az, ac, du, dz)  # noqa: E731
            C2 = max(C2, 0.5*(cK**2*((m('D', 2, 0) + 2*m('D', 1, 1) + m('D', 0, 2))*aL
                                      + m(nm, 2, 0) + 2*m(nm, 1, 1) + m(nm, 0, 2))
                              + 2*cK*cL*(m('D', 1, 0) + m('D', 0, 1))))
        kap = bD*kRem*d0 + (bDu + bDz)*cK*kE*d0**2 + C2
        print(f"  {r:.4f} {au:.3f}  {av:.3f}  {sD:.2f}  {sR:.3f}  {sW:.4g}  {tT:.4g}  {tau:.2f}  "
              f"{cK:.2e} {cL:.2e} {C2:.2e} {kap:.2e} {d0**4/(32*kap):.2e}")


if __name__ == '__main__':
    main()
