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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True)
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
