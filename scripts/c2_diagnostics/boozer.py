"""UNTRUSTED numerics (Q-19, tasks b, c).  |B| on invariant tori of field(1/4) in exact Boozer angles,
its Boozer spectrum, and quasisymmetry defects.

Method (see field.py for the exact Boozer facts):
  1. section conjugacy K(theta_s) on phi = 0 from 2000 section points (tori.conjugacy);
  2. N_A field lines from theta_s = alpha_j (uniform) integrated over one field period, N_P samples;
     on line j at angle phi: theta_s = alpha_j + iota*phi;
  3. phi_B = phi + eps*h,  theta_B = theta_s + iota*eps*h,  d(theta_B,phi_B) = (|B|^2/B^phi) d(alpha,phi);
  4. c_mn = (1/(2 pi^2)) sum |B| (|B|^2/B^phi) exp(-i(m theta_B - n NFP phi_B)) dalpha dphi
     (trapezoid; spectrally accurate since the alpha-integrated integrand is pi-periodic in phi).
Checks printed: mean Jacobian (should be 1), Fourier reconstruction error of |B| at the samples.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, json
from field import EPS, NFP, h_f, Bm_f, B_f
from tori import sections, iota_of, conjugacy, K_eval, rk4, IOTA_A, NS
from field import rhs_plain

MMAX, NMAX = 16, 16


def torus_data(rs, nper=2000, nmodes=40, NA=128, NP=128):
    sec = sections(1 + rs, 0*rs, nper)
    io, dig = iota_of(sec)
    starts_R, starts_z, info = [], [], []
    alpha = 2*np.pi*np.arange(NA)/NA
    for i, r in enumerate(rs):
        cR, cZ, res = conjugacy(sec[:, :, i], io[i], nmodes)
        starts_R.append(K_eval(cR, alpha)); starts_z.append(K_eval(cZ, alpha))
        info.append(dict(r=float(r), iota=float(io[i]), digits=float(dig[i]), conj_res=float(res),
                         cR=cR, cZ=cZ))
    y0 = np.array([np.concatenate(starts_R), np.concatenate(starts_z)])
    samples = []
    step = 2*NS // NP if 2*NS >= NP else 1
    ns = NP*step
    rk4(rhs_plain, y0, 0.0, ns - step, np.pi/ns, every=step,
        callback=lambda p, yy: samples.append((p, yy.copy())))
    phis = np.array([p for p, _ in samples])           # NP
    Y = np.array([yy for _, yy in samples])             # NP, 2, nlines
    out = []
    for i, d in enumerate(info):
        sl = slice(i*NA, (i + 1)*NA)
        Rr = Y[:, 0, sl]; zz = Y[:, 1, sl]
        P = np.broadcast_to(phis[:, None], Rr.shape)
        A = np.broadcast_to(alpha[None, :], Rr.shape)
        Bm = Bm_f(Rr, P, zz)
        BR, BP, BZ = B_f(Rr, P, zz)
        Bphi_contra = BP/Rr
        hh = h_f(Rr, P, zz)
        phiB = P + EPS*hh
        thB = A + d['iota']*P + d['iota']*EPS*hh
        Jac = Bm**2/Bphi_contra
        d.update(Bm=Bm, phiB=phiB, thB=thB, Jac=Jac, R=Rr, z=zz)
        out.append(d)
    return out


def spectrum(d, mmax=MMAX, nmax=NMAX):
    w = d['Bm']*d['Jac']
    NPa = w.size
    c = {}
    for m in range(0, mmax + 1):
        em = np.exp(-1j*m*d['thB'])
        for n in range(-nmax, nmax + 1):
            if m == 0 and n < 0:
                continue
            c[(m, n)] = (w*em*np.exp(1j*n*NFP*d['phiB'])).sum()/NPa
    return c


def reconstruct(c, th, ph):
    out = np.real(c[(0, 0)])*np.ones_like(th)
    for (m, n), v in c.items():
        if (m, n) == (0, 0):
            continue
        out += 2*np.real(v*np.exp(1j*(m*th - n*NFP*ph)))
    return out


def amplitudes(c):
    """cos-form amplitudes A_mn = 2|c_mn| ((m,n) != (0,0)), B00 = c_00."""
    return {k: (np.real(v) if k == (0, 0) else 2*abs(v)) for k, v in c.items()}


def qs_defect(A, M, N):
    """Fraction of the non-constant |B| spectrum (and of B00) incompatible with helicity (M, N):
    QS-compatible modes satisfy m*N - n*M = 0 (B = B(M theta_B - N NFP phi_B))."""
    tot = sum(a**2 for k, a in A.items() if k != (0, 0))
    bad = sum(a**2 for k, a in A.items() if k != (0, 0) and k[0]*N - k[1]*M != 0)
    return np.sqrt(bad)/A[(0, 0)], np.sqrt(bad/tot)


def derivative_sup(c, which, M=1, N=0, ng=256):
    """sup over a uniform Boozer grid of |xi B| for xi = N d_theta + M d_phi (Lean convention of
    Theory/Kinetic/Omnigeneity: QA = (N, M) = (0, 1), i.e. xi = d_phi_B)."""
    th, ph = np.meshgrid(2*np.pi*np.arange(ng)/ng, np.pi*np.arange(ng)/ng, indexing='ij')
    out = np.zeros_like(th)
    for (m, n), v in c.items():
        if (m, n) == (0, 0):
            continue
        k = N*m - M*n*NFP      # derivative factor of exp(i(m th - n NFP ph))
        out += 2*np.real(1j*k*v*np.exp(1j*(m*th - n*NFP*ph)))
    B = reconstruct(c, th, ph)
    return np.abs(out).max(), B.min(), B.max()


HELICITIES = [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (1, -2), (2, 1), (2, -1), (1, 3), (1, -3)]

if __name__ == '__main__':
    rA = 0.13073386650096105
    rs = np.array([0.05, 0.10, rA, 0.20, 0.287, 0.36, 0.40])
    data = torus_data(rs)
    summary = []
    for d in data:
        c = spectrum(d)
        A = amplitudes(c)
        rec = reconstruct(c, d['thB'], d['phiB'])
        print(f"\n=== r = {d['r']:.4f}  iota = {d['iota']:.8f} (digits {d['digits']:.1f}) "
              f"conj-fit res {d['conj_res']:.1e}")
        print(f"  mean Jacobian = {d['Jac'].mean():.10f} (expect 1);  |B| range on torus "
              f"[{d['Bm'].min():.4f}, {d['Bm'].max():.4f}];  recon err {np.abs(rec - d['Bm']).max():.1e}")
        # effective minor radius: area of the phi=0 section curve / pi
        th = np.linspace(0, 2*np.pi, 2001)
        Rc = K_eval(d['cR'], th); Zc = K_eval(d['cZ'], th)
        area = 0.5*abs(np.trapezoid(Rc*np.gradient(Zc, th) - Zc*np.gradient(Rc, th), th))
        reff = np.sqrt(area/np.pi)
        top = sorted(((a, k) for k, a in A.items() if k != (0, 0)), reverse=True)[:8]
        print(f"  r_eff = {reff:.4f}   B00 = {A[(0,0)]:.6f}")
        print('  top modes (m, n[NFP units]) A_mn/B00:', ', '.join(f"{k}:{a/A[(0,0)]:.3e}" for a, k in top))
        qs = {f"{M},{N}": qs_defect(A, M, N) for M, N in HELICITIES}
        best = min(qs.items(), key=lambda kv: kv[1][0])
        for k, (f1, f2) in qs.items():
            print(f"  helicity ({k}): defect/B00 = {f1:.4e}   fraction of variation = {f2:.3f}")
        print(f"  best helicity {best[0]}: defect/B00 = {best[1][0]:.4e}, fraction {best[1][1]:.3f}")
        supQA, Bmin, Bmax = derivative_sup(c, 'QA', M=1, N=0)
        supQH, _, _ = derivative_sup(c, 'QH', M=1, N=1)   # xi = d_theta + d_phi: B(theta - NFP phi)?
        print(f"  Lean-form QA defect sup|d_phiB B| = {supQA:.4f};  B_min = {Bmin:.4f};  "
              f"kappa = 2 delta/(B_min iota) = {2*supQA/(Bmin*d['iota']):.2f}")
        summary.append(dict(r=d['r'], r_eff=reff, iota=d['iota'], B00=A[(0, 0)],
                            Bmin=float(d['Bm'].min()), Bmax=float(d['Bm'].max()),
                            top=[(list(k), a/A[(0, 0)]) for a, k in top],
                            qs={k: list(v) for k, v in qs.items()}, best=best[0],
                            supQA=supQA, kappaQA=2*supQA/(Bmin*d['iota'])))
    json.dump(summary, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'boozer_summary.json'), 'w'),
              indent=1, default=float)
