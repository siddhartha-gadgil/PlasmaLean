"""UNTRUSTED numerics (N-34, notes/theory/dommaschk-qs-defect.md): the quasi-axisymmetry defect of
the Dommaschk certification target on the KAM torus C, in the torus-intrinsic form proposed for
certification, compared with the Boozer-spectrum defect of scripts/dommaschk_qa/diagnostics.py.

Torus K(theta, phi) = (R, z)(theta, psi = 2 phi) with frequency (iota, 1): L = d_phi + iota d_theta.
Field B = grad Phi, Phi = phi + V.  Vacuum Boozer angles on the torus (N-30 §2):

    phi_B = phi + v,   theta_B = theta + iota v,   v = V o K.

Torus-intrinsic quantities (no V needed except for the spectrum cross-check):

    a  = B . d_theta K = d_theta v,                 (covariant theta component)
    J  = B . L K = 1 + L v = |B|^2 / B^phi = Q/(R^8 D)   (Boozer Jacobian, > 0 iff B_phi > 0)
    g  = d_{phi_B}|_{theta_B} |B| = (1 + iota a) L|B| / J - iota d_theta |B|

(Q = n_R^2 + R^2 D^2 + n_z^2 in the flow-form polynomials D = R^7 B_phi, n = R^8 B_R,z.)
QA on the torus <=> g == 0.  Bounds (N-34 §3):
    defect_spec * B00 = sqrt(sum_{n != 0} A_mn^2) <= (sqrt 2 / NFP) ||g||_{L2(Boozer)} <= sup|g| / sqrt 2.

Usage:  python qs_defect.py [--torus results/20261101T015838Z/torus_C_N96_M80.json] [--n 256]
"""
import argparse
import json
import os
import time
from fractions import Fraction as Fr

import numpy as np

from dfield import ExactField, Evaluator, trig_values

HERE = os.path.dirname(os.path.abspath(__file__))
DEF_TORUS = os.path.join(HERE, 'results', '20261101T015838Z', 'torus_C_N96_M80.json')
NFP = 2


def torus_grid(d, nt, npsi, Ntr=None, Mtr=None):
    """R, z and their theta/psi derivatives on the nt x npsi grid (exact trig-polynomial evaluation
    by FFT with modes folded mod the grid size).  Optional truncation to |k| <= Ntr, |m| <= Mtr."""
    out = {}
    for key, idx, coef, kind in (('R', d['idx_R'], d['a'], 'c'), ('z', d['idx_z'], d['b'], 's')):
        C = np.zeros((nt, npsi), complex)
        Ct = np.zeros((nt, npsi), complex)
        Cp = np.zeros((nt, npsi), complex)
        for (k, m), c in zip(idx, coef):
            if (Ntr is not None and abs(k) > Ntr) or (Mtr is not None and abs(m) > Mtr):
                continue
            c = float(c)
            # cos(x) = Re e^{ix}; sin(x) = Re(-i e^{ix});  we build the complex series with Re taken later
            w = c if kind == 'c' else -1j*c
            C[k % nt, m % npsi] += w
            Ct[k % nt, m % npsi] += 1j*k*w
            Cp[k % nt, m % npsi] += 1j*m*w
        f = lambda X: np.real(np.fft.ifft2(X)*nt*npsi)
        out[key], out[key + '_t'], out[key + '_p'] = f(C), f(Ct), f(Cp)
    th = 2*np.pi*np.arange(nt)/nt
    ps = 2*np.pi*np.arange(npsi)/npsi
    TH, PS = np.meshgrid(th, ps, indexing='ij')
    out['theta'], out['psi'], out['phi'] = TH, PS, PS/2
    return out


def V_eval(ex, R, phi, z):
    """V and its partials (V_R, V_phi, V_z) from the exact term list c R^p z^j trig(m phi)."""
    V = np.zeros_like(R); VR = np.zeros_like(R); Vp = np.zeros_like(R); Vz = np.zeros_like(R)
    for (p, j, kind, m), c in ex.V.items():
        c = float(c)
        tr = np.cos(m*phi) if kind == 'c' else np.sin(m*phi)
        dtr = -m*np.sin(m*phi) if kind == 'c' else m*np.cos(m*phi)
        Rp, zj = R**p, z**j
        V += c*Rp*zj*tr
        VR += c*p*R**(p - 1)*zj*tr
        Vp += c*Rp*zj*dtr
        if j:
            Vz += c*j*Rp*z**(j - 1)*tr
    return V, VR, Vp, Vz


def normB_and_grad(ev, R, phi, z, h=1e-6):
    """|B| and its coordinate partials (d_R, d_phi, d_z at fixed other cylindrical coordinates),
    by central differences of the exact evaluator (error ~ h^2)."""
    def nb(R_, p_, z_):
        BR, BP, BZ = ev.B_cyl(R_, p_, z_)
        return np.sqrt(BR*BR + BP*BP + BZ*BZ)
    f = nb(R, phi, z)
    fR = (nb(R + h, phi, z) - nb(R - h, phi, z))/(2*h)
    fp = (nb(R, phi + h, z) - nb(R, phi - h, z))/(2*h)
    fz = (nb(R, phi, z + h) - nb(R, phi, z - h))/(2*h)
    return f, fR, fp, fz


def fourier_l1(F, rho=0.0):
    """Weighted l1 norm sum |F_km| e^{rho(|k|+|m|)} of a real grid function (FFT coefficients)."""
    nt, npsi = F.shape
    C = np.fft.fft2(F)/(nt*npsi)
    k = np.fft.fftfreq(nt, 1/nt)[:, None]; m = np.fft.fftfreq(npsi, 1/npsi)[None, :]
    return float(np.sum(np.abs(C)*np.exp(rho*(np.abs(k) + np.abs(m)))))


def tail_fraction(F, kcut, mcut):
    nt, npsi = F.shape
    C = np.fft.fft2(F)/(nt*npsi)
    k = np.abs(np.fft.fftfreq(nt, 1/nt))[:, None]; m = np.abs(np.fft.fftfreq(npsi, 1/npsi))[None, :]
    return float(np.sum(np.abs(C)*((k > kcut) | (m > mcut))))


def analyse(d, nt, npsi, Ntr=None, Mtr=None, msp=16, nsp=16, verbose=True):
    ex = ExactField()
    assert d['candidate_sha256'] == ex.sha
    ev = Evaluator(ex)
    iota = float(d['iota'])
    G = torus_grid(d, nt, npsi, Ntr, Mtr)
    R, z, phi = G['R'], G['z'], G['phi']
    Rt, zt = G['R_t'], G['z_t']
    Rf, zf = 2*G['R_p'], 2*G['z_p']                      # d_phi = 2 d_psi
    LR, Lz = Rf + iota*Rt, zf + iota*zt                   # L K (cylindrical coordinate derivatives)
    BR, BP, BZ = ev.B_cyl(R, phi, z)                      # physical components
    # invariance check: L R = R B_R / B_phi, L z = R B_z / B_phi
    inv = max(np.abs(LR - R*BR/BP).max(), np.abs(Lz - R*BZ/BP).max())
    f, fR, fp, fz = normB_and_grad(ev, R, phi, z)
    f_t = fR*Rt + fz*zt
    f_L = fR*LR + fp + fz*Lz
    a = BR*Rt + BZ*zt                                     # B . d_theta K
    J = BR*LR + BP*R + BZ*Lz                              # B . L K  (phi-component: B_phi * R * 1)
    J2 = f*f*R/BP                                         # |B|^2 / B^phi
    g = (1 + iota*a)*f_L/J - iota*f_t
    gY = J/(1 + iota*a)*g                                 # d_phi at fixed theta_B (mixed chart)
    # Boozer angles and spectrum (needs V)
    V, VR, Vp, Vz = V_eval(ex, R, phi, z)
    v_t = VR*Rt + Vz*zt
    v_L = VR*LR + Vp + Vz*Lz
    thB, phB = G['theta'] + iota*V, phi + V
    # c_mn = <f J e^{-i(m thB - n NFP phB)}>_{KAM grid};  direct sums
    E1 = np.exp(-1j*thB); E2 = np.exp(1j*NFP*phB)
    w = f*J/J.mean()
    cm = {}
    Em = np.ones_like(E1)
    for mm in range(0, msp + 1):
        En = np.ones_like(E1)
        for nn in range(0, nsp + 1):
            cm[(mm, nn)] = np.mean(w*Em*En)
            if nn:
                cm[(mm, -nn)] = np.mean(w*Em*np.conj(En))
            En = En*E2
        Em = Em*E1
    B00 = cm[(0, 0)].real
    A = {k: (2*abs(v) if k != (0, 0) else B00) for k, v in cm.items() if not (k[0] == 0 and k[1] < 0)}
    defect8 = np.sqrt(sum(A[k]**2 for k in A if k[1] != 0 and abs(k[1]) <= 8 and k[0] <= 8))/B00
    defect16 = np.sqrt(sum(A[k]**2 for k in A if k[1] != 0))/B00
    # spectral derivative sup (like boozer.derivative_sup, modes m, |n| <= 8) for comparison
    gL2 = np.sqrt(np.mean(g*g*J)/np.mean(J))
    top = sorted(((A[k]/B00, k) for k in A if k != (0, 0)), reverse=True)[:8]
    res = dict(
        iota=iota, grid=[nt, npsi], trunc=[Ntr, Mtr],
        invariance_err=float(inv),
        R_range=[float(R.min()), float(R.max())],
        B_range=[float(f.min()), float(f.max())], B00=float(B00),
        J_range=[float(J.min()), float(J.max())], J_mean=float(J.mean()),
        J_vs_B2overBphi=float(np.abs(J - J2).max()),
        J_vs_1plusLv=float(np.abs(J - 1 - v_L).max()),
        a_vs_vtheta=float(np.abs(a - v_t).max()),
        one_plus_iota_a_range=[float((1 + iota*a).min()), float((1 + iota*a).max())],
        sup_g=float(np.abs(g).max()), L2B_g=float(gL2),
        l1_g=fourier_l1(g), l1_g_rho0045=fourier_l1(g, 0.045),
        tail_g_24x28=tail_fraction(g, 24, 28),
        sup_gY=float(np.abs(gY).max()),
        defect_spec_m8n8=float(defect8), defect_spec_m16n16=float(defect16),
        bound_from_L2=float(np.sqrt(2)/NFP*gL2/B00),
        bound_from_sup=float(np.abs(g).max()/np.sqrt(2)/B00),
        bound_from_l1=float(fourier_l1(g)/np.sqrt(2)/B00),
        kappa_sup=float(2*np.abs(g).max()/(f.min()*abs(iota))),
        kappa_l1=float(2*fourier_l1(g)/(f.min()*abs(iota))),
        top_modes=[[list(k), float(v)] for v, k in top],
    )
    for key in ('defect_spec_m8n8', 'defect_spec_m16n16', 'bound_from_L2', 'bound_from_sup',
                'bound_from_l1'):
        res[key + '_over_iota'] = res[key]/abs(iota)
    if verbose:
        print(json.dumps(res, indent=1))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--torus', default=DEF_TORUS)
    ap.add_argument('--n', type=int, default=256)
    ap.add_argument('--trunc', type=str, default=None, help='N,M truncation of the torus')
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    d = json.load(open(a.torus))
    t0 = time.time()
    Ntr = Mtr = None
    if a.trunc:
        Ntr, Mtr = map(int, a.trunc.split(','))
    res = analyse(d, a.n, a.n, Ntr, Mtr)
    res['seconds'] = time.time() - t0
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
