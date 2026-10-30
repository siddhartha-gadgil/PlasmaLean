# Boozer spectrum of |B| along one field line (untrusted numerics).
# Along a field line x' = B: Boozer toroidal angle phi_B = c * int |B|^2 dt (B.grad phi_B = B^2/(G+iota I)),
# theta_B = iota*phi_B + theta0. So |B|(t) = sum_mn B_mn cos((m iota - n) phi_B + m theta0) and a
# least-squares fit in the frequencies (m iota - n) gives |B_mn| for one irrational surface.
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sympy as sp, itertools
from scipy.integrate import solve_ivp
from qs_family import family2, x, y, z

def spectrum(eps, S, lam, k, T=400.0, n=60000, Mmax=4, Nmax=24, nfp=2):
    B, psi = family2(eps, S, lam)
    Bm = sp.sqrt((B.T*B)[0])
    f = sp.lambdify((x, y, z), [B[0], B[1], B[2], Bm], 'numpy')
    d = np.arcsin(k); xs = np.sqrt((-eps + np.sqrt(eps**2 + 4*(S+d)**2))/2)
    def rhs(t, p):
        b = f(*p[:3]); return [b[0], b[1], b[2], b[3]**2]
    sol = solve_ivp(rhs, (0, T), [xs, 0, 0, 0], rtol=1e-11, atol=1e-13, dense_output=True)
    ts = np.linspace(0, T, n); P = sol.sol(ts)
    Bv = np.array(f(P[0], P[1], P[2])[3], dtype=float)
    phic = np.unwrap(np.arctan2(P[1], P[0]))
    Bz = np.array(f(P[0], P[1], P[2])[2], dtype=float)
    th = np.unwrap(np.arctan2(-np.sin(lam*P[2]), lam*Bz))
    c = np.polyfit(P[3], phic, 1)[0]; phiB = c*P[3]
    iota = abs(np.polyfit(phiB, th, 1)[0])
    cols, labels = [np.ones(n)], [(0, 0)]
    for m in range(Mmax+1):
        for nn in range(-Nmax, Nmax+1, nfp):
            if m == 0 and nn <= 0: continue
            w = (m*iota - nn)*phiB
            cols += [np.cos(w), np.sin(w)]; labels += [(m, nn)]
    A = np.array(cols).T
    coef, *_ = np.linalg.lstsq(A, Bv, rcond=None)
    fitres = np.linalg.norm(A@coef - Bv)/np.linalg.norm(Bv - Bv.mean())
    amps = {labels[0]: coef[0]}
    for j, lab in enumerate(labels[1:]):
        amps[lab] = np.hypot(coef[1+2*j], coef[2+2*j])
    return iota, amps, fitres

if __name__ == '__main__':
    for eps in [1/16, 1/8, 1/4]:
        for k in [0.4, 0.7]:
            iota, amps, fr = spectrum(eps, 4.0, 15.0, k)
            B00 = amps[(0, 0)]
            items = sorted(((v, kk) for kk, v in amps.items() if kk != (0, 0)), reverse=True)
            qa = np.sqrt(sum(v**2 for kk, v in amps.items() if kk != (0, 0) and kk[1] == 0))
            nonqa = np.sqrt(sum(v**2 for kk, v in amps.items() if kk[1] != 0))
            print(f"eps={eps:.4f} k={k} iota={iota:.4f} fit-res={fr:.1e} B00={B00:.5f} "
                  f"QA part={qa/B00:.2e} nonQA part={nonqa/B00:.2e} ratio={nonqa/qa:.3f}")
            print("   top modes (m,n):", [(kk, f"{v/B00:.2e}") for v, kk in items[:6]])
