#!/usr/bin/env python3
"""Untrusted oracle for the re-anchored bounce scheme (Phase 12, trapped alphas).

Integrates the vacuum Boozer guiding-centre equations (Theory/Kinetic/BoozerGuidingCentre) for a
3.5 MeV alpha in the reactor near-axis QA model (`reactorQA`, b1 = -4.3e-4) and, at every upper
turning point tau_k, re-anchors a fresh exact-QA (b1 = 0) reference orbit at the same state.  It
reports the per-bounce quantities that enter `Kinetic.BounceShear.reanchored_drift_le`:

* R_k   : |actual kick - reference kick| (in psi units, T m^2),
* e_k   : |2(phi_{k+1} - phi_k) - 2 Delta_k| (phase-step error),
* gamma : |d_{k+1} - d_k| for d = (C, S)/sin Delta (shear of the reference data),
* M     : max |d_k|,
* and a sampled Lipschitz constant K of the reduced exact-QA field on redBox (sup norm).

Nothing here is trusted; numbers only guide the note `notes/theory/trapped-alpha-status.md`.
Usage: python3 -I reanchor_sim.py [psi0] [Bt] [nbounce]
"""
import math
import sys

m = 6.6447e-27
q = 2 * 1.6022e-19
E = 3.5e6 * 1.6022e-19
B0, eta, b0, B2c, iota, G = 5.7, -0.07, -0.0137, 0.0165, 0.422, 58.1


def fields(psi, th, ph, b1):
    r = math.sqrt(2 * psi / B0)
    B = B0 + B0 * eta * r * math.cos(th) + r * r * (b0 + b1 * math.cos(2 * ph) + B2c * math.cos(2 * th))
    Bpsi = eta * math.cos(th) / r + (2 / B0) * (b0 + b1 * math.cos(2 * ph) + B2c * math.cos(2 * th))
    Bth = -B0 * eta * r * math.sin(th) - 2 * B2c * r * r * math.sin(2 * th)
    Bph = -2 * b1 * r * r * math.sin(2 * ph)
    return B, Bpsi, Bth, Bph


def rhs(y, mu, b1):
    psi, th, ph, rho = y
    B, Bpsi, Bth, Bph = fields(psi, th, ph, b1)
    a = m * mu + q * q * rho * rho * B
    return [
        -a * Bth / (m * q),
        (mu / q + q * rho * rho * B / m) * Bpsi + q * rho * B * B * iota / (G * m),
        q * rho * B * B / (G * m),
        -a * (Bph + iota * Bth) / (G * m * q),
    ]


def kick_rate(y, mu, b1):
    """(q^2 rho^2 B/m + mu) * B_phi, the integrand of the psi_p step."""
    psi, th, ph, rho = y
    B, _, _, Bph = fields(psi, th, ph, b1)
    return (q * q * rho * rho * B / m + mu) * Bph


def rk4(y, mu, b1, h):
    k1 = rhs(y, mu, b1)
    k2 = rhs([y[i] + h / 2 * k1[i] for i in range(4)], mu, b1)
    k3 = rhs([y[i] + h / 2 * k2[i] for i in range(4)], mu, b1)
    k4 = rhs([y[i] + h * k3[i] for i in range(4)], mu, b1)
    return [y[i] + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]) for i in range(4)]


def one_bounce(y0, mu, b1, h, ref_b1=-4.3e-4):
    """Integrate from an upper tip to the next upper tip (rho: + -> - crossing after a - -> +).
    Returns (end state, period, int kick_rate dt with b1, int g cos/sin of 2(phi-phi0))."""
    y = list(y0)
    t = 0.0
    seen_pos = False
    kick = 0.0
    Ic = Is = 0.0
    phi0 = y0[2]
    while True:
        # trapezoid accumulation of kick and reference harmonic integrals
        def acc(yy):
            B, _, _, _ = fields(yy[0], yy[1], yy[2], 0.0)
            g = -(q * q * yy[3] ** 2 * B / m + mu) * (2 * yy[0] / B0) * (2 * ref_b1)
            return kick_rate(yy, mu, b1), g * math.cos(2 * (yy[2] - phi0)), g * math.sin(2 * (yy[2] - phi0))
        a0 = acc(y)
        yn = rk4(y, mu, b1, h)
        a1 = acc(yn)
        kick += h / 2 * (a0[0] + a1[0])
        Ic += h / 2 * (a0[1] + a1[1])
        Is += h / 2 * (a0[2] + a1[2])
        if yn[3] > 0:
            seen_pos = True
        if seen_pos and y[3] > 0 >= yn[3]:
            # linear interpolation of the crossing
            s = y[3] / (y[3] - yn[3])
            ye = [y[i] + s * (yn[i] - y[i]) for i in range(4)]
            corr = (1 - s) * h
            kick -= corr * a1[0]
            Ic -= corr * a1[1]
            Is -= corr * a1[2]
            return ye, t + s * h, kick, Ic, Is
        y = yn
        t += h


def lipschitz_sample(mu, n=12):
    psiLo = 5.7 * 0.81 / 2
    psiA = 5.7 * 1.7 ** 2 / 2
    best = 0.0
    eps = [1e-6, 1e-7, 1e-9]
    for i in range(n + 1):
        for j in range(n + 1):
            for k in range(n + 1):
                y = [psiLo + (psiA - psiLo) * i / n, -2 + 4 * j / n, 0.0, -1 + 2 * k / n]
                f0 = rhs(y, mu, 0.0)
                rows = [0.0, 0.0, 0.0]
                for c, idx in enumerate([0, 1, 3]):
                    yp = list(y)
                    yp[idx] += eps[min(c, 2)] if idx != 3 else 1e-9
                    d = yp[idx] - y[idx]
                    f1 = rhs(yp, mu, 0.0)
                    for r_, ridx in enumerate([0, 1, 3]):
                        rows[r_] += abs((f1[ridx] - f0[ridx]) / d)
                best = max(best, max(rows))
    return best


def main():
    psi0 = float(sys.argv[1]) if len(sys.argv) > 1 else 5.27
    Bt = float(sys.argv[2]) if len(sys.argv) > 2 else 5.45
    nb = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    mu = E / Bt
    # theta0 with B(psi0, theta0, 0; b1) = Bt (bisection on (0, pi/2))
    lo, hi = 1e-6, math.pi / 2
    for _ in range(200):
        mid = (lo + hi) / 2
        if fields(psi0, mid, 0.0, -4.3e-4)[0] < Bt:
            lo = mid
        else:
            hi = mid
    y = [psi0, lo, 0.0, 0.0]
    h = 2e-8
    qi = q * iota
    Rs, es, ds, Ps, psis, Ds = [], [], [], [], [], []
    for k in range(nb):
        ye, P, kick, _, _ = one_bounce(y, mu, -4.3e-4, h)
        # fresh exact-QA reference anchored at the same tip state
        yr, Pr, _, Ic, Is = one_bounce(y, mu, 0.0, h)
        Delta = yr[2] - y[2]
        refkick = math.sin(2 * y[2]) * Ic + math.cos(2 * y[2]) * Is
        R = abs(kick - refkick) / qi
        e = abs(2 * (ye[2] - y[2]) - 2 * Delta)
        d = (Ic / qi / math.sin(Delta), Is / qi / math.sin(Delta))
        Rs.append(R)
        es.append(e)
        ds.append(d)
        Ps.append(Pr)
        Ds.append(Delta)
        psis.append(y[0])
        y = ye
    gam = max(max(abs(ds[k + 1][0] - ds[k][0]), abs(ds[k + 1][1] - ds[k][1])) for k in range(nb - 1))
    M = max(max(abs(a), abs(b)) for a, b in ds)
    sig = max(abs(Ds[k + 1] - Ds[k]) for k in range(nb - 1))
    print(f"psi0={psi0} Bt={Bt} bounces={nb}")
    print(f"P_ref in [{min(Ps):.3e}, {max(Ps):.3e}] s")
    print(f"psi at tips in [{min(psis):.4f}, {max(psis):.4f}]")
    print(f"Delta in [{min(Ds):.4f}, {max(Ds):.4f}], sigma = {sig:.3e}")
    print(f"budget per bounce R + gamma + M(e+sigma) = {max(Rs) + gam + M * (max(es) + sig):.3e}")
    print(f"max R_k = {max(Rs):.3e} T m^2 ; max e_k = {max(es):.3e} ; gamma = {gam:.3e} ; M = {M:.3e}")
    print(f"sampled Lipschitz K (exact-QA reduced field, sup norm) = {lipschitz_sample(mu, 8):.3e} 1/s")


if __name__ == "__main__":
    main()
