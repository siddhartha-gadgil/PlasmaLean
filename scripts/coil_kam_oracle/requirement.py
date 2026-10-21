"""UNTRUSTED.  The KAM smallness requirement for the coil torus, scaled from the constants of the
torus-A instance (`PlasmaLean/Design/KamTorusAExact.lean`, structure `SC` of `KamFlowStep.lean`).

The formulas of `SC` (eM, kE, keta1, ..., kap) are transcribed literally.  The requirement is the
smallness condition 32 kap e0 / delta0^4 <= 1, i.e. e0 <= delta0^4 / (32 kap).

Scalings for the coil field (all assumptions are stated; nothing here is certified):
* variables (theta, phi) with full phi-period (the coil field has no exact symmetry), so
  L = d_phi + iota d_theta = L_omega with omega = (iota, 1): the factor 2 of `SC.g = 2 e gamma` is
  lost and the Diophantine constant of iota (tau = 1) is gamma/2 (from that of iota/2); in the
  formula this is gamma_eff = gamma/4;
* the strip is isotropic in (theta, phi) (the FA weight e^{r(|k|+|m|)}); r_phi = 0.063 is the
  torus-A strip 0.1257 measured in phi;
* the torus bounds (au, az, aRt, ...), the inverse bounds and the twist are those of torus A
  (the coil torus is 5e-5 from torus A);
* D = B_phi ~ 1/R, n = R (B_R, B_z): bD = 1.3, first derivatives 1.6, n bounds 0.3;
* the Taylor constant C2 comes from `bd_comp_taylor` / `bd_comp_sub` (AnalyticComposition):
  for X with AnaFieldAt constant C = M geoZ(q)^2 and radius d, at s = d/2,
  |second-order remainder| <= 16 C/d^2 (|k1| + |k2|)^2 and |first-order Lipschitz| <= 8 C/d.
  With |k_i| <= cK e/delta^2 and |L k| <= cL e/delta^2:
  C2 = C_D (16 (2 cK)^2 aL/d^2 + 8 (2 cK) cL/d) + C_n 16 (2 cK)^2/d^2.
"""
import math

E1 = 2718 / 1000


def sc_kap(c):
    """Literal transcription of SC.kap and its dependencies (KamFlowStep.lean)."""
    eM = c['θ'] * c['δ0'] ** 4
    kE = c['sD']
    kη1 = c['sW'] * (c['az'] + c['au']) * kE
    kη2 = c['bD'] * c['sR'] ** 3 * (c['aRt'] + c['azt']) * kE
    kh = (1 + c['au']) ** 3 * c['sD'] * c['sW']
    kTc = (1 + c['au']) ** 3 * c['sD'] * c['sW'] ** 2 * (c['az'] + c['au']) * kE
    tTot = c['tT'] + kTc * eM
    τp = c['τ'] - kTc * eM
    g = 2 * E1 * c['γ']
    k20 = kη2 / g
    kc = (kη1 * c['δ0'] + tTot * k20) / τp
    k2 = k20 + kc
    k1 = (kη1 * c['δ0'] + tTot * k2) / g
    mA = max(c['aRt'], c['azt'])
    mV = max(c['au'], c['az'])
    cK = k1 * mA + k2 * c['δ0'] * kh * mV
    kS = (c['bDu'] + c['bDz']) * c['sD'] * kE * c['δ0'] + 3 * c['sR'] * kE * c['δ0'] + \
        c['sW'] * (c['az'] + c['au']) * kE / E1
    kRem = kS * k2 * kh * mV * c['δ0'] + k1 * kE / E1
    XRb = c['bnR'] * c['sD']
    XZb = c['bnZ'] * c['sD']
    kA = max((c['bnRu'] + XRb * c['bDu']) * c['sD'] + (c['bnRz'] + XRb * c['bDz']) * c['sD'],
             (c['bnZu'] + XZb * c['bDu']) * c['sD'] + (c['bnZz'] + XZb * c['bDz']) * c['sD'])
    cL = kA * cK + kE * c['δ0'] ** 2 + kRem * c['θ'] * c['δ0'] ** 3
    kap_wo_C2 = c['bD'] * kRem * c['δ0'] + (c['bDu'] + c['bDz']) * cK * kE * c['δ0'] ** 2
    return cK, cL, kap_wo_C2


μ = 1e-10
rA = 0.1257
TORUS_A = dict(ρ=rA, δ0=rA / 7, γ=0.0687, θ=5.83e-22 / (rA / 7) ** 4,
               au=0.228 + μ, az=0.224 + μ, aRt=0.236 + μ, azt=0.231 + μ,
               aLR=0.1375 * 0.236 + 0.130 + μ, aLz=0.1375 * 0.231 + 0.126 + μ,
               bD=1.64, bDu=3.09, bDz=0.61, bnR=0.42, bnRu=1.71, bnRz=1.08, bnZ=0.45, bnZu=1.59,
               bnZz=1.43, sD=1 / (1 - 0.4831), sR=1 / (1 - 0.228 - μ),
               sW=1 / (0.01813 - 0.004079), tT=19.84, τ=0.22, C2=6e9)


def geoZ(q):
    return (1 + q) / (1 - q)


def coil_case(r, gap, M_B, d, label):
    c = dict(TORUS_A)
    c.update(ρ=r, δ0=r / 7, γ=0.0687 / 4, bD=1.3, bDu=1.6, bDz=0.6, bnR=0.3, bnRu=1.6, bnRz=1.0,
             bnZ=0.3, bnZu=1.6, bnZz=1.4)
    c['θ'] = 1e-30 / c['δ0'] ** 4      # eM negligible (self-consistent at the end)
    cK, cL, k0 = sc_kap(c)
    q = math.exp(-gap)
    CD = 2 * math.cosh(r) * M_B * geoZ(q) ** 2
    Cn = 1.3 * 2 * M_B * geoZ(q) ** 2
    aL = max(c['aLR'], c['aLz'])
    C2 = CD * (16 * (2 * cK) ** 2 * aL / d ** 2 + 8 * (2 * cK) * cL / d) + Cn * 16 * (2 * cK) ** 2 / d ** 2
    kap = k0 + C2
    e_req = c['δ0'] ** 4 / (32 * kap)
    print(f"{label:58s} cK={cK:9.3e} cL={cL:9.3e} C2={C2:9.3e} kap={kap:9.3e} e0_req={e_req:9.3e}")
    return e_req


if __name__ == '__main__':
    cK, cL, k0 = sc_kap(TORUS_A)
    kap = k0 + TORUS_A['C2']
    print(f"torus A (check against KamTorusAExact): cK={cK:.4e} (<=10800) cL={cL:.4e} (<=130500) "
          f"kap={kap:.4e}  32 kap e0/delta0^4 = {32 * kap * 5.83e-22 / TORUS_A['δ0'] ** 4:.3e}  "
          f"e0_req = {TORUS_A['δ0'] ** 4 / (32 * kap):.3e}")
    print("coil field, phi-convention (gamma_eff = gamma/4), isotropic strip r, PW gap rho - r:")
    coil_case(0.02, 0.03, 3.5e4, 0.03, "crude: r=0.02, gap=0.03, M=3.5e4 (Mcoil), d=0.03")
    coil_case(0.02, 0.03, 10, 0.03, "sharp M=10: r=0.02, gap=0.03, d=0.03")
    coil_case(0.063, 0.05, 3.5e4, 0.05, "r=0.063 (torus-A strip in phi), gap=0.05, M=3.5e4, d=0.05")
    coil_case(0.063, 0.05, 10, 0.05, "r=0.063, gap=0.05, M=10, d=0.05")
    coil_case(0.063, 0.19, 10, 0.1, "adapted nbhd: r=0.063, gap=0.19, M=10, d=0.1")
