"""UNTRUSTED numerics (Q-19, task d).  Effective ripple eps_eff (Nemov, Kasilov, Kernbichler, Heyn,
Phys. Plasmas 6 (1999) 4622, Eqs. (29)-(31)) on invariant tori of field(1/4), by field-line tracing.

  eps_eff^{3/2} = pi R0^2/(8 sqrt 2) * lim (int ds/B) / (int ds |grad psi|/B)^2
                  * int_{b'min}^{b'max} db' sum_wells Hhat_j^2 / Ihat_j,
  Hhat_j = (1/b') int ds/B sqrt(b' - b) (4/b - 1/b') |grad psi| k_G,
  Ihat_j = int ds/B sqrt(1 - b/b'),     b = B/B0,  B0 = R0 = 1 (|B| = 1 on the exact axis R = 1).

Along a line parametrized by phi: ds/B = dphi/B^phi.  Exact vacuum identities used:
  grad psi = r_alpha x B  (r_alpha = d/d alpha at fixed phi on the torus, propagated by the
  variational equation of the phi-flow; B = grad psi x grad alpha with psi = toroidal flux/2pi);
  |grad psi| k_G = (b x kappa).grad psi = (B x grad|B|).grad psi / B^2  (vacuum: kappa = grad_perp B/B).
The overall sign of k_G is irrelevant (Hhat is squared).  The formula is recalled from the paper and
checked against the classical-stellarator limit derived in the note (validate()).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, json
from scipy.special import ellipk, ellipe
from scipy.integrate import quad


def nemov_sums(dphi, dsB, b, gpsi, gkg, bgrid):
    """Accumulate the pieces of Nemov's formula for one line sampled uniformly in phi.
    Returns (int ds/B, int ds|grad psi|/B, array over bgrid of sum_j Hhat^2/Ihat, n_wells array)."""
    I1 = dsB.sum()*dphi
    I2 = (dsB*gpsi).sum()*dphi
    S = np.zeros(len(bgrid)); nw = np.zeros(len(bgrid), dtype=int)
    n = len(b)
    for ib, bp in enumerate(bgrid):
        mask = b < bp
        if not mask.any():
            continue
        d = np.diff(mask.astype(np.int8))
        starts = np.where(d == 1)[0] + 1
        ends = np.where(d == -1)[0]          # last index inside
        if mask[0]:
            ends = ends[ends >= 0]
            if len(ends) and (len(starts) == 0 or ends[0] < starts[0]):
                ends = ends[1:]
        if len(starts) == 0 or len(ends) == 0:
            continue
        if starts[-1] > ends[-1]:
            starts = starts[:-1]
        m = min(len(starts), len(ends))
        starts, ends = starts[:m], ends[:m]
        ok = (starts > 0) & (ends < n - 1)
        starts, ends = starts[ok], ends[ok]
        if len(starts) == 0:
            continue
        x = np.clip(bp - b, 0, None)
        fH = dsB*np.sqrt(x)*(4/b - 1/bp)*gkg/bp
        fI = dsB*np.sqrt(np.clip(1 - b/bp, 0, None))
        # interior trapezoid via cumulative sums, plus sqrt-shaped end caps
        cH = np.concatenate([[0], np.cumsum(fH)]); cI = np.concatenate([[0], np.cumsum(fI)])
        H = (cH[ends + 1] - cH[starts]) - 0.5*(fH[starts] + fH[ends])
        Ii = (cI[ends + 1] - cI[starts]) - 0.5*(fI[starts] + fI[ends])
        tL = (bp - b[starts])/(b[starts - 1] - b[starts]); tL = np.clip(tL, 0, 1)
        tR = (bp - b[ends])/(b[ends + 1] - b[ends]); tR = np.clip(tR, 0, 1)
        H += (2/3)*(fH[starts]*tL + fH[ends]*tR); Ii += (2/3)*(fI[starts]*tL + fI[ends]*tR)
        H *= dphi; Ii *= dphi
        good = Ii > 0
        S[ib] = (H[good]**2/Ii[good]).sum(); nw[ib] = good.sum()
    return I1, I2, S, nw


def eps_eff_from(parts, bgrid, R0=1.0):
    I1 = sum(p[0] for p in parts); I2 = sum(p[1] for p in parts)
    S = sum(p[2] for p in parts)
    integral = np.trapezoid(S, bgrid)
    e32 = np.pi*R0**2/(8*np.sqrt(2))*I1/I2**2*integral
    return e32**(2/3), e32


def validate():
    """Classical large-aspect stellarator b = 1 - et cos(theta) - eh cos(N phi), theta = th0 + iota phi,
    |grad psi| = r, |grad psi| k_G = r sin(theta)/R0, ds/B = R0 dphi/b.  For et << eh << 1 the formula
    gives eps_eff^{3/2} -> (9/2) A eh^{3/2}, A = int_0^1 [E(k) - (1-k^2) K(k)] k dk (note, section 3)."""
    A = quad(lambda k: (ellipe(k*k) - (1 - k*k)*ellipk(k*k))*k, 0, 1)[0]
    print(f'A = {A:.6f};  predicted eps_eff/eh = ((9/2)A)^(2/3) = {(4.5*A)**(2/3):.4f}')
    N, iota, r, R0 = 10, 0.0123, 0.1, 1.0
    for eh, et in [(0.02, 0.002), (0.01, 0.0005)]:
        L = 2*np.pi*600; nper = 400
        phi = np.linspace(0, L, int(L/(2*np.pi/N)*nper) + 1); dphi = phi[1] - phi[0]
        parts = []
        bmin, bmax = 1 - et - eh, 1 + et + eh
        bgrid = np.linspace(bmin, bmax, 400)[1:-1]
        for th0 in np.linspace(0, 2*np.pi, 4, endpoint=False):
            th = th0 + iota*phi
            b = 1 - et*np.cos(th) - eh*np.cos(N*phi)
            parts.append(nemov_sums(dphi, R0/b, b, r*np.ones_like(b), r*np.sin(th)/R0, bgrid))
        ee, _ = eps_eff_from(parts, bgrid, R0)
        print(f'  eh = {eh}, et = {et}: eps_eff = {ee:.5f},  eps_eff/eh = {ee/eh:.4f}')


if __name__ == '__main__':
    validate()
