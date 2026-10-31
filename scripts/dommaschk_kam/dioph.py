"""UNTRUSTED.  Diophantine rotation numbers for the Dommaschk target (NFP 2).

Torus angles: theta (2 pi) and phi with period 2 pi/NFP = pi; the flow-form operator
d_phi + iota d_theta acts on e^{i(k theta + m psi)}, psi = 2 phi, with symbol i(iota k + 2m).
The small divisors are |iota k + 2m| = 2 |omega k + m| with omega = iota/2, the rotation number of
the period map.  Resonances: iota = 2p/q (period-map order q).  In the target window
|iota| in (0.228, 0.245) the low-order ones are 2/9 (0.2222, edge), 3/13 (q 26), 4/17 (q 17),
6/25 (q 25), 1/4 (q 8, edge).

Candidates are noble tails omega = [0; 8, a, 1, 1, 1, ...] (|iota| = 2 omega) with exact closed
forms; iota is negative for this field (diagnostics sign convention), so the torus uses -|iota|.
Diophantine constant (tau = 1, period map, as kam-route.md §4):
    gamma = min_{1 <= k <= K} k * ||k omega||   (and the same over k >= 2, low divisors exact).
"""
from mpmath import mp, mpf, sqrt, floor, nint

mp.dps = 60

# name -> continued-fraction head of omega = |iota|/2 = [0; a1, a2, 1, 1, 1, ...]
CANDIDATES = {
    'A': [8, 2],     # |iota| = (19 + sqrt 5)/89  = 0.238608: r_launch ~ 0.037, between 4/17 and 6/25
    'B': [8, 1],     # |iota| = (15 - sqrt 5)/55  = 0.232071: r_launch ~ 0.056, between 3/13 and 4/17
    'C': [8, 3],     # |iota| = (85 + sqrt 5)/361 = 0.241651: r_launch ~ 0.027, between 6/25 and 1/4
}
CLOSED = {'A': lambda: (19 + sqrt(5))/89, 'B': lambda: (15 - sqrt(5))/55, 'C': lambda: (85 + sqrt(5))/361}


def parse(spec):
    """'A' | 'B' | 'C' | 'cf:8,2,3' (head a1, a2, ... of omega = [0; a1, a2, ..., 1, 1, ...])."""
    if spec in CANDIDATES:
        return spec, CANDIDATES[spec]
    assert spec.startswith('cf:'), spec
    return spec, [int(x) for x in spec[3:].split(',')]


def omega_of(head):
    """[0; head, 1, 1, 1, ...] exactly (golden tail), at the current mp precision."""
    x = (1 + sqrt(5))/2
    for a in reversed(head):
        x = a + 1/x
    return 1/x


def cf_value(head, tail_ones=200):
    x = mpf(1)
    for _ in range(tail_ones):
        x = 1 + 1/x
    for a in reversed(head[1:]):
        x = a + 1/x
    return 1/x if head[0] == 0 else head[0] + 1/x


def iota_abs(spec):
    return 2*omega_of(parse(spec)[1])


def gamma(omega, K=20000):
    best, best2, kb, kb2 = None, None, 0, 0
    for k in range(1, K + 1):
        x = k*omega
        d = abs(x - nint(x))*k
        if best is None or d < best:
            best, kb = d, k
        if k >= 2 and (best2 is None or d < best2):
            best2, kb2 = d, k
    return float(best), kb, float(best2), kb2


def resonances(iota, qmax=40):
    """Nearest iota = 2p/q (q <= qmax, lowest terms in omega = p/q) on both sides."""
    om = iota/2
    lo, hi = None, None
    for q in range(1, qmax + 1):
        for p in range(int(floor(om*q)) - 1, int(floor(om*q)) + 3):
            if p <= 0:
                continue
            from math import gcd
            if gcd(p, q) != 1:
                continue
            v = mpf(p)/q
            if v < om and (lo is None or v > lo[0]):
                lo = (v, p, q)
            if v > om and (hi is None or v < hi[0]):
                hi = (v, p, q)
    return lo, hi


def low_order_margins(iota, qmax=30):
    """|iota - 2p/q| for all q <= qmax, sorted by q: list of (q, p, distance)."""
    om = iota/2
    out = []
    for q in range(1, qmax + 1):
        p = int(nint(om*q))
        out.append((q, p, float(2*abs(om - mpf(p)/q))))
    return out


def report(name):
    io = iota_abs(name)
    head = '[0;' + ','.join(str(x) for x in parse(name)[1]) + ',1,1,...]'
    g, kg, g2, kg2 = gamma(io/2)
    lo, hi = resonances(io, 30)
    near = sorted(low_order_margins(io, 30), key=lambda t: t[2]*t[0]**2)[:4]
    return dict(name=name, omega_cf=head, iota_abs=mp.nstr(io, 30), iota_float=float(io),
                gamma_period_map=g, gamma_k=kg, gamma_k_ge_2=g2, gamma_k2=kg2,
                gamma_flow=2*g, neighbours=[f"2*{lo[1]}/{lo[2]} = {float(2*lo[0]):.6f}",
                                            f"2*{hi[1]}/{hi[2]} = {float(2*hi[0]):.6f}"],
                margin_lo=float(io - 2*lo[0]), margin_hi=float(2*hi[0] - io),
                worst_q2_scaled=[dict(q=q, p=p, dist=d, dist_q2=d*q*q) for q, p, d in near])


if __name__ == '__main__':
    import json
    for nm in CANDIDATES:
        assert abs(iota_abs(nm) - CLOSED[nm]()) < mpf(10)**-50, nm
        assert abs(cf_value([0] + CANDIDATES[nm]) - CLOSED[nm]()/2) < mpf(10)**-50, nm
        print(json.dumps(report(nm), indent=1))
