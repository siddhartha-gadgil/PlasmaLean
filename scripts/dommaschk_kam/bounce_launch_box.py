"""External integer enclosure on the deep bounce launch strip (geometric theta=0).

Run python3 scripts/dommaschk_kam/bounce_launch_box.py. The whole strip interpolates
the two seed profiles, C + u(A-C), 11/25 <= u <= 27/50. The boxes include the decimal
screen profiles, the packed dyadic profiles and the exact Q-16 profiles near those
seeds. The field is the actual rational DommaschkQA2R candidate. The signed flux
density uses B dot (X_u cross X_phi) in physical cylindrical components.

The four quarter-circle charts use exp(i*2*phi)=i^q (1+it)^2/(1+t^2), 0<=t<=1.
The angular distance from the midpoint of a t-cell is at most its width, since
the angle derivative 2/(1+t^2) is at most two. Fourier derivative sup bounds
therefore enclose every phase in every cell. All inclusion decisions use outward
integer or rational operations. The default cover checks |B| <= 1.048, B_phi >= 1.03
and oriented flux density <= -0.000017, each in candidate units.

DommaschkKam.{Dp_ident,nRp_ident,nZp_ident} and DommaschkKamC.norm_field_sq
identify the polynomial components and Euclidean norm. Forms.interpolated_launch_flux
identifies the oriented density with the magnetic two-form on the launch cut. The profile
error input is the strip-distance conclusion of DommaschkKamEmbedded.dommaschk_Q16_embedded.
This external calculation concerns the launch slice only.
"""
import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from fractions import Fraction as F
from math import ceil, floor, isqrt
from pathlib import Path

from emit_flowfield import TARGET, build, crosscheck_cart, lean_sp, load, subst_R, to_list
from interface_arc import MU, RHO, collapse_modes

HERE = Path(__file__).resolve().parent
DESIGN = HERE.parents[1] / 'PlasmaLean/Design'
R0 = F(29, 32)
SEEDS = {
    'C': ('20261101T015838Z', 'ef91ae1b34333fd4b43ffbfb1d73ceda500ac3fecae1eb4cde320319497276c2',
          '691a12a2723954263e567ba7cdf198e6f0c10e6bdccac2a54e73ca8c7874bde4'),
    'A': ('20261101T111958Z', 'b2524e61c865759436434df012a2727febd5bc73347c0412c493efc73404c5ac',
          'd1c57b90b04d513eb5dc53c00004be612e4b09059e0a4f27394bf47ca917abf4'),
}
S = 1 << 52


@dataclass(frozen=True, slots=True)
class Box:
    """Fixed-point interval [lo/S,hi/S]. Products and quotients round out."""
    lo: int
    hi: int

    @staticmethod
    def rational(x):
        return Box(floor(x*S), ceil(x*S))

    def __add__(self, other):
        return Box(self.lo+other.lo, self.hi+other.hi)

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = [self.lo*other.lo, self.lo*other.hi, self.hi*other.lo, self.hi*other.hi]
        return Box(min(products)//S, -((-max(products))//S))

    def __truediv__(self, other):
        if other.lo <= 0:
            raise ArithmeticError('expected a strictly positive denominator')
        inverse = Box(S*S//other.hi, -((-S*S)//other.lo))
        return self*inverse

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))


def verified_read(path, digest):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError(f'file digest changed: {path}')
    return raw


def profile_coefficients(tag):
    """Real cosine/sine coefficients on theta=0; cross-check packed and decimal profiles."""
    stamp, jsha, lsha = SEEDS[tag]
    seed = json.loads(verified_read(HERE / 'results' / stamp / f'torus_{tag}_N96_M80.json', jsha))
    text = verified_read(DESIGN / f'DommaschkKam{tag}Data.lean', lsha).decode()
    n, m, bits, scale = [int(re.search(r'def '+name+r' : ℕ := (\d+)', text)[1])
                         for name in ['Nc', 'Mc', 'Fc', 'Sc']]
    result = {}
    for key, label, profile in [('R', 'datU', 'a'), ('z', 'datZ', 'b')]:
        data = re.search(r'def '+label+r' : List ℕ := \[(.*?)\]', text, re.S)[1]
        rows = [int(s, 16) for s in re.findall(r'0x[0-9a-fA-F]+', data)]
        if len(rows) != n+1 or any(v >> (bits*(2*m+1)) for v in rows):
            raise ValueError('incorrect packed-row dimensions')
        packed, decimal = [F(0)]*(m+1), [F(0)]*(m+1)
        for w, c in collapse_modes(rows, 0, 0, m, bits, scale):
            j = w//2
            packed[abs(j)] += -c if key == 'z' and j < 0 else c
        if key == 'R':
            packed[0] += R0
        for (_, j), val in zip(seed['idx_'+key], seed[profile], strict=True):
            decimal[abs(j)] += -F(val) if key == 'z' and j < 0 else F(val)
        for derivative in (False, True):
            factors = [2*j if derivative else 1 for j in range(m+1)]
            sign = -1 if key == 'R' and derivative else 1
            weights = [v*f*sign for v, f in zip(packed, factors)]
            # A Q-16 profile differs from the packed seed by weighted l1 <= MU.
            # |2m| <= 2 exp(RHO |m|)/RHO supplies the real phi derivative bound.
            kam = 2*MU/RHO if derivative else MU
            discrepancy = sum(abs(a-b)*f for a, b, f in zip(packed, decimal, factors))
            if discrepancy >= kam:
                raise ArithmeticError('screen profile exceeds the KAM error envelope')
            kind = 'sin' if (key == 'z') != derivative else 'cos'
            result[key, derivative] = (kind, weights, kam)
    return result


def field_polynomials():
    cand, pot = load(TARGET)
    polys, _ = build(pot)
    crosscheck_cart(polys, cand)
    source = (DESIGN / 'DommaschkKamFieldData.lean').read_text()
    data = []
    for key in ('D', 'nR', 'nZ'):
        coeff = subst_R(polys[key], R0)
        name = 'd'+key
        block = lean_sp(name, '', to_list(coeff)).split('def ', 1)[1]
        if 'def '+block not in source:
            raise ValueError(f'{name} does not match the Lean-identified polynomial')
        data.append({m: Box.rational(v) for m, v in coeff.items()})
    return data


def powers(box, degree):
    out = [Box(S, S)]
    for _ in range(degree):
        out.append(out[-1]*box)
    return out


def harmonics(t, quadrant, degree):
    """Rigorous interval powers at the rational midpoint of the unit circle chart."""
    c, s = (1-t*t)/(1+t*t), 2*t/(1+t*t)
    for _ in range(quadrant):
        c, s = -s, c
    c, s = Box.rational(c), Box.rational(s)
    xs, ys = [Box(S, S)], [Box(0, 0)]
    for _ in range(degree):
        x, y = xs[-1], ys[-1]
        nx, ny = x*c-y*s, x*s+y*c
        xs.append(Box(max(-S, nx.lo), min(S, nx.hi)))
        ys.append(Box(max(-S, ny.lo), min(S, ny.hi)))
    return xs, ys


def profile_model(kind, coeffs, error, width):
    # Separate the rapidly decaying high harmonics using their exact amplitude sum.
    cut = 24
    tail = sum(abs(x) for x in coeffs[cut+1:])
    lip = sum(abs(x)*j for j, x in enumerate(coeffs[:cut+1]))
    rad = ceil((error + tail + lip*width)*S)
    return kind, [Box.rational(x) for x in coeffs[:cut+1]], Box(-rad, rad)


def angular_box(model, cs, sn):
    kind, weights, result = model
    trigs = cs if kind == 'cos' else sn
    for w, trig in zip(weights, trigs):
        result = result + w*trig
    return result


def launch_model(nangle):
    C, A = profile_coefficients('C'), profile_coefficients('A')
    modes = {}
    for key, (kind, inner, err) in C.items():
        _, outer, _ = A[key]
        delta = [a-c for a,c in zip(outer, inner)]
        center = [c + F(49, 100)*d for c,d in zip(inner, delta)]
        # Central profile and difference error have correlated KAM contributions.
        # Treating their errors independently encloses both actual laws at every u.
        width = F(1, nangle)
        modes[key] = (profile_model(kind, center, err, width),
                      profile_model(kind, delta, 2*err, width))
    return modes


def poly_slices(polys, c, s):
    """Freeze the angular variables and group monomials by (R-R0,z) degrees."""
    cp, sp = powers(c, 3), powers(s, 3)
    angles = {(i, j): cp[i]*sp[j] for i in range(4) for j in range(4)}
    result = []
    for poly in polys:
        groups = {}
        for (r, z, i, j), a in poly.items():
            key = (r, z)
            groups[key] = groups.get(key, Box(0, 0)) + a*angles[i, j]
        result.append(groups)
    return result


def poly_value(coeffs, rp, zp):
    val = Box(0, 0)
    for (i, j), c in coeffs.items():
        val += c*rp[i]*zp[j]
    return val


def evaluate(seeds, polys, offset):
    (R, dRu), (z, dzu) = seeds['R', False], seeds['z', False]
    R, z = R + offset*dRu, z + offset*dzu
    dR, mixed_r = seeds['R', True]
    dz, mixed_z = seeds['z', True]
    dR, dz = dR + offset*mixed_r, dz + offset*mixed_z
    Rpow = powers(R, 8)
    rp = powers(R-Box.rational(R0), max(i for p in polys for i, _ in p))
    zp = powers(z, max(j for p in polys for _, j in p))
    D, nr, nz = [poly_value(p, rp, zp) for p in polys]
    br, bp, bz = nr/Rpow[8], D/Rpow[7], nz/Rpow[8]
    # Components of X_u cross X_phi are (-R*z_u, z_u*R_phi-R_u*z_phi, R*R_u).
    flux = -br*R*dzu + bp*(dzu*dR-dRu*dz) + bz*R*dRu
    b2_int = br.abs_upper()**2 + bp.abs_upper()**2 + bz.abs_upper()**2
    return isqrt(b2_int)+1, bp.lo, flux.hi


def check_arithmetic():
    # Independent rational values on all sign combinations test directed rounding.
    for x in (F(-7, 11), F(0), F(13, 17)):
        for y in (F(-2, 3), F(0), F(19, 23)):
            a, b = Box.rational(x), Box.rational(y)
            results = [(a+b, x+y), (a-b, x-y), (a*b, x*y)]
            if y > 0:
                results.append((a/b, x/y))
            for box, value in results:
                if not box.lo <= value*S <= box.hi:
                    raise ArithmeticError('directed rounding failed the rational sanity check')

    # Entire nondegenerate input intervals, including a sign change in a product.
    a, b = Box(-5*S//7, S//3), Box(S//13, 8*S//9)
    for op, image in ((lambda x, y: x*y, a*b), (lambda x, y: x/y, a/b)):
        for x in (F(a.lo, S), F(a.hi, S)):
            for y in (F(b.lo, S), F(b.hi, S)):
                if not image.lo <= op(x, y)*S <= image.hi:
                    raise ArithmeticError('interval-corner sanity check failed')


def run(nangle, nrad):
    if min(nangle, nrad) < 1:
        raise ValueError('positive subdivision counts required')
    check_arithmetic()
    modes, polys = launch_model(nangle), field_polynomials()
    du = [Box(floor(F(-1, 20)*S + F(i*S, 10*nrad)),
              ceil(F(-1, 20)*S + F((i+1)*S, 10*nrad))) for i in range(nrad)]
    width = ceil(F(S, nangle))
    mag_max, bp_min, flux_max = 0, None, None
    for q in range(4):
        for j in range(nangle):
            cs, sn = harmonics(F(2*j+1, 2*nangle), q, 24)
            seeds = {k: tuple(angular_box(model, cs, sn) for model in pair)
                     for k, pair in modes.items()}
            c = Box(max(-S, cs[1].lo-width), min(S, cs[1].hi+width))
            s = Box(max(-S, sn[1].lo-width), min(S, sn[1].hi+width))
            slices = poly_slices(polys, c, s)
            for offset in du:
                mag, bp, flux = evaluate(seeds, slices, offset)
                mag_max = max(mag_max, mag)
                bp_min = bp if bp_min is None else min(bp_min, bp)
                flux_max = flux if flux_max is None else max(flux_max, flux)
    return dict(cells=4*nangle*nrad, denominator=S, B_upper_numerator=mag_max,
                Bphi_lower_numerator=bp_min, flux_upper_numerator=flux_max)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quarter-cells', type=int, default=1024)
    parser.add_argument('--radial-cells', type=int, default=8)
    args = parser.parse_args()
    result = run(args.quarter_cells, args.radial_cells)
    print(json.dumps(result, indent=2))
    upper = F(result['B_upper_numerator'], S)
    lower = F(result['Bphi_lower_numerator'], S)
    flux = F(result['flux_upper_numerator'], S)
    if upper > F(1048, 1000) or lower < F(103, 100) or flux > -F(17, 10**6):
        raise SystemExit('subdivision does not establish all three launch-slice bounds')
