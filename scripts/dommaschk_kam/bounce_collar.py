"""Validate a two-sided field-line collar on the complete deep bounce launch strip.

Run python3 scripts/dommaschk_kam/bounce_collar.py. The default covers the
entire C+u(A-C) interpolation at theta=0, 11/25 <= u <= 27/50, at every
launch angle and throughout |tau| <= 1/8. Input geometry, rational field
identifications and outward dyadics are those of bounce_launch_box. The time
variable is geometric toroidal angle tau = phi - phi_launch. The test strength
1.0595 is below the fixed deep screening window in bounce_screen_20261123.json.
All field values are in the candidate's dimensionless normalization.

At each step an inflated (R,z) rectangle T contains the incoming rectangle X.
With F=(nR/D,nZ/D), the exact interval test is X+[0,dt]*F(T) strictly inside
T (reverse the sign for backward time). R>0 and D>0 make the vector field smooth
on an open neighbourhood. Local existence, the integral equation, first exit
and continuation on compact subsets then give existence and uniqueness through
the entire step. X+dt*F(T) encloses the outgoing section. A finite induction
gives the asserted collar for every seed, including the exact Q-16 profiles.
"""
import argparse
import json
from functools import cache
from fractions import Fraction as F
from math import ceil, comb, factorial, floor, isqrt

from bounce_launch_box import (
    R0, S, Box, angular_box, check_arithmetic, field_polynomials, harmonics,
    launch_model, powers,
)
from emit_flowfield import build, harm, load


ZERO = Box(0, 0)
B_REFERENCE = F(26, 25)
STRENGTH_LIMIT = F(10595, 10000)


def trig_center(x):
    """Outward cosine and sine via degree-21 Taylor and |f^(22)| <= 1."""
    def series(parity):
        terms = [(1 if k % 4 < 2 else -1)*x**k/factorial(k)
                 for k in range(parity, 22, 2)]
        remainder = abs(x)**22/factorial(22)
        mid = sum(terms)
        return Box(floor((mid-remainder)*S), ceil((mid+remainder)*S))
    return series(0), series(1)


def shifted_polynomials():
    """Subtract k R^7 first, so evaluating Bphi=k+(D-k R^7)/R^7 cancels dependency."""
    D, nr, nz = field_polynomials()
    diff = D.copy()
    for j in range(8):
        key = (j, 0, 0, 0)
        coeff = B_REFERENCE * comb(7, j) * R0**(7-j)
        diff[key] = diff.get(key, ZERO) - Box.rational(coeff)
    return [harmonic_polynomial(p) for p in (diff, nr, nz)]


@cache
def harmonic_terms(a, b):
    """Expand c^a s^b with w=exp(i*2phi), c=(w+w^-1)/2, s=(w-w^-1)/(2i)."""
    weights = {}
    for i in range(a+1):
        for j in range(b+1):
            k = a+b-2*(i+j)
            if k < 0 or (k == 0 and b%2):
                continue
            num = comb(a,i)*comb(b,j)*(-1)**(j+b//2) * (2 if k else 1)
            key = 2*k-int(b%2)
            weights[key] = weights.get(key, F(0))+F(num, 2**(a+b))
    # Check the entire identity by expanding cos/sin(k*2phi) as Re/Im(c+is)^k,
    # subtracting c^a s^b and reducing s^2 to 1-c^2 in exact arithmetic.
    terms = [(a,b,-1)]
    for key,weight in weights.items():
        polynomial = harm((key+1)//2)[key%2]
        terms.extend((i,j,weight*v) for (_,_,i,j),v in polynomial.items())
    remainder = {}
    for i,j,v in terms:
        for l in range(j//2+1):
            key = (i+2*l, j%2)
            remainder[key] = remainder.get(key, F(0))+v*comb(j//2,l)*(-1)**l
    if any(remainder.values()):
        raise ArithmeticError('harmonic transformation failed its exact polynomial identity')
    return [(key, Box.rational(v)) for key,v in weights.items() if v]


def harmonic_polynomial(poly):
    """Group by actual harmonics; store each spatial coefficient as nested Horner rows."""
    layers = {}
    for (r, z, a, b), coeff in poly.items():
        for key, weight in harmonic_terms(a, b):
            group = layers.setdefault(key, {})
            group[r,z] = group.get((r,z), ZERO) + coeff*weight
    result = {}
    for k, p in layers.items():
        p = {ix:v for ix,v in p.items() if v != ZERO}
        if not p:
            continue
        rows = []
        for j in reversed(range(1+max(z for _, z in p))):
            degree = max((r for r,z in p if z == j), default=0)
            rows.append([p.get((r,j), ZERO) for r in reversed(range(degree+1))])
        result[k] = rows
    return result


def trig_slab(cs, sn, rotations, width):
    angles = [Box(S,S)]
    for k,(c,s) in enumerate(rotations, 1):
        center_c, center_s = cs[k]*c-sn[k]*s, sn[k]*c+cs[k]*s
        radius = k*width
        for a, derivative in ((center_s, center_c), (center_c, center_s)):
            # Use the smaller of global Lipschitz and local Taylor-with-remainder bounds.
            numerator = 2*derivative.abs_upper()*radius+radius**2
            error = min(radius, -(-numerator//(2*S)))
            angles.append(Box(max(-S, a.lo-error), min(S, a.hi+error)))
    return angles


def horner(coeffs, x):
    value = coeffs[0]
    for a in coeffs[1:]:
        value = value*x+a
    return value


def poly_values(polys, R, z, angles):
    u = R-Box.rational(R0)
    out = []
    for p in polys:
        val = ZERO
        for k,rows in p.items():
            coeff = horner([horner(row, u) for row in rows], z)
            val = val+coeff*angles[k]
        out.append(val)
    return out


def field_on(polys, angles, R, z):
    diff, nr, nz = poly_values(polys, R, z, angles)
    if R.lo <= 0:
        raise ArithmeticError('tube reaches R=0')
    Rpow = powers(R, 8)
    bp = Box.rational(B_REFERENCE) + diff/Rpow[7]
    if bp.lo <= 0:
        raise ArithmeticError('tube reaches Bphi=0')
    br, bz = nr/Rpow[8], nz/Rpow[8]
    mag = isqrt(sum(x.abs_upper()**2 for x in (br, bp, bz))) + 1
    # D=R^7 Bphi; the same positive enclosure bounds the ODE denominator.
    D = Rpow[7]*bp
    return (nr/D, nz/D), mag, bp.lo


def advance(incoming, polys, angles, sign, step):
    duration = Box.rational(sign*step)
    times = Box(min(0, duration.lo), max(0, duration.hi))
    # Small initial padding is a heuristic only. The inclusion below is decisive.
    guess = [ceil(step*S/10)]*2
    for _ in range(8):
        tube = [Box(x.lo-p, x.hi+p) for x, p in zip(incoming, guess)]
        velocity, mag, bp = field_on(polys, angles, *tube)
        swept = [x+times*v for x,v in zip(incoming, velocity)]
        if all(t.lo < a.lo and a.hi < t.hi for t, a in zip(tube, swept)):
            end = tuple(x+duration*v for x, v in zip(incoming, velocity))
            return end, mag, bp, max(x.abs_upper() for x in velocity)
        guess = [max(old, ceil(F(9, 8)*step*v.abs_upper())+2)
                 for old, v in zip(guess, velocity)]
    raise ArithmeticError('Picard tube did not close')


def check_field_values(polys):
    """Independent exact point checks against original powers of R, c and s."""
    _, potential = load()
    originals, _ = build(potential)
    for R,z,t,q in ((F(19,20), F(-1,20), F(1,5), 1),
                    (F(99,100), F(1,25), F(2,3), 0),
                    (F(9,10), F(-1,100), F(1,4), 3)):
        c,s = (1-t*t)/(1+t*t), 2*t/(1+t*t)
        for _ in range(q):
            c,s = -s,c
        vals = [sum(v*R**a*z**b*c**i*s**j for (a,b,i,j),v in originals[k].items())
                for k in ('D','nR','nZ')]
        D,nr,nz = vals
        cs,sn = harmonics(t, q, 3)
        angles = trig_slab(cs, sn, [trig_center(F(0))]*3, 0)
        rbox,zbox = Box.rational(R),Box.rational(z)
        diff,br_num,bz_num = poly_values(polys, rbox, zbox, angles)
        for interval, expected in zip((diff,br_num,bz_num), (D-B_REFERENCE*R**7,nr,nz)):
            if not interval.lo <= expected*S <= interval.hi:
                raise ArithmeticError('rational harmonic recombination failed')
        velocity, mag, bp = field_on(polys, angles, rbox, zbox)
        for v,numerator in zip(velocity,(nr,nz)):
            if not v.lo <= numerator*S/D <= v.hi:
                raise ArithmeticError('rational field-line slope check failed')
        norm2 = (D/R**7)**2+(nr/R**8)**2+(nz/R**8)**2
        if mag**2 < S*S*norm2 or bp > S*D/R**7:
            raise ArithmeticError('rational strength check failed')


def check_constant_flow():
    """The same stepper must enclose both exact endpoints of a translating test field."""
    rseed, zseed, vr, vz, dt = F(1), F(1,20), F(1,4), F(-1,7), F(1,16)
    # D=R^7, nR=vr*R^7, nZ=vz*R^7, hence both coordinate velocities are constant.
    coeffs = [comb(7, j)*R0**(7-j) for j in range(8)]
    def component(scale):
        return harmonic_polynomial({(j,0,0,0): Box.rational(scale*c)
                                    for j,c in enumerate(coeffs)})
    model = [component(1-B_REFERENCE), component(vr), component(vz)]
    starting = (Box.rational(rseed), Box.rational(zseed))
    for sign in (-1, 1):
        end, _, _, _ = advance(starting, model, [Box(S,S)], sign, dt)
        exact = (rseed+sign*dt*vr, zseed+sign*dt*vz)
        if any(not x.lo <= v*S <= x.hi for x,v in zip(end, exact)):
            raise ArithmeticError('constant-velocity continuation sanity check failed')


def run(nangle, nrad, dt, steps):
    if min(nangle, nrad, dt, steps) <= 0:
        raise ValueError('positive subdivision counts and step size required')
    check_arithmetic()
    check_constant_flow()
    modes, polys = launch_model(nangle), shifted_polynomials()
    check_field_values(polys)
    offsets = [Box(floor(S*(F(-1,20)+F(i,10*nrad))), ceil(S*(F(-1,20)+F(i+1,10*nrad))))
               for i in range(nrad)]
    rot = {sign: [[trig_center(sign*k*(2*i+1)*dt) for k in range(1,4)]
                  for i in range(steps)] for sign in (-1,1)}
    # Doubled launch phase is within 1/nangle of the rational chart midpoint.
    # Within a time step, doubled phase is within dt of its temporal midpoint.
    width = ceil((F(1, nangle)+dt)*S)
    mag_max, bp_min, speed_max = 0, None, 0
    for quadrant in range(4):
        for j in range(nangle):
            cs, sn = harmonics(F(2*j+1, 2*nangle), quadrant, 24)
            seeds = [tuple(angular_box(m, cs, sn) for m in modes[k, False])
                     for k in ('R', 'z')]
            initial = [tuple(center+off*delta for center, delta in seeds)
                       for off in offsets]
            for sign in (-1,1):
                boxes = initial[:]
                for rotation in rot[sign]:
                    angles = trig_slab(cs, sn, rotation, width)
                    for k, box in enumerate(boxes):
                        boxes[k], mag, bp, speed = advance(box, polys, angles, sign, dt)
                        mag_max = max(mag_max, mag)
                        bp_min = bp if bp_min is None else min(bp_min, bp)
                        speed_max = max(speed_max, speed)
    return dict(half_collar=str(dt*steps), step=str(dt), steps_per_direction=steps,
                launch_cells=4*nangle*nrad, tube_count=8*nangle*nrad*steps, denominator=S,
                B_upper_numerator=mag_max, Bphi_lower_numerator=bp_min,
                coordinate_speed_upper_numerator=speed_max)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quarter-cells', type=int, default=256)
    parser.add_argument('--radial-cells', type=int, default=2)
    parser.add_argument('--step', type=F, default=F(1, 256))
    parser.add_argument('--steps', type=int, default=32)
    args = parser.parse_args()
    result = run(args.quarter_cells, args.radial_cells, args.step, args.steps)
    print(json.dumps(result, indent=2))
    if F(result['B_upper_numerator'], S) >= STRENGTH_LIMIT:
        raise SystemExit('enclosure exceeds the lower mirror-height test')
