"""External exact-arithmetic Q-31 arc check. Run with python3 interface_arc.py [--torus A|C].

The arc is theta = 0, 0 <= phi <= 1/5 in geometric radians. Input is the packed
128-bit Fourier seed that Lean actually uses, with KAM strip error 10^-12
at rho=9/1400 per profile (DommaschkKamEmbedded.dommaschk_Q16_embedded).
In the oracle angle psi=2*phi, a mode (k,m) acquires derivative factors k and
2*m. The phase shift in the Lean coefficients cancels its evaluation shift
(DommaschkKamATorus.eval_u₀A and eval_z₀A).

For order p=a+b, |k|^a |2m|^b <= 2^b p! exp(rho*(|k|+|m|))/rho^p.
This follows from the p-th term of exp at a nonnegative argument. It
transfers the existing weighted l1 error to each real derivative. For the
finite seed, each jet is a Taylor polynomial in phi about zero. The
Lagrange remainder uses the absolute Fourier moments and |phi|<=1/5.
All operations controlling signs use Python's arbitrary-precision integers
and Fractions. Decimal summaries are rounded outward for display.

With K=(R,phi,z), t=K_theta, p=K_phi and N=p cross t (outward for a
positively wound embedded meridian), use G_ij=K_i.K_j and H_ij=-N.K_ij.
Writing v=(iota,1), evaluate D=det(Gv,Hv), E=H(v,v), M=G(v,v). Since
N multiplies the source's II by a positive scalar, a zero of D with E>0
gives positive II(Y,Z) for any tangent Z with positive g(Y,Z).
The implication is in Theory/Stability/InterfacePrincipalDirection.lean.
The torus-A obstruction is independently checked in Lean by DommaschkInterfaceArcBounds.
The torus-C enclosure uses the same argument and is externally checked.
"""
import argparse
import hashlib
import re
from dataclasses import dataclass
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path

DATA = Path(__file__).resolve().parents[2] / 'PlasmaLean/Design/DommaschkKamAData.lean'
DATA_SHA = 'd1c57b90b04d513eb5dc53c00004be612e4b09059e0a4f27394bf47ca917abf4'
TORI = {
    'A': (DATA, DATA_SHA, 19, 89),
    'C': (DATA.with_name('DommaschkKamCData.lean'),
          '691a12a2723954263e567ba7cdf198e6f0c10e6bdccac2a54e73ca8c7874bde4', 85, 361),
}
END = F(1, 5)
RHO = F(9, 1400)
MU = F(1, 10**12)
JETS = [(a, b) for a in range(3) for b in range(3-a)]


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        corners = [self.lo*other.lo, self.lo*other.hi, self.hi*other.lo, self.hi*other.hi]
        return Interval(min(corners), max(corners))

    def __str__(self):
        scale = 10**12
        def decimal(integer):
            units, fractional = divmod(abs(integer), scale)
            sign = '-' if integer < 0 else ''
            return f'{sign}{units}.{fractional:012d}'
        return f'[{decimal(self.lo*scale//1)}, {decimal(-((-self.hi*scale)//1))}]'


def point(x):
    return Interval(x, x)


def collapse_modes(profile_rows, order_theta, order_phi, m, bits, scale):
    """Collapse signed modes onto theta=0. Each returned weight multiplies a
    trig function of frequency 2*j with the phase added by the derivatives."""
    coeffs = [0] * (2*m+1)
    mask = (1 << bits)-1
    offset = 1 << (bits-1)
    for k, row in enumerate(profile_rows):  # row k encodes the nonnegative half
        for j in range(-m, m+1):
            field = ((row >> (bits*(j+m))) & mask) - offset
            # Real series from the half and its conjugate reflected half:
            # 2 * field / 2^scale, including the packed constant term.
            coeffs[j+m] += 2*field * k**order_theta * (2*j)**order_phi
    return [(2*j, F(coeffs[j+m], 1 << scale)) for j in range(-m, m+1)]


def read_jets(degree, torus='A'):
    path, digest, _, _ = TORI[torus]
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError('unexpected packed seed file')
    text = raw.decode()
    def get_nat(name):
        return int(re.search(r'def '+name+r' : ℕ := (\d+)', text)[1])
    n, m, bits, scale = map(get_nat, ('Nc','Mc','Fc','Sc'))
    jets = {}
    for name, is_z in [('R',0), ('z',1)]:
        label = 'datZ' if is_z else 'datU'
        block = re.search(r'def '+label+r' : List ℕ := \[(.*?)\]', text, re.S)[1]
        rows = [int(t,16) for t in re.findall(r'0x[0-9a-fA-F]+',block)]
        if len(rows) != n+1 or any(x >> ((2*m+1)*bits) for x in rows):
            raise ValueError('packed row layout mismatch')
        for a,b in JETS:
            modes = collapse_modes(rows, a, b, m, bits, scale)
            phase = a+b-is_z
            poly = [sum(c*w**d for w,c in modes) * (1,0,-1,0)[(phase+d)%4] / factorial(d)
                    for d in range(degree+1)]
            if name == 'R' and a == b == 0:
                poly[0] += F(29,32)
            rem = sum(abs(c)*abs(w)**(degree+1) for w,c in modes)
            rem *= END**(degree+1)/factorial(degree+1)
            kam_error = MU * 2**b * factorial(a+b) / RHO**(a+b)
            jets[name,a,b] = (poly, rem + kam_error)
    return jets


def jet_enclosure(jet, arg):
    poly, error = jet
    s = point(poly[-1])
    for c in reversed(poly[:-1]):
        s = s*arg + point(c)
    return s + Interval(-error,error)


def dot(x,y):
    return sum((u*v for u,v in zip(x,y)), point(F(0)))


def geometry(jets, phi, iota):
    def jet(name,a,b):
        return jet_enclosure(jets[name,a,b],phi)
    R = jet('R',0,0)
    rt, rp, zt, zp = jet('R',1,0), jet('R',0,1), jet('z',1,0), jet('z',0,1)
    zero = point(F(0))
    t, p = (rt, zero, zt), (rp,R,zp)
    N = (R*zt, zp*rt-rp*zt, -R*rt)
    tt = (jet('R',2,0), zero, jet('z',2,0))
    tp = (jet('R',1,1), rt, jet('z',1,1))
    pp = (jet('R',0,2)-R, rp+rp, jet('z',0,2))
    g11, g12, g22 = dot(t,t), dot(t,p), dot(p,p)
    h11, h12, h22 = -dot(N,tt), -dot(N,tp), -dot(N,pp)
    g1, g2 = iota*g11+g12, iota*g12+g22
    h1, h2 = iota*h11+h12, iota*h12+h22
    return dict(det=g1*h2-g2*h1, E=iota*h1+h2, M=iota*g1+g2,
                area2=dot(N,N))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--torus', choices=TORI, default='A')
    ap.add_argument('--cells', type=int, default=16)
    ap.add_argument('--degree', type=int, default=24, help='Taylor degree for each seed jet')
    args = ap.parse_args()
    if args.cells < 1:
        ap.error('cells must be positive')
    if args.degree < 0:
        ap.error('Taylor degree must be nonnegative')
    jets = read_jets(args.degree, args.torus)
    precision = 10**16
    root = isqrt(5*precision**2)
    _, _, offset, divisor = TORI[args.torus]
    iota = Interval(-(offset+F(root+1,precision))/divisor, -(offset+F(root,precision))/divisor)
    ends = [geometry(jets, point(x), iota)['det'] for x in (F(0), END)]
    cells = [geometry(jets, Interval(END*i/args.cells, END*(i+1)/args.cells), iota)
             for i in range(args.cells)]
    print(f'Torus {args.torus}. Number of rational cells on [0,1/5] = {args.cells}, Taylor degree = {args.degree}')
    print('D(0)', ends[0], 'D(1/5)', ends[1])
    bounds = {}
    for key in ['E','M','area2']:
        bounds[key] = Interval(min(c[key].lo for c in cells), max(c[key].hi for c in cells))
        print(key, bounds[key])
    if not (ends[0].hi < 0 < ends[1].lo and all(x.lo > 0 for x in bounds.values())):
        raise ArithmeticError('inconclusive signs or interval too wide')


if __name__ == '__main__':
    main()
