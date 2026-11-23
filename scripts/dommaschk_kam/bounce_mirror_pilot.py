"""External centered Taylor-model pilot for one small cell of the deep launch strip.

Run OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_mirror_pilot.py.
A non-rigorous DOP853 trajectory proposes the coefficients of a continuous-time
piecewise polynomial. The checker treats those coefficients as dyadic input,
bounds their defects against the identified field, and propagates the Euclidean
distance using a one-sided Jacobian bound. It explicitly charges every jump
between independently fitted segments. All acceptance decisions use integers.

The default birth cell has |alpha| <= 2^-35 and |u-0.49| <= 2^-22, on
the same C+u(A-C) cut as bounce_launch_box. At a verified crossing band the
code encloses d|B|^2/d|tau|, for tau the signed geometric angle since launch.
For each fixed height, continuity and positivity of that outward derivative
at all level crossings give the unique first mirror on each traced arc.
"""
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import ceil, factorial, floor, isqrt

import numpy as np
from scipy.integrate import solve_ivp

from bounce_collar import harmonic_polynomial, trig_center
from bounce_launch_box import (
    Box, R0, S, angular_box, field_polynomials, harmonics, launch_model,
)
from bounce_screen import load_inputs, seed_cut


ORDER = 7
SCALE = 1 << 80
ALPHA_WIDTH = F(1, 2**35)
U_WIDTH = F(1, 2**22)
HEIGHTS = (F('1.0595923312168822'), F('1.0601092782791866'))


def ceil_div(a, b):
    return -(-a//b)


class Model:
    """p(s) + [-e,e] on -1 <= s <= 1. Coefficients and e have denominator SCALE."""
    __slots__ = ('a', 'e')

    def __init__(self, a, e=0):
        self.a, self.e = a, e

    @staticmethod
    def rational(x):
        value = F(x)*SCALE
        return Model([round(value)], int(value.denominator != 1))

    @staticmethod
    def box(x):
        lo, hi = x.lo*(SCALE//S), x.hi*(SCALE//S)
        c = (lo+hi)//2
        return Model([c], max(c-lo, hi-c))

    def __add__(self, other):
        a, b = self.a, other.a
        if len(a)<len(b):
            a,b = b,a
        return Model([v+b[i] if i<len(b) else v for i,v in enumerate(a)], self.e+other.e)

    def __neg__(self):
        return Model([-v for v in self.a], self.e)

    def __sub__(self, other):
        return self+(-other)

    def __mul__(self, other):
        a,b = self.a,other.a
        conv = [0]*(len(a)+len(b)-1)
        for i,v in enumerate(a):
            for j,w in enumerate(b):
                conv[i+j] += v*w
        c = [v//SCALE for v in conv[:ORDER+1]]
        # Charge discarded coefficients, dyadic rounding, then input remainders.
        err = sum(abs(v) for v in conv[ORDER+1:])+sum(v%SCALE for v in conv[:ORDER+1])
        err += self.e*(sum(map(abs,b))+other.e)+other.e*sum(map(abs,a))
        return Model(c, ceil_div(err, SCALE))

    def integer(self, k):
        return Model([k*v for v in self.a], abs(k)*self.e)

    def bound(self):
        radius = self.e+sum(abs(v) for v in self.a[1:])
        return F(self.a[0]-radius,SCALE), F(self.a[0]+radius,SCALE)

    def endpoint(self, sign):
        return sum(v*sign**k for k,v in enumerate(self.a))

    def restrict(self, low, high):
        """Compose with the affine map from [-1,1] to [low,high] and retain the remainder."""
        if not -1<=low<=high<=1:
            raise ValueError('normalized time restriction must lie in [-1,1]')
        mid = Model.rational((F(low)+high)/2)
        rad = Model.rational((F(high)-low)/2)
        affine = Model([mid.a[0],rad.a[0]],mid.e+rad.e)
        result = horner([Model([a]) for a in reversed(self.a)],affine)
        return Model(result.a,result.e+self.e)


ZERO, ONE = Model.rational(0), Model.rational(1)
R0M = Model.rational(R0)


def polynomial_data():
    data = []
    for p in field_polynomials():
        group = []
        for axis in (None,0,1):
            derivative = {}
            for powers,x in p.items():
                ix = list(powers)
                y = x
                if axis is not None:
                    if not ix[axis]:
                        continue
                    n = ix[axis]
                    y = Box(n*x.lo,n*x.hi)
                    ix[axis] -= 1
                derivative[tuple(ix)] = y
            polys = harmonic_polynomial(derivative)
            group.append({k:[[Model.box(v) for v in row] for row in rows]
                          for k,rows in polys.items()})
        data.append(group)
    return data


def angle_models(center, half_step, alpha_width, origin=()):
    """Enclose harmonics about origin + center, with jitter at most alpha_width."""
    angles = [ONE]
    for k in range(1,4):
        # Range reduction by exact doubling avoids Taylor evaluation at large angles.
        c,s = trig_center(2*k*center/64)
        for _ in range(6):
            c,s = c*c-s*s, Box(2*S,2*S)*c*s
        if origin:
            co, si = origin[k-1]
            c, s = co*c-si*s, si*c+co*s
        phase = [Model.box(c), Model.box(s), -Model.box(c), -Model.box(s)]
        w = 2*k*half_step
        for initial in (1,0):
            a = []
            error = ceil((abs(w)**(ORDER+1)/factorial(ORDER+1)+2*k*alpha_width)*SCALE)
            for j in range(ORDER+1):
                v = phase[(initial-j)%4]*Model.rational(w**j/factorial(j))
                a.append(v.a[0])
                error += v.e
            angles.append(Model(a,error))
    return angles


def horner(row,x):
    value = row[0]
    for a in row[1:]:
        value = value*x+a
    return value


def evaluate(p, rz, angles):
    u,z = rz[0]-R0M,rz[1]
    coeffs = {k:horner([horner(row,u) for row in rows],z) for k,rows in p.items()}
    value, phi = ZERO, ZERO
    for k,v in coeffs.items():
        value = value+v*angles[k]
        if k%2:
            phi = phi+(v*angles[k+1]).integer(k+1)
        elif k:
            phi = phi-(v*angles[k-1]).integer(k)
    return value, phi


def launch(alpha_width, u_width):
    # The width used by launch_model is in doubled phase, psi=2*alpha.
    modes = launch_model(floor(1/(2*alpha_width)))
    cs,sn = harmonics(F(0),0,24)
    delta = Box(-ceil(S*u_width),ceil(S*u_width))
    return [Model.box(angular_box(modes[k,False][0],cs,sn)
                      +delta*angular_box(modes[k,False][1],cs,sn)) for k in ('R','z')]


def proposals(ev, initial, sign, dt, count):
    def rhs(t,x):
        return sign*np.asarray(ev.rhs(sign*t,x[0],x[1]))
    solution = solve_ivp(rhs,(0,float(dt*count)),initial,method='DOP853',
                         rtol=3e-14,atol=1e-15,max_step=float(dt),dense_output=True)
    if not solution.success:
        raise ArithmeticError(solution.message)
    s = np.cos(np.arange(ORDER+1)*np.pi/ORDER)
    vandermonde = np.polynomial.polynomial.polyvander(s,ORDER)
    for i in range(count):
        positions = solution.sol((i+(s+1)/2)*float(dt))
        floats = np.linalg.solve(vandermonde,positions.T).T
        yield [Model([round(float(v)*SCALE) for v in a]) for a in floats]


def radius_step(radius, defect, mu, dt):
    """For y' <= mu*y+defect use exp(max(0,mu)*dt) <= 1/(1-max(0,mu)*dt)."""
    growth = max(F(0),mu)*dt
    if growth >= 1:
        raise ArithmeticError('logarithmic norm step too large')
    return ceil((radius+dt*defect*SCALE)/(1-growth))


def quotient_range(num, denom):
    a,b = num.bound()
    c,d = denom.bound()
    if c<=0:
        raise ArithmeticError('denominator is not bounded from zero')
    values = (a/c,a/d,b/c,b/d)
    return min(values),max(values)


def radius_check(data, angles, nominal, incoming, dt, sign, tube_radius):
    true = [Model(x.a,tube_radius) for x in nominal]
    val = [evaluate(g[0],true,angles)[0] for g in data]
    grad = [[evaluate(p,true,angles)[0] for p in g[1:]] for g in data]
    D,nr,nz = val
    if true[0].bound()[0]<=0 or D.bound()[0]<=0:
        raise ArithmeticError('field-line coordinates lose regularity')
    D2 = D*D
    jac = [[(grad[i+1][j]*D-n*grad[0][j]).integer(sign) for j in (0,1)]
           for i,n in enumerate((nr,nz))]
    diagonal = max(quotient_range(jac[i][i],D2)[1] for i in (0,1))
    off = quotient_range(jac[0][1]+jac[1][0],D2.integer(2))
    mu = diagonal+max(map(abs,off))  # Gershgorin on (J+J^T)/2, Euclidean norm.
    # Normalized proposal time increases from 0 in both directions; F is multiplied by sign.
    center_fields = [evaluate(g[0],nominal,angles)[0] for g in data]
    den = center_fields[0]
    defects = []
    for x,n in zip(nominal,center_fields[1:]):
        slope = Model([j*x.a[j] for j in range(1,len(x.a))])*Model.rational(2/dt)
        bounds = quotient_range(slope*den-n.integer(sign),den)
        defects.append(ceil(max(map(abs,bounds))*SCALE))
    defect = F(isqrt(sum(x*x for x in defects))+1,SCALE)
    final = radius_step(incoming,defect,mu,dt)
    return final,defect,val,grad


def geometry(data, angles, tube, val, grad, sign, want_slope):
    R = tube[0]
    rp = [ONE]
    for _ in range(17):
        rp.append(rp[-1]*R)
    D,nr,nz = val
    # U = R^16 |B|^2; compare near the threshold before dividing.
    U = (R*D)*(R*D)+nr*nr+nz*nz
    gaps = [quotient_range(U-rp[16]*Model.rational(h*h),rp[16]) for h in HEIGHTS]
    derivative = None
    if want_slope:
        dphi = [evaluate(g[0],tube,angles)[1] for g in data]
        # D*dP/dphi on the actual field line.
        material = [D*f+nr*g[0]+nz*g[1] for f,g in zip(dphi,grad)]
        # D*dU/dphi, with D*dR/dphi = nR.
        tmp = R*D
        Du = (tmp*(nr*D+R*material[0])+nr*material[1]+nz*material[2]).integer(2)
        derivative = quotient_range((R*Du-(nr*U).integer(16)).integer(sign),rp[17]*D)
    return gaps,derivative


def check_arithmetic():
    """Sanity checks with exact polynomials and a translating manufactured field."""
    def value(p,s):
        return sum(F(a,SCALE)*s**j for j,a in enumerate(p.a))
    p = Model([SCALE//(j+2)*(-1)**j for j in range(ORDER+1)],SCALE//99)
    q = Model([SCALE//(2*j+3) for j in range(ORDER+1)],SCALE//75)
    product = p*q
    for s in (F(-1), F(-2,7), F(1,3), F(1)):
        for sp in (-1,1):
            for sq in (-1,1):
                exact = (value(p,s)+sp*F(p.e,SCALE))*(value(q,s)+sq*F(q.e,SCALE))
                if abs(exact-value(product,s))*SCALE>product.e:
                    raise ArithmeticError('Taylor product/remainder sanity check failed')
        # Check the affine subinterval reparametrization used for action quadrature.
        low,high = F(-2,3),F(1,5)
        restricted = p.restrict(low,high)
        raw = value(p,(low+high)/2+(high-low)*s/2)
        if abs(raw-value(restricted,s))*SCALE+p.e>restricted.e:
            raise ArithmeticError('Taylor subinterval restriction sanity check failed')
    # D=1, nR=1/4, nZ=-1/8. The line moves at constant speed, and its
    # physical strength squared is R^-14+(nR^2+nZ^2)R^-16.
    vr,vz,dt = F(1,4),F(-1,8),F(1,32)
    data = [[{0:[[Model.rational(v)]]},{},{}] for v in (F(1),vr,vz)]
    for sign in (-1,1):
        reference = [Model([int(a*SCALE),int(sign*v*dt*SCALE/2)])
                     for a,v in ((F(1),vr),(F(0),vz))]
        rad = 1 << 25
        end,defect,val,grad = radius_check(data,[ONE],reference,0,dt,sign,rad)
        if end>=rad or defect>F(1,10**18):
            raise ArithmeticError('constant-velocity residual sanity check failed')
        tube = [Model(x.a,rad) for x in reference]
        gaps,slope = geometry(data,[ONE],tube,val,grad,sign,True)
        for s in (F(-1),F(0),F(1)):
            r = value(reference[0],s)
            strength = r**(-14)+(vr*vr+vz*vz)*r**(-16)
            deriv = sign*vr*(-14*r**(-15)-16*(vr*vr+vz*vz)*r**(-17))
            if not slope[0]<=deriv<=slope[1] or any(
                not lo<=strength-h*h<=hi for h,(lo,hi) in zip(HEIGHTS,gaps)
            ):
                raise ArithmeticError('material derivative/strength sanity check failed')


@dataclass(frozen=True, slots=True)
class MirrorSegment:
    """Certified |tau| interval [index*dt,(index+1)*dt] and dyadic proof inputs.

    coeffs holds two ascending Taylor coefficient tuples in s=2*(|tau|/dt-index)-1.
    All integer coefficients and radii use SCALE. The outgoing radius is also an
    upper bound at every intermediate time. The trial radius verifies first exit.
    """
    index: int
    sign: int
    dt: F
    alpha_width: F
    coeffs: tuple
    incoming_radius: int
    outgoing_radius: int
    trial_radius: int
    defect: F
    origin: tuple = ()

    def models(self, low=F(-1), high=F(1)):
        """Return ([R,z], harmonics) on the whole slab. Each Model is independent."""
        nominal_tube = [Model(list(a),self.outgoing_radius) for a in self.coeffs]
        half = self.sign*self.dt/2
        center = self.sign*(self.index+F(1,2))*self.dt
        if low!=-1 or high!=1:
            nominal_tube = [x.restrict(low,high) for x in nominal_tube]
            center += half*(F(low)+high)/2
            half *= (F(high)-low)/2
        angles = angle_models(center,half,self.alpha_width,self.origin)
        return nominal_tube,angles

    def fields(self, data, low=F(-1), high=F(1)):
        """Return (tube, angles, [D,nR,nZ]); dℓ/d|tau| = sqrt((R D)^2+nR^2+nZ^2)/D."""
        tube,angles = self.models(low, high)
        return tube,angles,[evaluate(g[0],tube,angles)[0] for g in data]


def certified_segments(data, seed, ev, init, sign, dt, count, alpha_width, origin=()):
    """Yield immutable proof records in increasing outward angle, including every accepted slab."""
    if sign not in (-1,1) or dt<=0 or count<=0:
        raise ValueError('a direction, positive step, and positive count are required')
    previous = [x.a[0] for x in seed]
    radius = isqrt(sum(x.e*x.e for x in seed))+1
    for i,nominal in enumerate(proposals(ev,init,sign,dt,count)):
        radius += isqrt(sum((x.endpoint(-1)-y)**2 for x,y in zip(nominal,previous)))+1
        angles = angle_models(sign*(i+F(1,2))*dt,sign*dt/2,alpha_width,origin)
        trial = max(2*radius,ceil(F(1,10**10)*SCALE))
        for _ in range(5):
            final,defect,_,_ = radius_check(data,angles,nominal,radius,dt,sign,trial)
            if final<trial:
                break
            trial = 2*final+2
        else:
            raise ArithmeticError(f'bootstrap failed at step {i}')
        yield MirrorSegment(i,sign,dt,alpha_width,tuple(tuple(x.a) for x in nominal),
                            radius,final,trial,defect,origin)
        previous = [x.endpoint(1) for x in nominal]
        radius = final


def check_crossings(data, segments, geometry_on=geometry):
    """Prove both first-root brackets and the signed derivative throughout the height band."""
    max_radius, max_trial, max_defect = 0,0,F(0)
    first = [None,None]
    last = [None,None]
    slopes = [None,None]
    band_slope = None
    expected = 0
    for segment in segments:
        i,dt,sign = segment.index,segment.dt,segment.sign
        if i!=expected or (i and (dt!=step or sign!=direction)):
            raise ValueError('a single contiguous direction from the launch is required')
        expected,step,direction = i+1,dt,sign
        tube,angles,val = segment.fields(data)
        gaps,_ = geometry_on(data,angles,tube,val,None,sign,False)
        if i == 0 and gaps[0][1]>=0:
            raise ArithmeticError('initial fully allowed slab not verified')
        slope = None
        if gaps[0][1]>=0 and gaps[1][0]<=0:
            grad = [[evaluate(p,tube,angles)[0] for p in g[1:]] for g in data]
            _,slope = geometry_on(data,angles,tube,val,grad,sign,True)
            band_slope = slope[0] if band_slope is None else min(band_slope,slope[0])
        for j,(lo,hi) in enumerate(gaps):
            if hi<0:
                if first[j] is not None and last[j] is None:
                    raise ArithmeticError('ambiguous window returns below threshold')
            elif first[j] is None:
                first[j] = i*dt
            if first[j] is not None and last[j] is None:
                if lo>0:
                    last[j] = i*dt
                else:
                    if slope is None:
                        raise ArithmeticError('inconsistent height-window comparison')
                    slopes[j] = slope[0] if slopes[j] is None else min(slopes[j],slope[0])
        max_radius = max(max_radius,segment.outgoing_radius)
        max_trial = max(max_trial,segment.trial_radius)
        max_defect = max(max_defect,segment.defect)
        if all(t is not None for t in last):
            break
    if not expected:
        raise ValueError('empty trajectory')
    return dict(direction=sign,steps=i+1,max_radius_numerator=max_radius,max_trial_numerator=max_trial,
                max_defect_numerator=ceil(max_defect*SCALE),
                brackets=[[str(a),str(b)] for a,b in zip(first,last)],
                outward_B2_slope_lower_numerators=[floor(s*SCALE) if s is not None else None for s in slopes],
                band_slope_lower_numerator=floor(band_slope*SCALE) if band_slope is not None else None,
                success=band_slope is not None and band_slope>0 and all(t is not None for t in last)
                and all(a is not None and a>0 for a in slopes))


def pilot_inputs(alpha_width=ALPHA_WIDTH,u_width=U_WIDTH):
    """Return (data,seed,ev,init) for certified_segments; the birth is centered at (alpha,u)=(0,.49)."""
    if not (0 < alpha_width <= F(1,2) and 0 < u_width <= F(1,20)):
        raise ValueError('positive half-widths within the declared deep strip required')
    check_arithmetic()
    ev,seeds = load_inputs()
    c,a = [seed_cut(*s,np.array([0.]))[0][:,0] for s in seeds]
    return polynomial_data(),launch(alpha_width,u_width),ev,c+0.49*(a-c)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--step',type=F,default=F(1,32))
    ap.add_argument('--limit',type=F,default=F(21,4))
    ap.add_argument('--alpha-half-width',type=F,default=ALPHA_WIDTH)
    ap.add_argument('--u-half-width',type=F,default=U_WIDTH)
    args = ap.parse_args()
    if min(args.step,args.limit)<=0:
        raise ValueError('positive step and limit required')
    inputs = pilot_inputs(args.alpha_half_width,args.u_half_width)
    results = [check_crossings(inputs[0],certified_segments(
        *inputs,sign,args.step,ceil(args.limit/args.step),args.alpha_half_width)) for sign in (-1,1)]
    print(json.dumps(dict(scale=SCALE,step=str(args.step),alpha_half_width=str(args.alpha_half_width),
                          u_half_width=str(args.u_half_width),heights=list(map(str,HEIGHTS)),runs=results),indent=2))
    if not all(x['success'] for x in results):
        raise SystemExit('pilot did not verify both regular mirrors')
