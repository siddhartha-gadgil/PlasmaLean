"""Validate the field-line error in coordinates e=M(t)v.

Each M is affine in outward time with dyadic endpoints shared by adjacent
steps. The proposal approximates the variational flow. Acceptance uses the
actual interval Jacobian on the physical tube, the positive determinant of M,
and the logarithmic norm of M^-1(JM-M'). This accounts for the rotation and
stretch of the physical error region along the reference trace.
"""
from fractions import Fraction as F
from math import ceil, isqrt

import numpy as np
from scipy.linalg import expm

import bounce_mirror_pilot as pilot


FRAME_SCALE = 1 << 40


def norm_upper(components):
    """Upper Euclidean norm for arbitrary rational components in the caller's units."""
    total = sum(x*x for x in components)
    return isqrt(ceil(total))+1


def product(a, b):
    return [[a[i][0]*b[0][j]+a[i][1]*b[1][j] for j in (0,1)] for i in (0,1)]


def jacobian(data, angles, tube, sign):
    val = [pilot.evaluate(g[0],tube,angles)[0] for g in data]
    d = [[pilot.evaluate(p,tube,angles)[0] for p in g[1:]] for g in data]
    den = val[0]
    if tube[0].bound()[0]<=0 or den.bound()[0]<=0:
        raise ArithmeticError('frame trial reaches singular field coordinates')
    jnum = [[(d[i+1][k]*den-val[i+1]*d[0][k]).integer(sign) for k in (0,1)] for i in (0,1)]
    return jnum, den*den


def propose_frame(start, jnum, den2, dt):
    """Choose a dyadic endpoint. Floating-point values never enter acceptance bounds."""
    j = np.array([[float(sum(pilot.quotient_range(x,den2))/2) for x in row] for row in jnum])
    end = expm(float(dt)*j) @ np.asarray(start,dtype=float)
    return [[round(x) for x in row] for row in end]


def affine_frame(start, end, dt):
    factor = pilot.SCALE//(2*FRAME_SCALE)
    m = [[pilot.Model([(a+b)*factor,(b-a)*factor]) for a,b in zip(row,next_row,strict=True)]
         for row,next_row in zip(start,end,strict=True)]
    rate = [[pilot.Model.rational(F(b-a,FRAME_SCALE)/dt) for a,b in zip(row,next_row,strict=True)]
            for row,next_row in zip(start,end,strict=True)]
    adj = [[m[1][1],-m[0][1]],[-m[1][0],m[0][0]]]
    det = m[0][0]*m[1][1]-m[0][1]*m[1][0]
    if det.bound()[0]<=0:
        raise ArithmeticError('frame determinant not separated from zero')
    # ||M||₂ <= sqrt(||M||₁ ||M||∞). Entries are affine in time.
    weights = [[max(abs(a),abs(b)) for a,b in zip(row,next_row,strict=True)]
               for row,next_row in zip(start,end,strict=True)]
    op = F(isqrt(max(map(sum,weights))*max(map(sum,zip(*weights))))+1,FRAME_SCALE)
    return m,rate,adj,det,op


def shifted_jump(start, jump):
    """Outward bound on ||M(start)^-1 * jump|| in trajectory dyadic units."""
    (a,b),(c,d) = start
    det = a*d-b*c
    if det<=0:
        raise ArithmeticError('singular frame at a reference jump')
    x,y = jump
    return norm_upper([F(FRAME_SCALE*(d*x-b*y),det),F(FRAME_SCALE*(a*y-c*x),det)])


def radius_in_frame(data, angles, nominal, incoming, dt, sign, trial, frame, residual, den):
    op = frame[-1]
    tube = [pilot.Model(x.a,ceil(op*trial)) for x in nominal]
    jnum,den2 = jacobian(data,angles,tube,sign)
    return linear_step_in_frame(jnum,den2,incoming,dt,frame,residual,den)


def linear_step_in_frame(jnum,den2,incoming,dt,frame,residual,den):
    """Bound v'=M^-1((J M-M')v+f) given J=jnum/den2 and f=residual/den."""
    m,rate,adj,det,_ = frame
    jm = product(jnum,m)
    centered = [[jm[i][j]-den2*rate[i][j] for j in (0,1)] for i in (0,1)]
    numerator = product(adj,centered)
    denominator = det*den2
    diagonal = max(pilot.quotient_range(numerator[i][i],denominator)[1] for i in (0,1))
    offdiag = pilot.quotient_range(numerator[1][0]+numerator[0][1],denominator.integer(2))
    mu = diagonal+max(map(abs,offdiag))
    err = []
    for a,b in adj:
        bounds = pilot.quotient_range(a*residual[0]+b*residual[1],det*den)
        err.append(max(map(abs,bounds))*pilot.SCALE)
    defect = F(norm_upper(err),pilot.SCALE)
    return pilot.radius_step(incoming,defect,mu,dt),defect


def framed_segments(data, seed, ev, init, sign, dt, count, alpha_width, origin=()):
    if sign not in (-1,1) or dt<=0 or count<=0:
        raise ValueError('positive step and count and a signed direction required')
    previous = [x.a[0] for x in seed]
    radius = norm_upper([x.e for x in seed])
    start = [[FRAME_SCALE,0],[0,FRAME_SCALE]]
    for i,nominal in enumerate(pilot.proposals(ev,init,sign,dt,count)):
        angles = pilot.angle_models(sign*(i+F(1,2))*dt,sign*dt/2,alpha_width,origin)
        radius += shifted_jump(start,[x.endpoint(-1)-y for x,y in zip(nominal,previous,strict=True)])
        val = [pilot.evaluate(g[0],nominal,angles)[0] for g in data]
        den = val[0]
        residual = []
        for x,n in zip(nominal,val[1:],strict=True):
            slope = pilot.Model([j*x.a[j] for j in range(1,len(x.a))])*pilot.Model.rational(2/dt)
            residual.append(n.integer(sign)-slope*den)
        # Midpoint estimates of the unconstrained Jacobian only propose the new frame.
        center = [pilot.Model([x.a[0]]) for x in nominal]
        at_center = [pilot.Model([x.a[0]],x.e) for x in angles]
        end = propose_frame(start,*jacobian(data,at_center,center,sign),dt)
        frame = affine_frame(start,end,dt)
        trial = max(2*radius,ceil(F(1,10**10)*pilot.SCALE))
        for _ in range(6):
            final,defect = radius_in_frame(data,angles,nominal,radius,dt,sign,trial,frame,residual,den)
            if final<trial:
                break
            trial = 2*final+2
        else:
            raise ArithmeticError(f'frame first-exit test failed at step {i}')
        op = frame[-1]
        yield pilot.MirrorSegment(i,sign,dt,alpha_width,tuple(tuple(x.a) for x in nominal),
                                  ceil(op*radius),ceil(op*final),ceil(op*trial),defect,origin)
        previous = [x.endpoint(1) for x in nominal]
        radius,start = final,end


def check_frame():
    """A shearing solution transports a round initial error to a tilted ellipse."""
    one,zero = pilot.ONE,pilot.ZERO
    data = [[{0:[[one]]},{},{}], [{0:[[one],[zero]]},{},{0:[[one]]}], [{},{},{}]]
    start = [[FRAME_SCALE,0],[0,FRAME_SCALE]]
    initial_radius = pilot.SCALE//1000
    dt = F(1,8)
    for sign in (-1,1):
        end = [[FRAME_SCALE,sign*FRAME_SCALE//8],[0,FRAME_SCALE]]
        frame = affine_frame(start,end,dt)
        final,defect = radius_in_frame(data,[one],[one,zero],initial_radius,dt,sign,
                                       2*initial_radius,frame,[zero,zero],one)
        if final>initial_radius+2 or defect>F(1,pilot.SCALE):
            raise ArithmeticError('shear should have zero growth in its variational frame')
        for x,y in ((3,4),(-4,3)):
            jump = [8*x+sign*y,8*y]
            if shifted_jump(end,jump) != 41:
                raise ArithmeticError('inverse frame did not undo exact shear')
    # A constant shear frame maps physical forcing (4,0) to (4,0) and
    # (4,3) to (1,3). Test the latter to distinguish physical and frame norms.
    shear = [[FRAME_SCALE,FRAME_SCALE],[0,FRAME_SCALE]]
    constant = affine_frame(shear,shear,dt)
    force = [pilot.Model.rational(x) for x in (4,3)]
    field = [[{0:[[one]]},{},{}]]+[[{0:[[n]]},{},{}] for n in force]
    _,defect = radius_in_frame(field,[one],[one,zero],0,dt,1,pilot.SCALE//100,constant,force,one)
    if defect != F(norm_upper([pilot.SCALE,3*pilot.SCALE]),pilot.SCALE):
        raise ArithmeticError('frame forcing is outside its transformed Euclidean bound')
    try:
        affine_frame(start,[[0,0],[0,0]],dt)
    except ArithmeticError:
        pass
    else:
        raise ArithmeticError('singular moving frame accepted')
