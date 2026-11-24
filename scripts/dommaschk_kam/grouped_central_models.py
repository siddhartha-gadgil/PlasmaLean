"""Exact interpolation and rowwise compression of the central ODE field models."""
from fractions import Fraction as F
from functools import lru_cache
from math import ceil

from bounce_mirror_pilot import Model,R0M,ZERO,angle_models
from bounce_phase_frame import affine_frame
from screen_endpoint_jacobian_sharing import native_jet
from screen_native_endpoint_residuals import sharp_budget
from screen_sparse_reference_defects import enclosing_box
from verify_grouped_mirror_exclusion import compose

DEGREE=12
NODES=tuple(F(n,4096) for n in (-4096,-3956,-3547,-2896,-2048,-1060,0,1060,2048,2896,3547,3956,4096))


@lru_cache(maxsize=1)
def basis():
    cols=[]
    for x in NODES:
        p=[F(1)]
        for y in NODES:
            if x==y:
                continue
            q=[F(0)]*(len(p)+1)
            for k,v in enumerate(p):
                q[k]-=v*y/(x-y)
                q[k+1]+=v/(x-y)
            p=q
        cols.append(p)
    return cols


def eval_at(p,x):
    value=0
    for c in reversed(p):
        value=value*x+c
    return value


def fit(rows):
    """Enclose the piecewise original polynomials on one clock, including their error radii."""
    n=len(rows)
    ys=[]
    for x in NODES:
        j=min(n-1,int((x+1)*n/2))
        ys.append(eval_at(rows[j].a,n*x+n-2*j-1))
    poly=[round(sum(y*p[k] for y,p in zip(ys,basis(),strict=True))) for k in range(DEGREE+1)]
    width=0
    for j,row in enumerate(rows):
        local=compose(poly,F(2*j+1-n,n),F(1,n))
        exact=[*row.a,*[0]*(len(poly)-len(row.a))]
        width=max(width,ceil(row.e+sum(abs(x-y) for x,y in zip(local,exact,strict=True))))
    return Model(poly,width)


def compress(m,i,start,stop):
    """Move to the original clock before charging all coefficients above degree seven."""
    local=compose(m.a,F(2*i+1-start-stop,stop-start),F(1,stop-start))
    poly=list(map(round,local[:8]))
    error=sum(abs(q-v) for q,v in zip(local[:8],poly,strict=True))+sum(map(abs,local[8:]))
    return Model(poly,m.e+ceil(error))


def coordinates(job):
    _,_,i,coords,*_=job
    r,z=map(Model,coords)
    return r,r-R0M,z,angle_models(F(2*i+1,128),F(1,128),F(0))


def boxes(forward):
    cols=[]
    for job in forward:
        r,_,z,w=coordinates(job)
        cols.append([r,z,*w])
    r,z,*waves=[fit(ms) for ms in zip(*cols,strict=True)]
    return r,r-R0M,z,waves


def horner(rows,x):
    value=rows[0]
    for row in rows[1:]:
        value=value.product(x,DEGREE)+row
    return value


def field_models(inputs):
    _,u,z,angles=inputs
    out=[]
    for p,*_ in native_jet():
        value=ZERO
        for w,rows in reversed(p.items()):
            amp=horner([horner(row,u) for row in rows],z)
            value=amp.product(angles[w],DEGREE)+value
        out.append(value)
    return out


def quotient(job,local):
    _,_,_,coords,left,right,_,count=job
    r,z=map(Model,coords)
    d,nr,nz=local
    dr,dz=[Model([128*(j+1)*v for j,v in enumerate(m.a[1:])]) for m in (r,z)]
    vr,vz=nr-dr*d,nz-dz*d
    _,_,adj,det,_=affine_frame(left,right,F(1,64))
    x,y=[a*vr+b*vz for a,b in adj]
    den=det*d
    bound=enclosing_box([x,y],den,count)
    if bound[2]<=0:
        raise ValueError('nonpositive framed denominator in the grouped residual')
    return (x,y,den),bound,sharp_budget(*bound)
