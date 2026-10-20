"""UNTRUSTED helpers: parse the certified first integral P from the Lean data file, the field
field(1/4) (numerical gradient of h) and torus coordinates."""
import re, os, numpy as np
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','PlasmaLean','Design','RationalStellaratorConfinedData.lean')).read()
def fpoly(name):
    m=re.search(r'def '+name+r' : FPoly :=\s*fpoly% "([^"]*)"',src,re.S)
    rows=[r.split() for r in m.group(1).replace('\n',' ').split(';') if r.strip()]
    return [(int(r[0]),tuple(map(int,r[1:]))) for r in rows]
P=fpoly('Pz')
SC=2.0**40
def W(x):
    X,Y,Z=x[...,0],x[...,1],x[...,2]
    r2=X*X+Y*Y
    return (r2-1)/2, Z, (X*X-Y*Y)/r2, 2*X*Y/r2
def evalP(p,w):
    out=0
    for c,e in p:
        t=c
        for wi,ei in zip(w,e):
            if ei: t=t*wi**ei
        out=out+t
    return out
def dP(p,i):
    return [(c*e[i],tuple(ei-(j==i) for j,ei in enumerate(e))) for c,e in p if e[i]>0]
dPs=[dP(P,i) for i in range(4)]
def Ival(x): return evalP(P,W(x))
def DI(x):
    X,Y,Z=x[...,0],x[...,1],x[...,2]
    r2=X*X+Y*Y
    w=W(x)
    s,z,C,S=w
    # gradients of s,z,C,S
    gs=np.stack([X,Y,0*X],-1)
    gz=np.stack([0*X,0*X,1+0*X],-1)
    # C=cos2phi, grad = -2 sin2phi grad phi, grad phi=(-Y,X,0)/r2
    gphi=np.stack([-Y/r2,X/r2,0*X],-1)
    gC=(-2*S)[...,None]*gphi
    gS=(2*C)[...,None]*gphi
    g=sum(evalP(dPs[i],w)[...,None]*gg for i,gg in enumerate([gs,gz,gC,gS]))
    return g
def Hnum_grad(x):
    X,Y,Z=x[...,0],x[...,1],x[...,2]
    pass
def field(x,eps=0.25):
    # numeric gradient of h=H/4 analytically via sympy-free formula
    X,Y,Z=x[...,0],x[...,1],x[...,2]
    r2=X*X+Y*Y
    tor=np.stack([-Y/r2,X/r2,0*X],-1)
    return tor+eps*gradh(x)
def h(x):
    X,Y,Z=x[...,0],x[...,1],x[...,2]
    r2=X*X+Y*Y
    Aq=(r2-1)**2-4*Z**2; Bq=(r2-1)*(r2-5)-4*Z**2
    return (Aq*(X*X-Y*Y)-Bq*2*X*Y*Z)/r2**2/4
def gradh(x,d=1e-6):
    out=[]
    for k in range(3):
        e=np.zeros(3); e[k]=d
        out.append((h(x+e)-h(x-e))/(2*d))
    return np.stack(out,-1)
def tor_pts(s,z,phi):
    R=np.sqrt(1+2*s)
    return np.stack([R*np.cos(phi),R*np.sin(phi),z+0*phi],-1)
