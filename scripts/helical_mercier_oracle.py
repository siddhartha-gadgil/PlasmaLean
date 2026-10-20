"""UNTRUSTED oracle: general Mercier index (Landreman-Jorge 2020 eq. 3.1) for the exact helical
equilibrium HelicalEquilibrium.eqField a (default a = 1/4), mu0 = 1 units, period ell = pi.
Usage: python helical_mercier_oracle.py [a]. Requires sympy, numpy. Output per surface psi_h = c:
(D_Merc, iota, diota/dpsi, V'', mu0 p' V'', int |Xi|^2/|grad psi|^3, X^2 / int B^2/|grad psi|^3).
Used in PlasmaLean/Design/HelicalMercier.lean (numerical finding only)."""
import sympy as sp, numpy as np, sys
a=float(sys.argv[1]) if len(sys.argv)>1 else 0.25
x,y,z=sp.symbols('x y z',real=True)
r2=x**2+y**2
P=(x**2-y**2)*sp.cos(2*z)+2*x*y*sp.sin(2*z)
psi=r2+(a+2*a/3*r2)*P
Fv=4+2*psi
K=sp.Matrix([-y,x,1]); g=sp.Matrix([sp.diff(psi,v) for v in (x,y,z)])
B=(Fv*K+g.cross(K))/(1+r2)
J=sp.Matrix([sp.diff(B[2],y)-sp.diff(B[1],z), sp.diff(B[0],z)-sp.diff(B[2],x), sp.diff(B[1],x)-sp.diff(B[0],y)])
# check force balance J x B = -4 grad psi
fb=J.cross(B)+4*g
print('fb check', [float(sp.N(e.subs({x:0.3,y:0.2,z:0.1}))) for e in fb])
f=sp.lambdify((x,y,z),[B[0],B[1],B[2],J[0],J[1],J[2],g[0],g[1],g[2]],'numpy')
ell=np.pi  # period
N=2000
th=np.linspace(0,2*np.pi,N,endpoint=False); dth=2*np.pi/N
def Iint(v): return np.sum(v)*dth
def surf(c):
    cs=np.cos(2*th); qa=2*a/3*cs; qb=1+a*cs
    R=np.where(np.abs(qa)>1e-14,(-qb+np.sqrt(qb**2+4*qa*c))/(2*qa+1e-300),c/qb)
    R=np.where(np.abs(qa)>1e-14,R,c/qb)
    r=np.sqrt(R); X=r*np.cos(th); Y=r*np.sin(th)
    psiR=qb+2*qa*R
    vals=[np.broadcast_to(np.asarray(v,dtype=float),X.shape) for v in f(X,Y,0*X)]
    return X,Y,psiR,vals
def basics(c):
    X,Y,psiR,(Bx,By,Bz,Jx,Jy,Jz,gx,gy,gz)=surf(c)
    jac=1/(2*psiR)
    phic=Iint(Bz*jac)/(2*np.pi)  # dpsi_tor/dc
    Vc=ell*Iint(jac)
    Ic=Iint(Jz*jac)/(2*np.pi)
    # iota: field line in helical frame: du/dz = (dtheta/dz)-1 ; T = ∮ du/(du/dz)
    r2v=X**2+Y**2
    Bth=(-Y*Bx+X*By)/np.sqrt(r2v)
    dthdz=Bth/(np.sqrt(r2v)*Bz)
    T=Iint(1/(dthdz-1))
    iota=ell/(2*np.pi)*(1+2*np.pi/T)
    return phic,Vc,Ic,iota
def D(c):
    h=c*1e-3
    m=basics(c-h); o=basics(c); p=basics(c+h)
    psic=o[0]
    iotap=(p[3]-m[3])/(2*h)/psic
    Vpp=(p[1]/p[0]-m[1]/m[0])/(2*h)/psic
    Ip=o[2]/psic
    mpp=-4/psic
    X_,Y_,psiR,(Bx,By,Bz,Jx,Jy,Jz,gx,gy,gz)=surf(c)
    B2=Bx**2+By**2+Bz**2; JB=Jx*Bx+Jy*By+Jz*Bz; J2=Jx**2+Jy**2+Jz**2
    gpsi2=(gx**2+gy**2+gz**2)*psic**2
    # dS/|grad psi|^3 = (dS/|grad c|) / (psic^3 |grad c|^2), dS/|grad c| = ell dth/(2 psiR); gpsi2 = psic^2 |grad c|^2
    w=ell/(2*psiR)/(gpsi2*psic)
    BXi=JB-Ip*B2; Xi2=J2-2*Ip*JB+Ip**2*B2
    Xv=2*np.pi**2*iotap-Iint(w*BXi)
    IB2=Iint(w*B2)
    Dm=(Xv**2+(mpp*Vpp-Iint(w*Xi2))*IB2)/(2*np.pi)**6
    return Dm, o[3], iotap, Vpp, mpp*Vpp, Iint(w*Xi2), Xv**2/IB2
for c in [1e-3,0.01,0.03,0.05,0.08]:
    print(c, D(c))
if a==0:
    # check against the exact Lean value mercierIndex_cylinder = -1/(1024 pi^2 r^2) (ell = pi, mu0 = 1)
    for c in [1e-3,0.01,0.08]:
        exact=-1/(1024*np.pi**2*c); num=D(c)[0]
        print('a=0 check', c, num, exact); assert abs(num-exact)<1e-6*abs(exact)
