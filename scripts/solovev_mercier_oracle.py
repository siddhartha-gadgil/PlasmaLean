"""UNTRUSTED oracle: general Mercier index (Landreman-Jorge 2020 eq. 3.1) for the reactor Solov'ev
equilibrium (A = 7/4 T, L = 10 m, F = 50 T m), using the exact surface parametrization
u = R^2 = L^2 + 2 sqrt(c) sin t, z = sqrt(2c) cos t / R and dl/|grad psiT| = dt/(sqrt 2 u).
Output per surface psiT = c: (D_Merc, D_Shear, q, V''), then (mu0 p' V'', int|Xi|^2/|grad psi|^3, int(perp part)).
Used in PlasmaLean/Design/SolovevMercier.lean (numerical finding only)."""
import numpy as np
A=7/4; L=10.; F=50.
N=4000
t=np.linspace(-np.pi,np.pi,N,endpoint=False); dt=2*np.pi/N
def I(f): return np.sum(f)*dt
def geo(c):
    s=np.sqrt(c); u=L**2+2*s*np.sin(t); R=np.sqrt(u); z=np.sqrt(2)*s*np.cos(t)/R
    g2=4*s**2*(s*np.cos(t)**2+u*np.sin(t))**2/u+2*s**2*np.cos(t)**2*u
    return s,u,R,z,g2
def basics(c):
    s,u,R,z,g2=geo(c)
    psic=F/(2*np.pi)*I(u**-1.5)/np.sqrt(2)
    Vc=np.sqrt(2)*np.pi*I(u**-0.5)
    Ic=(3*A/L**2)*I(u**-0.5)/np.sqrt(2)/(2*np.pi)
    return psic,Vc,Ic
def D(c,h=None):
    h=h or c*1e-3
    pm,Vm,Im=basics(c-h); p0,V0,I0=basics(c); pp,Vp,Ip=basics(c+h)
    psic=p0
    q=lambda pc: pc/(A/L**2)
    iotap=((1/q(pp))-(1/q(pm)))/(2*h)/psic
    Vpp=((Vp/pp)-(Vm/pm))/(2*h)/psic
    Iprime=I0/psic
    mu0pp=-3*A**2/L**4/psic
    s,u,R,z,g2=geo(c)
    B2=F**2/u+(A/L**2)**2*g2/u
    JB=3*A*F/L**2
    J2=9*A**2*u/L**4
    w=2*np.pi*R/(np.sqrt(2)*u)/(psic**3*g2)
    BXi=JB-Iprime*B2
    Xi2=J2-2*Iprime*JB+Iprime**2*B2
    X=2*np.pi**2*iotap-I(w*BXi)
    IB2=I(w*B2)
    D=(X**2+(mu0pp*Vpp-I(w*Xi2))*IB2)/(2*np.pi)**6
    Dshear=iotap**2/(16*np.pi**2)
    return D,Dshear,q(psic),Vpp
for c in [1,5,25,100,200,400,625]:
    print(c, D(c))
print("well vs Xi2")
def parts(c,h=None):
    h=h or c*1e-3
    pm,Vm,Im=basics(c-h); p0,V0,I0=basics(c); pp,Vp,Ip=basics(c+h)
    psic=p0
    Vpp=((Vp/pp)-(Vm/pm))/(2*h)/psic
    Iprime=I0/psic
    mu0pp=-3*A**2/L**4/psic
    s,u,R,z,g2=geo(c)
    B2=F**2/u+(A/L**2)**2*g2/u
    JB=3*A*F/L**2; J2=9*A**2*u/L**4
    w=2*np.pi*R/(np.sqrt(2)*u)/(psic**3*g2)
    Xi2=J2-2*Iprime*JB+Iprime**2*B2
    perp=mu0pp**2*g2*psic**2/B2
    return mu0pp*Vpp, I(w*Xi2), I(w*perp)
for c in [1,25,100,400,625]: print(c,parts(c))
