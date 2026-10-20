"""UNTRUSTED oracle for PlasmaLean/Design/SolovevBallooning.lean (not part of the trusted base).

Proposes the two-variable Riccati certificate F = s*a + f0 + f1*w^2/(w^2+s^2) + f2*w*s/(w^2+s^2)
(f0 = x*A0(y), f1 = x*A1(y), f2 = A2(y), a = a0 - 75/(s|B|^2)) for the reactor Solov'ev surface
psiT = s^2 by maximizing the margin of  Q - dF/dt - d*dF/dsigma - F^2/P >= m  on a (t, chi) grid
(sigma = w tan chi) with a convex SOCP (cvxpy/Clarabel). Coefficients were then rounded to multiples
of 2^-16; every claim is re-checked in Lean by kernel-evaluated interval arithmetic.
Usage: python solovev_ballooning_oracle.py s w K Nt Nchi   (used: K=2, Nt=256, Nchi=61;
w = 2, 1, 0.7, 0.5 for s = 1, 2, 3, 4). Writes cert3_s<s>.json.
"""
import numpy as np, math, sys, cvxpy as cp, json
A=7/4; L=10.; F=50.; c=A/L**2; r2=math.sqrt(2); rate=F*L**2/(r2*A)
def base(s,x,y):
    """component-formula coefficient functions at (x,y) on circle"""
    u=L**2+2*s*y; R=np.sqrt(u); z=r2*s*x/R; W=z*z+R*R-L**2
    BR,BP,BZ=-c*R*z, F/R, c*W
    gsR,gsZ=R*W/(2*s), R*R*z/(2*s)
    gtR,gtZ=x*(L**2+s*y)/(s*R), -R*y/(r2*s)
    Phit=-rate/R**3
    kR,kP,kZ=-Phit*gtR, 1/R, -Phit*gtZ
    ell=L**2/(r2*A*R)
    gpR,gpZ=-3*c*c*R*W, -3*c*c*R*R*z
    GR=c*c*R*z*z-F**2/R**3-c*c*R*W; GZ=-2*c*c*R*R*z+2*c*c*z*W
    B2=BR**2+BP**2+BZ**2
    p0=(kR**2+kP**2+kZ**2)/(ell*B2)
    p1=-2*(kR*gsR+kZ*gsZ)/(ell*B2)
    p2=(gsR**2+gsZ**2)/(ell*B2)
    # triple a x b . c with a=B, b=k0 or gs, c = gp or G ; phi comp of gp,G zero
    def trip(b, cc):
        bR,bP,bZ=b; cR,cZ=cc
        # (B x b)_R = BP*bZ - BZ*bP ; (B x b)_Z = BR*bP - BP*bR
        return (BP*bZ-BZ*bP)*cR + (BR*bP-BP*bR)*cZ
    Bk0gp=trip((kR,kP,kZ),(gpR,gpZ)); Bk0G=trip((kR,kP,kZ),(GR,GZ)); BgsG=trip((gsR,0,gsZ),(GR,GZ))
    q0=-2*ell*Bk0gp*Bk0G/B2**3
    q1=2*ell*Bk0gp*BgsG/B2**3
    d=3*rate*y/R**5
    acore=-1.5*F/(s*B2)
    return dict(p0=p0,p1=p1,p2=p2,q0=q0,q1=q1,d=d,acore=acore,B2=B2,R=R)

s=float(sys.argv[1]); w=float(sys.argv[2]); K=int(sys.argv[3])
Nt=int(sys.argv[4]); Nc=int(sys.argv[5])
ts=np.linspace(0,2*np.pi,Nt,endpoint=False); x=np.cos(ts); y=np.sin(ts)
b=base(s,x,y)
# f0 = x*A0(y), f1 = x*A1(y), f2 = A2(y)
Xb=np.array([x*y**k for k in range(K+1)]).T
dXb=np.array([-y**(k+1)+(k*(1-y**2)*y**(k-1) if k>0 else 0) for k in range(K+1)]).T
Yb=np.array([y**k for k in range(K+1)]).T
dYb=np.array([(k*y**(k-1)*x if k>0 else 0*y) for k in range(K+1)]).T
c0=cp.Variable(K+1); c1=cp.Variable(K+1); c2=cp.Variable(K+1); a0=cp.Variable(); m=cp.Variable()
a=a0+b['acore']
f0=Xb@c0; f1=Xb@c1; f2=Yb@c2; df0=dXb@c0; df1=dXb@c1; df2=dYb@c2
chis=np.linspace(-np.pi/2,np.pi/2,Nc)[1:-1]
cons=[]
for ch in chis:
    sg=w*math.tan(ch); D=w*w+sg*sg
    rho=w*w/D; nu=w*sg/D; drho=-2*sg*w*w/D**2; dnu=w*(w*w-sg*sg)/D**2
    P=b['p0']+sg*b['p1']+sg**2*b['p2']
    Fv=sg*a+f0+rho*f1+nu*f2
    E=b['q0']-df0-rho*df1-nu*df2-cp.multiply(b['d'],a+drho*f1+dnu*f2)
    cons.append(E-cp.multiply(1/P,cp.square(Fv))>=m)
cons.append(b['q0']-df0-cp.multiply(b['d'],a)-cp.multiply(1/b['p2'],cp.square(a))>=m)
prob=cp.Problem(cp.Maximize(m),cons+[cp.abs(c0)<=50,cp.abs(c1)<=50,cp.abs(c2)<=50,cp.abs(a0)<=100])
prob.solve(solver=cp.CLARABEL)
print("status",prob.status,"margin",m.value,"a0",a0.value)
Z=[0.0]*(K+1)
json.dump(dict(s=s,w=w,K=K,a0=float(a0.value),Pa=[Z,Z,c2.value.tolist()],Pb=[c0.value.tolist(),c1.value.tolist(),Z],margin=float(m.value)),open(f"cert3_s{s}.json","w"))
