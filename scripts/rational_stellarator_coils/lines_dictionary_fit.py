from base import *
from lines import line_field
import itertools
rng=np.random.default_rng(0)
# sample points in T
n=4000
s=rng.uniform(-.1,.1,n); z=rng.uniform(-.1,.1,n); ph=rng.uniform(0,2*np.pi,n)
X=tor_pts(s,z,ph)
target=0.25*gradh(X)
def dist_T_ok(p,u):
    # min distance from line to tube T approx via sampling on line
    t=np.linspace(-5,5,4001)
    pts=p+t[:,None]*u
    R=np.hypot(pts[:,0],pts[:,1]); ss=(R**2-1)/2
    d=np.maximum(np.abs(ss)-0.1,np.abs(pts[:,2])-0.1)
    return d.min()
lines=[]
# vertical lines
for rho in [0.4,0.55,0.65,1.35,1.5,1.8]:
    for a in np.linspace(0,2*np.pi,24,endpoint=False):
        lines.append((np.array([rho*np.cos(a),rho*np.sin(a),0]),np.array([0,0,1.])))
# tilted lines through hole
for rho in [0.0,0.3,0.5]:
    for a in np.linspace(0,2*np.pi,12,endpoint=False):
        for th in [0.3,0.6]:
            for b in np.linspace(0,2*np.pi,8,endpoint=False):
                u=np.array([np.sin(th)*np.cos(b),np.sin(th)*np.sin(b),np.cos(th)])
                lines.append((np.array([rho*np.cos(a),rho*np.sin(a),0]),u))
# horizontal lines above/below
for z0 in [0.35,-0.35,0.6,-0.6]:
    for b in np.linspace(0,np.pi,12,endpoint=False):
        for off in np.linspace(-1.5,1.5,7):
            u=np.array([np.cos(b),np.sin(b),0]); nrm=np.array([-np.sin(b),np.cos(b),0])
            lines.append((off*nrm+np.array([0,0,z0]),u))
good=[(p,u) for p,u in lines if dist_T_ok(p,u)>0.12]
print(len(lines),len(good))
A=np.stack([line_field(X,p,u).reshape(-1) for p,u in good],1)
b=target.reshape(-1)
for lam in [1e-8,1e-6,1e-4,1e-2]:
    M=A.T@A+lam*np.eye(A.shape[1]); c=np.linalg.solve(M,A.T@b)
    r=(A@c-b).reshape(-1,3); print(lam, np.linalg.norm(r,axis=1).max(), np.abs(c).sum(), np.abs(c).max())
