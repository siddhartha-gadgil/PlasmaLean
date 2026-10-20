import sys
from base import *
from lines import line_field
from scipy.optimize import least_squares
rng=np.random.default_rng(1)
n=1500
s=rng.uniform(-.1,.1,n); z=rng.uniform(-.1,.1,n); ph=rng.uniform(0,2*np.pi,n)
X=tor_pts(s,z,ph); target=0.25*gradh(X)
rot=np.diag([-1,-1,1.]); sig=np.array([[0,1,0],[1,0,0],[0,0,-1.]])
def group(p,u):
    return [(p,u,1),(rot@p,rot@u,1),(sig@p,sig@u,-1),(rot@sig@p,rot@sig@u,-1)]
def unpack(v,K):
    out=[]
    for k in range(K):
        q=v[5*k:5*k+5]
        p=q[:3]; th,ph_=q[3],q[4]
        u=np.array([np.sin(th)*np.cos(ph_),np.sin(th)*np.sin(ph_),np.cos(th)])
        out.append((p,u))
    return out
def linedist(p,u):
    t=np.linspace(-4,4,801); pts=p+t[:,None]*u
    R=np.hypot(pts[:,0],pts[:,1]); ss=(R**2-1)/2
    d=np.maximum(np.abs(ss)-0.1,np.abs(pts[:,2])-0.1)
    return d.min()
def cols(v,K):
    C=[]
    for p,u in unpack(v,K):
        f=sum(sg*line_field(X,pp,uu) for pp,uu,sg in group(p,u))
        C.append(f.reshape(-1))
    return np.stack(C,1)
dmin=float(sys.argv[2]) if len(sys.argv)>2 else 0.1
def res(v,K):
    A=cols(v,K); c,*_=np.linalg.lstsq(A,target.reshape(-1),rcond=None)
    r=A@c-target.reshape(-1)
    pen=[max(0,dmin-linedist(p,u))*10 for p,u in unpack(v,K)]
    return np.concatenate([r,pen])
K=int(sys.argv[1])
best=None
for trial in range(6):
    v=[]
    for k in range(K):
        a=rng.uniform(0,2*np.pi)
        if rng.uniform()<0.5: rho=rng.uniform(0,0.6)
        else: rho=rng.uniform(1.4,2.0)
        v+= [rho*np.cos(a),rho*np.sin(a),rng.uniform(-.5,.5),rng.uniform(0,np.pi),rng.uniform(0,2*np.pi)]
    sol=least_squares(res,np.array(v),args=(K,),max_nfev=400)
    A=cols(sol.x,K); c,*_=np.linalg.lstsq(A,target.reshape(-1),rcond=None)
    e=np.linalg.norm((A@c-target.reshape(-1)).reshape(-1,3),axis=1).max()
    print(trial,e,[round(linedist(p,u),3) for p,u in unpack(sol.x,K)],flush=True)
    if best is None or e<best[0]: best=(e,sol.x,c)
np.save(f'nl_K{K}.npy',np.concatenate([best[1],best[2]]))
