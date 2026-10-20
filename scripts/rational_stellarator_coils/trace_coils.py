import numpy as np, sys, pickle
from common import *
def load_phi(fn):
    d=pickle.load(open(fn,'rb'))
    keep=[(lab,cc) for lab,cc in zip(d['modes'],d['c']) if abs(cc)>1e-10]
    return d['aw'],keep
def mk(keep):
    def Phi(t,p):
        out=0*np.asarray(t,float)
        for (m,n,kind),cc in keep:
            arg=m*t-n*p
            out=out+cc*(np.sin(arg) if kind=='sin' else np.cos(arg))
        return out
    def grad(t,p):
        gt=0*np.asarray(t,float); gp=0*np.asarray(t,float)
        for (m,n,kind),cc in keep:
            arg=m*t-n*p
            if kind=='sin': gt=gt+cc*m*np.cos(arg); gp=gp-cc*n*np.cos(arg)
            else: gt=gt-cc*m*np.sin(arg); gp=gp+cc*n*np.sin(arg)
        return gt,gp
    return Phi,grad
def wrap(d): return (d+np.pi)%(2*np.pi)-np.pi
def trace(Phi,grad,lev,t0,p0,ds=0.004,maxn=200000):
    pts=[(t0,p0)]; t,p=t0,p0
    def f(t,p):
        gt,gp=grad(t,p); g=np.hypot(gt,gp)
        return -gp/g, gt/g
    left=False
    for k in range(maxn):
        k1=f(t,p); k2=f(t+ds/2*k1[0],p+ds/2*k1[1]); k3=f(t+ds/2*k2[0],p+ds/2*k2[1]); k4=f(t+ds*k3[0],p+ds*k3[1])
        t+=ds/6*(k1[0]+2*k2[0]+2*k3[0]+k4[0]); p+=ds/6*(k1[1]+2*k2[1]+2*k3[1]+k4[1])
        for _ in range(2):
            gt,gp=grad(t,p); r=Phi(t,p)-lev; g2=gt*gt+gp*gp
            t-=r*gt/g2; p-=r*gp/g2
        pts.append((t,p))
        dist=np.hypot(wrap(t-t0),wrap(p-p0))
        if dist>5*ds: left=True
        if left and dist<1.5*ds:
            break
    else:
        raise RuntimeError('no closure')
    pts=np.array(pts[:-1])
    return pts
def all_loops(Phi,grad,Nc,ds=0.004,nseed=64):
    tg=np.linspace(0,2*np.pi,400,endpoint=False); pg=np.linspace(0,2*np.pi,400,endpoint=False)
    TG,PG=np.meshgrid(tg,pg,indexing='ij'); F=Phi(TG,PG)
    fmin,fmax=F.min(),F.max(); dF=(fmax-fmin)/Nc
    levels=fmin+(np.arange(Nc)+0.5)*dF
    loops=[]
    seeds_lines=[('p',pv) for pv in np.linspace(0,2*np.pi,nseed,endpoint=False)]+[('t',tv) for tv in np.linspace(0,2*np.pi,nseed,endpoint=False)]
    for lev in levels:
        mine=[]
        for kind,v in seeds_lines:
            s=np.linspace(0,2*np.pi,2001)
            if kind=='p': vals=Phi(s,v+0*s)
            else: vals=Phi(v+0*s,s)
            sc=np.where(np.sign(vals[:-1]-lev)!=np.sign(vals[1:]-lev))[0]
            for i in sc:
                a,b=s[i],s[i+1]
                for _ in range(50):
                    m=(a+b)/2
                    vm=Phi(m,v) if kind=='p' else Phi(v,m)
                    va=Phi(a,v) if kind=='p' else Phi(v,a)
                    if np.sign(vm-lev)==np.sign(va-lev): a=m
                    else: b=m
                t0,p0=((a+b)/2,v) if kind=='p' else (v,(a+b)/2)
                # already on a loop of this level?
                on=False
                for L in mine:
                    if np.min(np.hypot(wrap(L[:,0]-t0),wrap(L[:,1]-p0)))<3*ds: on=True;break
                if on: continue
                L=trace(Phi,grad,lev,t0,p0,ds)
                mine.append(L)
        for L in mine: loops.append((lev,L))
    return loops,dF
if __name__=="__main__":
    aw,keep=load_phi(sys.argv[1]); Nc=int(sys.argv[2])
    Phi,grad=mk(keep)
    loops,dF=all_loops(Phi,grad,Nc)
    P=frontier_pts(0.105,256,17); tgt=hel(P)
    B=np.zeros_like(P); coils=[]
    for lev,L in loops:
        t,p=L[:,0],L[:,1]
        R=1+aw*np.cos(t)
        xyz=np.stack([R*np.cos(p),R*np.sin(p),aw*np.sin(t)],-1)
        # current direction: K dA = (Phi_t x_p - Phi_p x_t); the tracer moves along (dt,dp)=(-Phi_p,Phi_t)
        # whose surface tangent is -Phi_p x_t + Phi_t x_p = K direction: so sign +1.
        B+=biot_polyline(xyz,dF,P); coils.append((dF,xyz))
    e=np.linalg.norm(B-tgt,axis=1)
    print('Nc',Nc,'loops',len(loops),'max err',e.max(),'rms',np.sqrt((e**2).mean()),'pts',sum(len(x) for _,x in coils),flush=True)
    pickle.dump(coils,open(f'tcoils_{aw}_{Nc}.pkl','wb'))
