import numpy as np, sys, pickle, time
from common import *
aw=float(sys.argv[1]); M=int(sys.argv[2]); Nn=int(sys.argv[3]); lam=float(sys.argv[4])
a=0.105
nt,npf=72,144
th=np.linspace(0,2*np.pi,nt,endpoint=False); ph=np.linspace(0,2*np.pi,npf,endpoint=False)
TH,PH=np.meshgrid(th,ph,indexing='ij')
Rw=1+aw*np.cos(TH)
Xs=np.stack([Rw*np.cos(PH),Rw*np.sin(PH),aw*np.sin(TH)],-1)
Xt=np.stack([-aw*np.sin(TH)*np.cos(PH),-aw*np.sin(TH)*np.sin(PH),aw*np.cos(TH)],-1)
Xp=np.stack([-Rw*np.sin(PH),Rw*np.cos(PH),0*TH],-1)
dA=(2*np.pi/nt)*(2*np.pi/npf)
P=frontier_pts(a,64,9)
tgt=hel(P)
Y=Xs.reshape(-1,3)
def Bfield(Kdl,x):
    # Kdl: (G,3) current element per grid cell (already times dtheta dphi)
    out=np.zeros_like(x)
    for i0 in range(0,len(x),256):
        d=x[i0:i0+256,None,:]-Y[None]
        r3=np.linalg.norm(d,axis=-1)**3
        out[i0:i0+256]=np.sum(np.cross(Kdl[None],d)/r3[...,None],axis=1)/(4*np.pi)
    return out
modes=[(m,n) for m in range(0,M+1) for n in range(-Nn,Nn+1,2) if not (m==0 and n<=0)]
cols=[];labels=[]
t0=time.time()
for (m,n) in modes:
    for kind in ('sin','cos'):
        arg=m*TH-n*PH
        if kind=='sin': Ft=m*np.cos(arg); Fp=-n*np.cos(arg)
        else: Ft=-m*np.sin(arg); Fp=n*np.sin(arg)
        Kdl=(Ft[...,None]*Xp-Fp[...,None]*Xt)*dA
        cols.append(Bfield(Kdl.reshape(-1,3),P).reshape(-1)); labels.append((m,n,kind))
A=np.stack(cols,1); b=tgt.reshape(-1)
print('build',time.time()-t0,A.shape,flush=True)
c=np.linalg.solve(A.T@A+lam*np.eye(A.shape[1]),A.T@b)
r=(A@c-b).reshape(-1,3); e=np.linalg.norm(r,axis=1)
print('aw',aw,'M',M,'Nn',Nn,'lam',lam,'max err',e.max(),'rms',np.sqrt((e**2).mean()),'max tgt',np.linalg.norm(tgt,axis=1).max())
big=sorted(zip(np.abs(c),labels),reverse=True)[:12]; print(big)
pickle.dump(dict(aw=aw,modes=labels,c=c),open(f'cp_{aw}_{M}_{Nn}.pkl','wb'))
