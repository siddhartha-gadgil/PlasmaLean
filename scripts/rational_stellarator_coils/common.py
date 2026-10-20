import numpy as np
def r2f(x): return x[...,0]**2+x[...,1]**2
def hel(x):
    """helical part (1/16) grad H of field(1/4) (exact formulas of RationalStellarator.lean)."""
    X,Y,Z=x[...,0],x[...,1],x[...,2]
    r2=X*X+Y*Y; w=1/r2
    Aq=(r2-1)**2-4*Z**2; Bq=(r2-1)*(r2-5)-4*Z**2; Xd=X*X-Y*Y; Yp=2*X*Y*Z
    Hnum=Aq*Xd-Bq*Yp
    H0=4*X*(r2-1)*Xd+2*X*Aq-4*X*(r2-3)*Yp-2*Y*Z*Bq
    H1=4*Y*(r2-1)*Xd-2*Y*Aq-4*Y*(r2-3)*Yp-2*X*Z*Bq
    H2=-8*Z*Xd+8*Z*Yp-2*X*Y*Bq
    G0=H0*w**2-4*X*Hnum*w**3
    G1=H1*w**2-4*Y*Hnum*w**3
    G2=H2*w**2
    return np.stack([G0,G1,G2],-1)/16
def frontier_pts(a,n_phi,n_side):
    """points on the four faces of {|s|<=a,|z|<=a}, s=(r2-1)/2."""
    ph=np.linspace(0,2*np.pi,n_phi,endpoint=False)
    u=np.linspace(-a,a,n_side)
    pts=[]
    for sv in (-a,a):
        R=np.sqrt(1+2*sv)
        P,U=np.meshgrid(ph,u,indexing='ij')
        pts.append(np.stack([R*np.cos(P),R*np.sin(P),U],-1).reshape(-1,3))
    for zv in (-a,a):
        P,U=np.meshgrid(ph,u,indexing='ij')
        R=np.sqrt(1+2*U)
        pts.append(np.stack([R*np.cos(P),R*np.sin(P),zv+0*U],-1).reshape(-1,3))
    return np.concatenate(pts)
def biot_polyline(pts_loop,I,x,chunk=4000):
    """field (mu0=1) of closed polygon pts_loop (M,3) current I at points x (P,3); exact segment formula."""
    A=pts_loop; Bv=np.roll(pts_loop,-1,axis=0)
    out=np.zeros_like(x)
    for i0 in range(0,len(x),chunk):
        xx=x[i0:i0+chunk][:,None,:]
        a=A[None,:,:]-xx; b=Bv[None,:,:]-xx
        na=np.linalg.norm(a,axis=-1); nb=np.linalg.norm(b,axis=-1)
        cr=np.cross(a,b)
        den=na*nb*(na*nb+np.sum(a*b,-1))
        f=(na+nb)/den
        out[i0:i0+chunk]=I/(4*np.pi)*np.sum(cr*f[...,None],axis=1)
    return out
