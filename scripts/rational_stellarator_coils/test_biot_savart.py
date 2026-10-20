from common import *
# check: long straight wire approx -> 1/(2 pi rho)
L=1e4
loop=np.array([[0,0,-L],[0,0,L],[L,0,L],[L,0,-L]],float)
x=np.array([[1.0,0,0]])
print(biot_polyline(loop,2*np.pi,x))  # expect ~ (0,1,0) minus return ~1/L
# check helper hel vs numeric gradient of h
def h(x):
    X,Y,Z=x[...,0],x[...,1],x[...,2]; r2=X*X+Y*Y
    Aq=(r2-1)**2-4*Z**2; Bq=(r2-1)*(r2-5)-4*Z**2
    return (Aq*(X*X-Y*Y)-Bq*2*X*Y*Z)/r2**2/16
p=np.array([[1.05,0.2,0.04]]); d=1e-6
print(hel(p), [(h(p+d*e)-h(p-d*e))/(2*d) for e in np.eye(3)])
