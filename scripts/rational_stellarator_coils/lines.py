from base import *
def line_field(x,p,u):
    # infinite line through p, direction u (unit), unit "current" normalization: field = u x w_perp / |w_perp|^2 (i.e. mu0 I/(2pi)=1)
    u=np.asarray(u,float); u=u/np.linalg.norm(u)
    w=x-p
    wp=w-(w@u)[...,None]*u
    return np.cross(u,wp)/np.sum(wp*wp,-1)[...,None]
# check z-axis gives toroidal field
x=tor_pts(np.array([0.05]),np.array([0.02]),np.array([0.3]))
print(line_field(x,np.zeros(3),[0,0,1]), field(x,0))
