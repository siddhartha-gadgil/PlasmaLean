"""N-42: does the cylindrical window of the source (section 6.3) survive a far wall?
Same F_mn as check_cylinder_hotcore.py; a = B_i = 1; untrusted floats."""
import mpmath as mp
mp.mp.dps = 20

def Ip(m, x):
    """I_m'(x) by the recurrence."""
    return (mp.besseli(m - 1, x) + mp.besseli(m + 1, x))/2
def Kp(m, x):
    """K_m'(x) by the recurrence (mpmath's besselk ignores its derivative keyword)."""
    return -(mp.besselk(m - 1, x) + mp.besselk(m + 1, x))/2
def nout(m, k, h):
    m = abs(m)
    if k == 0:
        return mp.coth(m*mp.log(h))/m if h != mp.inf else mp.mpf(1)/m
    k = abs(k)
    if h == mp.inf:
        return -mp.besselk(m, k)/(k*Kp(m, k))
    A = -Kp(m, k*h); B = Ip(m, k*h)
    phi = A*mp.besseli(m, k) + B*mp.besselk(m, k)
    dphi = k*(A*Ip(m, k) + B*Kp(m, k))
    return -phi/dphi
def F(m, k, h, Be, Bt):
    pl = 0 if k == 0 else abs(k)*mp.besseli(abs(m), abs(k))/Ip(abs(m), abs(k))
    return pl + (k*Be + m*Bt)**2*nout(m, k, h) - Bt**2
s = mp.mpf('0.16107'); Be = mp.sqrt(1 - 3*s/4); Bt = mp.sqrt(s)
for h in [1 + s/16, mp.mpf('1.05'), mp.mpf('1.1'), mp.mpf('1.2'), mp.mpf(2), mp.inf]:
    best = (mp.inf, None)
    for m in range(1, 6):
        for j in range(-200, 201):
            k = mp.mpf(j)/50
            f = F(m, k, h, Be, Bt)
            if f < best[0]: best = (f, (m, float(k)))
    print('h=%s  min_{m>=1} F = %.6f at (m,k)=%s   (s^2/8 = %.6f)' % (h, best[0], best[1], s**2/8))
