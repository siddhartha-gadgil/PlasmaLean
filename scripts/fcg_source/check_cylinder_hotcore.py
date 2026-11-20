"""Independent numerical checks (N-42, untrusted floats at 30 digits) of the cylindrical ideal-MHD
window (section 6) and the hot-core constants (section 9.2) of
sources/fusion_complex_geometry_and_stability.pdf. Normalisation a = 1, B_i = 1."""
import mpmath as mp
mp.mp.dps = 30

def Ip(m, x):
    """I_m'(x) by the recurrence."""
    return (mp.besseli(m - 1, x) + mp.besseli(m + 1, x))/2
def Kp(m, x):
    """K_m'(x) by the recurrence (mpmath's besselk ignores its derivative keyword)."""
    return -(mp.besselk(m - 1, x) + mp.besselk(m + 1, x))/2

def nout(m, k, h):
    m = abs(m)
    if k == 0:
        return mp.coth(m*mp.log(h))/m
    k = abs(k)
    # phi = A I_m(k r) + B K_m(k r), phi'(h) = 0
    A = -Kp(m, k*h); B = Ip(m, k*h)
    phi = A*mp.besseli(m, k) + B*mp.besselk(m, k)
    dphi = k*(A*Ip(m, k) + B*Kp(m, k))
    return -phi/dphi

def F(m, k, s, h, Be, Bt):
    kap = abs(k)
    if k == 0:
        plasma = 0
    else:
        mm = abs(m)
        plasma = kap*mp.besseli(mm, kap)/Ip(mm, kap)
    if m == 0 and k == 0:
        return None
    return plasma + (k*Be + m*Bt)**2*nout(m, k, h) - Bt**2

# k = 0 impedance formula vs a direct annulus computation is the closed form itself; check the
# k -> 0 limit of the Bessel impedance agrees with coth formula
print('k->0 impedance limit (m=2,h=1.01):', nout(2, mp.mpf('1e-8'), mp.mpf('1.01')), nout(2, 0, mp.mpf('1.01')))
worst = []
for s in [mp.mpf('0.01'), mp.mpf('0.05'), mp.mpf('0.16107'), mp.mpf('0.25')]:
    h = 1 + s/16
    Be = mp.sqrt(1 - 3*s/4); Bt = mp.sqrt(s)
    ell = mp.log(h); D = (h**2 - 1)/2
    assert ell + s*D/Be**2 <= s/8
    mn = mp.inf; mnr = mp.inf
    for m in range(-10, 11):
        for kk in [mp.mpf(j)/20 for j in range(-400, 401)]:
            if m == 0 and kk == 0: continue
            f = F(m, kk, s, h, Be, Bt)
            mn = min(mn, f/(s**2/8)) if m != 0 else mn
            mnr = min(mnr, f/(s**2/80*(1 + abs(m) + abs(kk))))
    worst.append((float(s), float(mn), float(mnr)))
print('min F/(s^2/8) over m!=0, and min F/(s^2/80 (1+|m|+kappa)) over grid:')
for w in worst: print('  s=%.5f  %.4f  %.4f' % w)
# unstable branch
Bi, Be, Bt = 1, mp.mpf('1.1'), mp.mpf('0.5')
k = -Bt/Be
f = k*mp.besseli(1, abs(k))/Ip(1, abs(k))*(-1) if False else abs(k)*mp.besseli(1, abs(k))/Ip(1, abs(k)) + (k*Be + Bt)**2*nout(1, k, mp.mpf(2)) - Bt**2
print('unstable branch F (Be=1.1,Bt=0.5,m=1,k=-Bt/Be, wall h=2):', f, ' bound', Bt**2/Be**2 - Bt**2)
# parameter illustration
mu0 = 4e-7*mp.pi; e = mp.mpf('1.602176634e-19')
p = 2*mp.mpf('1e20')*mp.mpf('12.5e3')*e
s = 8*mu0*p/25
print('p=%.6g Pa s=%.6f beta=s/4=%.6f Be=%.5f Bt=%.5f' % (p, s, s/4, 5*mp.sqrt(1 - 3*s/4), 5*mp.sqrt(s)))
# hot-core constants
def abd(c):
    a = mp.erf(c/mp.sqrt(2)) - mp.sqrt(2/mp.pi)*c*mp.exp(-c**2/2)
    b = mp.erf(c/mp.sqrt(2)) - mp.sqrt(2/mp.pi)*(c + c**3/3)*mp.exp(-c**2/2)
    d = mp.sqrt(2/mp.pi)*(c**2 + 2)*mp.exp(-c**2/2)
    return a, b, d
for c in [mp.mpf('2.8'), mp.mpf(3)]:
    a, b, d = abd(c)
    d0 = 2*mp.sqrt(2/mp.pi)
    print('c=%s a=%.10f H3=%.10f' % (c, a, b - d**2/(3*a**2)))
    for dl in [mp.mpf(0), mp.mpf('0.01')]:
        H4 = (1-dl)/(1+dl)*b - (d + dl*d0)**2/(3*(1-dl)**2*a**2)
        H5 = (1-dl)/(1+dl)*b - (d + dl*d0)**2/((1-dl)**2*a**2)
        print('   delta=%s H4=%.12f H5=%.16f' % (dl, H4, H5))
# chi moments cross-check by quadrature
c = mp.mpf('2.8')
a, b, d = abd(c)
dens = lambda r: mp.sqrt(2/mp.pi)*r**2*mp.exp(-r**2/2)
print('quadrature a,b,d:', mp.quad(dens, [0, c]) - a, mp.quad(lambda r: r**2*dens(r), [0, c])/3 - b, mp.quad(lambda r: r*dens(r), [c, mp.inf]) - d)
