"""UNTRUSTED numerics (Q-19, task a).  Invariant tori of field(1/4) near the axis: rotation number
iota by a weighted Birkhoff average, and the section conjugacy K(theta_s) on phi = 0.

Integrator: classical RK4 in phi, vectorized over field lines (NS steps per field period pi).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from field import rhs, rhs_plain

NS = 200  # RK4 steps per field period (step-halving check in __main__)


def rk4(fun, y, phi0, nsteps, dphi, every=1, callback=None):
    """Integrate y (shape (dim, nlines)) from phi0; callback(phi, y) every `every` steps."""
    phi = phi0
    if callback is not None:
        callback(phi, y)
    for i in range(nsteps):
        k1 = fun(phi, y)
        k2 = fun(phi + dphi/2, y + dphi/2*k1)
        k3 = fun(phi + dphi/2, y + dphi/2*k2)
        k4 = fun(phi + dphi, y + dphi*k3)
        y = y + dphi/6*(k1 + 2*k2 + 2*k3 + k4)
        phi = phi0 + (i + 1)*dphi
        if callback is not None and (i + 1) % every == 0:
            callback(phi, y)
    return y


def sections(R0s, z0s, nper, ns=NS):
    """Section points at phi = k pi, k = 0..nper, for lines launched at (R0s, z0s) on phi = 0."""
    y = np.array([np.atleast_1d(R0s), np.atleast_1d(z0s)], dtype=float)
    out = []
    rk4(rhs_plain, y, 0.0, nper*ns, np.pi/ns, every=ns, callback=lambda p, yy: out.append(yy.copy()))
    return np.array(out)  # (nper+1, 2, nlines)


def birkhoff_weights(n):
    t = (np.arange(n) + 0.5)/n
    w = np.exp(-1.0/(t*(1 - t)))
    return w/w.sum()


def iota_of(sec):
    """Rotation number from section points (nper+1, 2, nlines): poloidal angle about the exact axis
    (R, z) = (1, 0); iota = <d theta per period>/pi.  Returns (iota, digits estimate)."""
    th = np.unwrap(np.arctan2(sec[:, 1, :], sec[:, 0, :] - 1.0), axis=0)
    d = np.diff(th, axis=0)
    n = d.shape[0]
    full = (birkhoff_weights(n)[:, None]*d).sum(0)/np.pi
    h = n//2
    a = (birkhoff_weights(h)[:, None]*d[:h]).sum(0)/np.pi
    b = (birkhoff_weights(h)[:, None]*d[h:2*h]).sum(0)/np.pi
    return full, -np.log10(np.abs(a - b) + 1e-17)


def conjugacy(sec_line, iota, nmodes=32):
    """Fourier fit R(theta), z(theta) with theta_s(k) = k*pi*iota (theta_s = 0 at launch).
    Returns coefficient arrays and the fit residual (max abs)."""
    k = np.arange(sec_line.shape[0])
    th = k*np.pi*iota
    cols = [np.ones_like(th)]
    for m in range(1, nmodes + 1):
        cols += [np.cos(m*th), np.sin(m*th)]
    A = np.array(cols).T
    cR, *_ = np.linalg.lstsq(A, sec_line[:, 0], rcond=None)
    cZ, *_ = np.linalg.lstsq(A, sec_line[:, 1], rcond=None)
    res = max(np.abs(A@cR - sec_line[:, 0]).max(), np.abs(A@cZ - sec_line[:, 1]).max())
    return cR, cZ, res


def K_eval(c, th, deriv=False):
    nm = (len(c) - 1)//2
    out = np.full_like(th, 0.0 if deriv else c[0])
    for m in range(1, nm + 1):
        if deriv:
            out += m*(-c[2*m-1]*np.sin(m*th) + c[2*m]*np.cos(m*th))
        else:
            out += c[2*m-1]*np.cos(m*th) + c[2*m]*np.sin(m*th)
    return out


IOTA_A = (75 + np.sqrt(5))/562   # KAM-certified torus (RationalStellaratorConfinedForever)


def find_r_for_iota(target, lo=0.12, hi=0.145, nper=2000, rounds=3, n=17):
    """Vectorized bracketing: evaluate iota on a grid, keep the bracketing cell, repeat."""
    for _ in range(rounds):
        rr = np.linspace(lo, hi, n)
        io, _ = iota_of(sections(1 + rr, 0*rr, nper))
        k = np.searchsorted(io, target)
        lo, hi = rr[k-1], rr[k]
        # linear interpolation inside the cell
        rint = rr[k-1] + (target - io[k-1])*(rr[k] - rr[k-1])/(io[k] - io[k-1])
    return rint


if __name__ == '__main__':
    rs = np.array([0.02, 0.05, 0.10, 0.131, 0.15, 0.20, 0.25, 0.287, 0.328, 0.36, 0.40, 0.42])
    sec = sections(1 + rs, 0*rs, 2000)
    io, dig = iota_of(sec)
    io2, _ = iota_of(sections(1 + rs, 0*rs, 2000, ns=2*NS))
    print('step-halving change in iota (max):', np.abs(io - io2).max())
    print('iota_0 exact = 1 - sqrt(3)/2 =', 1 - np.sqrt(3)/2)
    for r, i, d in zip(rs, io, dig):
        print(f'r = {r:.3f}  iota = {i:.10f}  digits ~ {d:.1f}')
    rA = find_r_for_iota(IOTA_A)
    print('KAM torus A: iota_A =', IOTA_A, ' launch r (phi=0 outboard) =', rA)
