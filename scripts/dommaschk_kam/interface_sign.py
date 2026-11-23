"""Untrusted N-44 interface sign screen for the stored Dommaschk torus A.

Geometric angles are (theta, phi) in radians. Fourier sampling uses psi=2*phi.
Physical field-line time gives Y=q*v, v=(iota,1), q=B_phi/R. The straight
physical-time chart is x'=x+v*h, D_v h=c/q-1, c=1/mean(1/q), omega=c*v.
Pull back each constant straight-chart covector d as d+(v.d)*dh. Then the
first/second forms in the original geometric chart may be used without
inverting the angular map. II_ij = -n.K_ij uses the outward unit normal, so a
round cylinder has positive poloidal curvature (N-44, source sections 6–7).

Run from the root with .venv-ws/bin/python scripts/dommaschk_kam/interface_sign.py
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

from dfield import Evaluator, ExactField, TARGET, TARGET_SHA
from qs_defect import torus_grid

HERE = Path(__file__).resolve().parent
TORUS = HERE / 'results/20261101T111958Z/torus_A_N96_M80.json'
TORUS_SHA = 'b2524e61c865759436434df012a2727febd5bc73347c0412c493efc73404c5ac'
FIELD_SHA = '9bd100ec63244c0980856a3633188f7bebcbb28b7a96417e2931210583bcb646'


def dot(a, b):
    return np.sum(a * b, axis=-1)


def vec(x, y, z):
    return np.stack([x, y, z], axis=-1)


def curvature_test(data, field, n):
    """Work on the unshifted Fourier grid for the full real-valued input series."""
    if n <= 2 * max(data['N'], data['M']):
        raise ValueError('grid must resolve all input Fourier modes')
    g = torus_grid(data, n, n)
    R, Rt, Rp = g['R'], g['R_t'], 2 * g['R_p']
    z, zt, zp = g['z'], g['z_t'], 2 * g['z_p']
    k = np.fft.fftfreq(n, 1/n)[:, None]
    m = 2 * np.fft.fftfreq(n, 1/n)[None, :]

    def derivative(f, mode):
        return np.fft.ifft2(1j * mode * np.fft.fft2(f)).real

    # Components in the moving orthonormal cylindrical basis at each point.
    t = vec(Rt, np.zeros_like(R), zt)
    p = vec(Rp, R, zp)
    tt = vec(derivative(Rt, k), np.zeros_like(R), derivative(zt, k))
    tp = vec(derivative(Rt, m), Rt, derivative(zt, m))
    pp = vec(derivative(Rp, m) - R, 2*Rp, derivative(zp, m))
    normal = np.cross(p, t)
    normal /= np.linalg.norm(normal, axis=-1, keepdims=True)
    psi = g['psi']
    # The rounded moving centre shared by A and C in DommaschkKamAData.lean.
    centre_R = 0.9187 + 0.0592*np.cos(psi) - 0.0108*np.cos(2*psi) - 0.003*np.cos(3*psi)
    centre_z = -0.0604*np.sin(psi) + 0.0107*np.sin(2*psi) + 0.0029*np.sin(3*psi)
    outward = normal[..., 0]*(R-centre_R) + normal[..., 2]*(z-centre_z)
    if outward.min() <= 0:
        raise ValueError('normal failed the outward test against the moving centre')

    g11, g12, g22 = dot(t, t), dot(t, p), dot(p, p)
    det = g11*g22 - g12**2
    if det.min() <= 0:
        raise ValueError('singular first fundamental form')
    ii11, ii12, ii22 = -dot(normal, tt), -dot(normal, tp), -dot(normal, pp)
    iota = -(19 + np.sqrt(5))/89
    br, bp, bz = field.B_cyl(R, g['phi'], z)
    q = bp/R
    if q.min() <= 0:
        raise ValueError('field has nonpositive toroidal velocity')
    Y = q[..., None]*(iota*t + p)
    tangency_error = np.linalg.norm(Y - vec(br, bp, bz), axis=-1).max()
    # Row II(Y,.) g^{-1} in geometric angles, applied below to covectors.
    yt, yp = q*(iota*ii11+ii12), q*(iota*ii12+ii22)
    wt = (yt*g22 - yp*g12)/det
    wp = (yp*g11 - yt*g12)/det
    normal_curvature = q*(iota*yt+yp)/dot(Y, Y)  # II(Y,Y)/|Y|^2

    c = 1/np.mean(1/q)
    rhs = c/q - 1
    denominator = 1j * (iota*k + m)
    denominator[0, 0] = 1
    H = np.fft.fft2(rhs)/denominator
    H[0, 0] = 0
    ht, hp = np.fft.ifft2(1j*k*H).real, np.fft.ifft2(1j*m*H).real
    det_chart = 1+iota*ht+hp
    # d0=omega/|omega|^2 and d1=J omega=(-c,c*iota).
    norm_factor = c*(iota**2+1)
    a = wt*(iota/norm_factor + ht/c) + wp*(1/norm_factor + hp/c)
    b = c*(-wt+iota*wp)
    if det_chart.min() <= 0:
        raise ValueError('physical-time chart has nonpositive Jacobian')

    def point(i, j):
        return dict(theta_turn=i/n, phi_turn=j/(2*n), a=float(a[i,j]),
                    b=float(b[i,j]), normal_curvature=float(normal_curvature[i,j]))

    # These two angles gave well-separated, opposite requirements in the initial
    # search. Retain them across grid refinements to avoid near-zero denominators.
    if n % 4:
        raise ValueError('grid must contain the fixed witness points')
    witnesses = [point(n//2, 0), point(0, n//4)]
    for witness in witnesses:
        witness['sigma_boundary'] = -witness['a']/witness['b']

    return dict(grid=n, omega=[c*iota, c], min_outward=float(outward.min()),
                min_area=float(np.sqrt(det.min())), max_tangency_error=float(tangency_error),
                chart_determinant_min=float(det_chart.min()),
                max_chart_residual=float(abs(q*det_chart-c).max()),
                a_range=[float(a.min()),float(a.max())], b_range=[float(b.min()),float(b.max())],
                witnesses=witnesses)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--grids', type=int, nargs='+', default=[256,384,512])
    args = ap.parse_args()
    for path, expected in [(TORUS,TORUS_SHA), (Path(TARGET),FIELD_SHA)]:
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f'unexpected input file: {path}')
    data = json.loads(TORUS.read_text())
    field = ExactField()
    if data['candidate_sha256'] != TARGET_SHA or field.sha != TARGET_SHA or data['tag'] != 'A':
        raise ValueError('candidate and torus identity mismatch')
    ev = Evaluator(field)
    for n in args.grids:
        print(json.dumps(curvature_test(data, ev, n), indent=2))


if __name__ == '__main__':
    main()
