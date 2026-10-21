"""UNTRUSTED.  The concrete coil field B_c = tfField + polyCoilFieldC of PlasmaLean.

The data are parsed from the Lean sources (PolygonCoilCubicData.lean: repKC, repVC; the orbit
under {id, Rot_pi, sigma, Rot_pi sigma} of PolygonCoilData.orbit; the TF rectangle of
RationalStellaratorCoilsTF.lean with Lambda = 10^6 and kappa = 1/2).

The segment field is the closed form `segClosed` of PolygonCoilSegment.lean:
    B = kappa (alpha + beta) / (alpha beta (alpha beta + a.b)) * (a x b),
    a = p - y, b = q - y, alpha = |a|, beta = |b|.
"""
import os
import re

import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
S32 = 2 ** 32
LAM = 10 ** 6


def parse_rep():
    src = open(os.path.join(ROOT, 'PlasmaLean/Design/PolygonCoilCubicData.lean')).read()
    k = re.search(r'def repKC : List Int := \[([^\]]*)\]', src).group(1)
    K = [int(x) for x in k.split(',')]
    body = src[src.index('def repVC'):]
    body = body[:body.index('def filsC')]
    polys = []
    for blk in re.findall(r'\[\s*(\([^\]]*\))\s*\]', body):
        pts = [tuple(int(v) for v in t) for t in re.findall(r'\((-?\d+),\s*(-?\d+),\s*(-?\d+)\)', blk)]
        polys.append(pts)
    assert len(polys) == 2 and all(len(p) == 24 for p in polys)
    return K, polys


def gRi(p):
    return (-p[0], -p[1], p[2])


def gSi(p):
    return (p[1], p[0], -p[2])


def fils():
    K, V = parse_rep()
    out = []
    for k, vs in zip(K, V):
        out += [(k, vs), (k, [gRi(p) for p in vs]), (-k, [gSi(p) for p in vs]),
                (-k, [gRi(gSi(p)) for p in vs])]
    return out


def all_segs():
    """List of (K, p, q) integer records (allSegs filsC), 192 entries."""
    segs = []
    for k, vs in fils():
        for i in range(len(vs)):
            segs.append((k, vs[i], vs[(i + 1) % len(vs)]))
    return segs


SEGS = all_segs()
TF = [((0, 0, -LAM), (0, 0, LAM)), ((0, 0, LAM), (LAM, 0, LAM)), ((LAM, 0, LAM), (LAM, 0, -LAM)),
      ((LAM, 0, -LAM), (0, 0, -LAM))]


def seg_arrays():
    """kappa, p, q as float arrays (all 196 segments, TF last)."""
    kap = [k / S32 for k, _, _ in SEGS] + [0.5] * 4
    P = [np.array(p, float) / S32 for _, p, _ in SEGS] + [np.array(p, float) for p, _ in TF]
    Q = [np.array(q, float) / S32 for _, _, q in SEGS] + [np.array(q, float) for _, q in TF]
    return np.array(kap), np.array(P), np.array(Q)


KAP, PP, QQ = seg_arrays()


def seg_factor(kap, a, b, al, be, ab):
    """kappa (alpha + beta)/(alpha beta (alpha beta + a.b)), evaluated stably: when a.b < 0 (the
    point sees the segment at an obtuse angle, e.g. the TF legs of length 2e6) the denominator
    alpha beta + a.b = |a x b|^2/(alpha beta - a.b) is used."""
    c = np.cross(a, b)
    cc = (c * c).sum(-1)
    stable = kap * (al + be) * (al * be - ab) / (al * be * cc)
    direct = kap * (al + be) / (al * be * (al * be + ab))
    return np.where(np.real(ab) < 0, stable, direct)


def field(y, which=slice(None)):
    """Real field at points y (..., 3), double precision (closed form)."""
    y = np.asarray(y, float)
    out = np.zeros(y.shape)
    for kap, p, q in zip(KAP[which], PP[which], QQ[which]):
        a = p - y
        b = q - y
        al = np.sqrt((a * a).sum(-1))
        be = np.sqrt((b * b).sum(-1))
        ab = (a * b).sum(-1)
        f = seg_factor(kap, a, b, al, be, ab)
        out += f[..., None] * np.cross(a, b)
    return out


def field_c(y, which=slice(None)):
    """Complex field at complex points y (..., 3) by the same closed form with principal square
    roots (valid in the neighbourhood of the real tube; cf. segFieldC_ofReal)."""
    y = np.asarray(y, complex)
    out = np.zeros(y.shape, complex)
    for kap, p, q in zip(KAP[which], PP[which], QQ[which]):
        a = p - y
        b = q - y
        al = np.sqrt((a * a).sum(-1))
        be = np.sqrt((b * b).sum(-1))
        ab = (a * b).sum(-1)
        f = seg_factor(kap, a, b, al, be, ab)
        out += f[..., None] * np.cross(a, b)
    return out


if __name__ == '__main__':
    print(len(SEGS), 'coil segments')
    y = np.array([1.0, 0.0, 0.0])
    print('B(1,0,0) =', field(y), ' poly part', field(y, slice(0, 192)))
