"""Scoping pilot (N-216 stage 3): enclosure quality of the frame-reduced Jacobian on wide balls.

UNTRUSTED. Nothing here is a proof and nothing is compiled by Lean. The script drives the
campaign's own Taylor-model arithmetic (``bounce_mirror_pilot.Model``, the sparse monomial
evaluator ``emit_sparse_taylor_slab.models`` and the frame algebra of ``bounce_phase_frame``)
with a trial ball of frame radius rho around a float-proposed reference line at label u.

For one slab it reports three things.

``existing``  The quantity the generated Lean modules bound today,
    A(s, x) = adj(M) (Jnum(x) M - D(x)^2 M') / (det(M) D(x)^2),
    with the whole spatial ball placed in the remainder of the two position models (exactly what
    ``emit_sparse_forward_jacobian.emit`` does with ``physical_trial_radius``). From the same
    enclosure of trace, difference and off-diagonal sum we read an upper AND a lower bound for
    the quadratic form:  (tr_lo - disk)/(2 den) <= <w, A w>/|w|^2 <= (tr_hi + disk)/(2 den).

``meanvalue`` The proposed alternative: the same enclosure on the central line (remainder 0),
    plus a Lipschitz term. With Q = D_x(n/D) the physical Jacobian,
    A(s, y + M v) - A(s, y) = sum_l v_l G_l,  G_l = M^-1 (sum_k M_kl H_k) M,  H_k = d_k Q,
    where H_k is enclosed on the tube by interval arithmetic from the second derivatives of
    the three field polynomials. Then |<w, (sum_l v_l G_l) w>| <= rho (|t| + |N|_F) |w|^2 with
    t_l = tr(G_l)/2 and N the 2x2 array of the traceless symmetric parts.

``float``     A sampled value of the true extreme eigenvalues of the symmetric part of A on the
    ball and the slab (the quantity a perfect enclosure would return), and the same for the
    central line alone.

All interval results use exact integer or rational arithmetic with outward rounding, but the
reference line and the frames are float proposals, as in the campaign.
"""
import argparse
import json
import sys
import time
from fractions import Fraction as F
from math import ceil, isqrt
from pathlib import Path

KAM = Path(__file__).resolve().parents[1] / "dommaschk_kam"
sys.path.insert(0, str(KAM))

import numpy as np  # noqa: E402

import bounce_mirror_pilot as pilot  # noqa: E402
from bounce_mirror_pilot import Model, R0M, SCALE, ZERO  # noqa: E402
from bounce_phase_frame import FRAME_SCALE, affine_frame, jacobian, product, propose_frame  # noqa: E402
from bounce_common_section import section_polynomial_data  # noqa: E402
from emit_sparse_jacobian import derivative  # noqa: E402
from emit_sparse_taylor_slab import DATA, coefficients, models  # noqa: E402

DT = F(1, 64)
SOURCES = ("dD", "dnR", "dnZ")


# ---------------------------------------------------------------- reference line and frames
def references(label, sign, wanted):
    """Float-proposed dyadic reference polynomials and frames, as in framed_segments."""
    ev, seeds = pilot.load_inputs()
    c, a = [pilot.seed_cut(*s, np.array([0.0]))[0][:, 0] for s in seeds]
    data = section_polynomial_data(0)
    start = [[FRAME_SCALE, 0], [0, FRAME_SCALE]]
    last = max(wanted)
    for i, nominal in enumerate(pilot.proposals(ev, c + label * (a - c), sign, DT, last + 1)):
        angles = pilot.angle_models(sign * (i + F(1, 2)) * DT, sign * DT / 2, F(0))
        center = [Model([x.a[0]]) for x in nominal]
        at_center = [Model([x.a[0]], x.e) for x in angles]
        end = propose_frame(start, *jacobian(data, at_center, center, sign), DT)
        if i in wanted:
            yield i, nominal, angles, start, end, data
        start = end


# ---------------------------------------------------------------- sparse polynomial tables
def tables():
    text = DATA.read_text()
    out = {}
    for name in SOURCES:
        p = coefficients(text, name)
        d = [derivative(p, 0), derivative(p, 1)]
        dd = [derivative(d[0], 0), derivative(d[0], 1), derivative(d[1], 1)]  # uu, uz, zz
        out[name] = (p, d, dd)
    return out


def total(terms, columns):
    return sum(models(terms, columns), ZERO)


# ---------------------------------------------------------------- existing machinery
def frame_radii(start, end, rho):
    """Half-widths of the physical box containing M(s) v for |v| <= rho, all |s| <= 1.

    'square' is the campaign convention op*rho on both coordinates. 'rows' uses the Euclidean
    norms of the rows of M, which are convex in s, hence attained at an endpoint."""
    op = affine_frame(start, end, DT)[-1]
    square = ceil(op * rho * SCALE)
    rows = []
    for k in (0, 1):
        n2 = max(sum(x * x for x in m[k]) for m in (start, end))
        rows.append(ceil(F(isqrt(n2) + 1, FRAME_SCALE) * rho * SCALE))
    return square, rows, op


def symmetric_models(tab, nominal, angles, start, end, sign, radii, horner=None):
    """Models of den, tr, dif, off exactly as matrix_certificate builds them.

    With horner (the harmonic Horner data of bounce_mirror_pilot.polynomial_data) the field
    and its gradient come from pilot.evaluate, the evaluator of the Python checker and of the
    Horner-jet Lean modules; otherwise from the sparse monomial sums."""
    R, z = (Model(x.a, e) for x, e in zip(nominal, radii, strict=True))
    if horner is not None:
        jnum, den2 = jacobian(horner, angles, [R, z], sign)
    else:
        columns = (R - R0M, z, angles[2], angles[1])
        val = [total(tab[n][0], columns) for n in SOURCES]
        grad = [[total(t, columns) for t in tab[n][1]] for n in SOURCES]
        den = val[0]
        if den.bound()[0] <= 0:
            raise ArithmeticError("field denominator not positive on the tube")
        jnum = [[(grad[i + 1][k] * den - val[i + 1] * grad[0][k]).integer(sign) for k in (0, 1)]
                for i in (0, 1)]
        den2 = den * den
    m, rate, adj, det, _ = affine_frame(start, end, DT)
    jm = product(jnum, m)
    centered = [[jm[i][j] - den2 * rate[i][j] for j in (0, 1)] for i in (0, 1)]
    num = product(adj, centered)
    return dict(den=det * den2, tr=num[0][0] + num[1][1], dif=num[0][0] - num[1][1],
                off=num[0][1] + num[1][0], jremainder=max(x.e for row in jnum for x in row),
                den2=den2)


def sqrt_upper(x, scale=10**12):
    return F(isqrt(ceil(x * scale * scale)) + 1, scale)


def two_sided(sm):
    """Upper and lower bound for the Rayleigh quotient of the symmetric part of A."""
    dl, dh = sm["den"].bound()
    if dl <= 0:
        raise ArithmeticError("frame-field denominator not positive")
    tlo, thi = sm["tr"].bound()
    disk = sqrt_upper(max(map(abs, sm["dif"].bound())) ** 2 + max(map(abs, sm["off"].bound())) ** 2)
    hi, lo = thi + disk, tlo - disk
    return (lo / (2 * (dl if lo < 0 else dh)), hi / (2 * (dl if hi > 0 else dh)),
            dict(den=[float(dl), float(dh)], tr=[float(tlo), float(thi)], disk=float(disk),
                 dif=float(max(map(abs, sm["dif"].bound()))),
                 off=float(max(map(abs, sm["off"].bound()))),
                 remainder_tr=sm["tr"].e / SCALE, remainder_dif=sm["dif"].e / SCALE,
                 remainder_J_over_D2=float(F(sm["jremainder"], SCALE) / sm["den2"].bound()[0])))


# ---------------------------------------------------------------- rational intervals
class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)

    @staticmethod
    def of(model):
        return I(*model.bound())

    def __add__(self, o):
        o = o if isinstance(o, I) else I(o)
        return I(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, I) else I(o)))

    def __mul__(self, o):
        o = o if isinstance(o, I) else I(o)
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return I(min(p), max(p))

    __rmul__ = __mul__

    def inv(self):
        if self.lo <= 0:
            raise ArithmeticError("interval reciprocal of a non-positive quantity")
        return I(1 / self.hi, 1 / self.lo)

    def mag(self):
        return max(abs(self.lo), abs(self.hi))

    def round(self, digits=10**15):
        """Outward rounding keeps the rationals short."""
        return I(F((self.lo * digits).__floor__(), digits), F(-((-self.hi * digits).__floor__()), digits))


def hull(a, b):
    return b if a is None else I(min(a.lo, b.lo), max(a.hi, b.hi))


def horner_second_data():
    """Harmonic Horner rows (as bounce_mirror_pilot.polynomial_data) up to second derivatives."""
    from bounce_collar import harmonic_polynomial
    from bounce_launch_box import Box, field_polynomials

    out = []
    for p in field_polynomials():
        group = []
        for axes in ((), (0,), (1,), (0, 0), (0, 1), (1, 1)):
            current = dict(p)
            for axis in axes:
                lowered = {}
                for powers, x in current.items():
                    ix = list(powers)
                    n = ix[axis]
                    if n:
                        ix[axis] -= 1
                        lowered[tuple(ix)] = Box(n * x.lo, n * x.hi)
                current = lowered
            group.append({k: [[Model.box(v) for v in row] for row in rows]
                          for k, rows in harmonic_polynomial(current).items()})
        out.append(group)
    return out


def second_derivatives(tab, nominal, angles, sign, radii, pieces=1, horner2=None):
    """Interval hull of H[k][i][j] = sign d_k d_j (n_i/D) over pieces^2 sub-boxes of the tube."""
    H = [[[None, None], [None, None]] for _ in (0, 1)]
    sub = [-(-e // pieces) for e in radii]
    for a in range(pieces):
        for b in range(pieces):
            shift = [(2 * a + 1 - pieces) * sub[0], (2 * b + 1 - pieces) * sub[1]]
            cell = [Model([x.a[0] + d, *x.a[1:]]) for x, d in zip(nominal, shift)]
            part = second_derivatives_box(tab, cell, angles, sign, sub, horner2)
            for k in (0, 1):
                for i in (0, 1):
                    for j in (0, 1):
                        H[k][i][j] = hull(H[k][i][j], part[k][i][j])
    return H


def second_derivatives_box(tab, nominal, angles, sign, radii, horner2=None):
    R, z = (Model(x.a, e) for x, e in zip(nominal, radii, strict=True))
    columns = (R - R0M, z, angles[2], angles[1])
    val, d1, d2 = [], [], []
    for index, n in enumerate(SOURCES):
        if horner2 is not None:
            v, du, dz, uu, uz, zz = (I.of(pilot.evaluate(g, [R, z], angles)[0]).round()
                                     for g in horner2[index])
            val.append(v)
            d1.append([du, dz])
            d2.append([[uu, uz], [uz, zz]])
            continue
        p, d, dd = tab[n]
        val.append(I.of(total(p, columns)).round())
        d1.append([I.of(total(t, columns)).round() for t in d])
        uu, uz, zz = (I.of(total(t, columns)).round() for t in dd)
        d2.append([[uu, uz], [uz, zz]])
    D, Dj, Djk = val[0], d1[0], d2[0]
    iD = D.inv()
    # H[k][i][j] = d_k d_j (n_i / D), times the direction sign.
    H = [[[None, None], [None, None]] for _ in (0, 1)]
    for i in (0, 1):
        n, nj, njk = val[i + 1], d1[i + 1], d2[i + 1]
        for j in (0, 1):
            for k in (0, 1):
                h = (njk[j][k] * iD - (nj[j] * Dj[k] + nj[k] * Dj[j] + n * Djk[j][k]) * iD * iD
                     + 2 * n * Dj[j] * Dj[k] * iD * iD * iD)
                H[k][i][j] = (h * sign).round()
    return H


def lipschitz_constant(tab, nominal, angles, start, end, sign, radii, pieces=1, horner2=None):
    """K with |<w,(A(s,y+Mv)-A(s,y))w>| <= K |v| |w|^2 on the tube, by interval arithmetic."""
    H = second_derivatives(tab, nominal, angles, sign, radii, pieces, horner2)
    M = [[I(min(a, b), max(a, b)) * F(1, FRAME_SCALE) for a, b in zip(r0, r1)]
         for r0, r1 in zip(start, end)]
    det_lo = affine_frame(start, end, DT)[3].bound()[0]
    det_hi = affine_frame(start, end, DT)[3].bound()[1]
    idet = I(det_lo, det_hi).inv()
    adj = [[M[1][1], -M[0][1]], [-M[1][0], M[0][0]]]

    def mat(a, b):
        return [[(a[i][0] * b[0][j] + a[i][1] * b[1][j]).round() for j in (0, 1)] for i in (0, 1)]

    t2 = F(0)
    n2 = F(0)
    for col in (0, 1):
        mix = [[(M[0][col] * H[0][i][j] + M[1][col] * H[1][i][j]).round() for j in (0, 1)]
               for i in (0, 1)]
        G = mat(adj, mat(mix, M))
        G = [[(x * idet).round() for x in row] for row in G]
        t2 += ((G[0][0] + G[1][1]) * F(1, 2)).mag() ** 2
        n2 += ((G[0][0] - G[1][1]) * F(1, 2)).mag() ** 2 + ((G[0][1] + G[1][0]) * F(1, 2)).mag() ** 2
    hmax = max(H[k][i][j].mag() for k in (0, 1) for i in (0, 1) for j in (0, 1))
    return sqrt_upper(t2) + sqrt_upper(n2), float(hmax)


# ---------------------------------------------------------------- float truth
def float_extremes(tab, nominal, angles_center, start, end, sign, index, rho):
    def ev(terms, u, z, c, s):
        return sum(float(q) * u**i * z**j * c**k * s**n for q, (i, j, k, n) in terms)

    def Q(phi, x):
        u, z, c, s = x[0] - float(pilot.R0), x[1], np.cos(2 * phi), np.sin(2 * phi)
        v = [ev(tab[n][0], u, z, c, s) for n in SOURCES]
        g = [[ev(t, u, z, c, s) for t in tab[n][1]] for n in SOURCES]
        return sign * np.array([[(g[i + 1][k] * v[0] - v[i + 1] * g[0][k]) / v[0] ** 2
                                 for k in (0, 1)] for i in (0, 1)])

    m0, m1 = (np.array(m, dtype=float) / FRAME_SCALE for m in (start, end))
    rate = (m1 - m0) / float(DT)
    polys = [np.array(x.a, dtype=float) / SCALE for x in nominal]
    dirs = [np.array([np.cos(t), np.sin(t)]) for t in np.arange(16) * np.pi / 8]
    out = dict(center=[0.0, 0.0], ball=[0.0, 0.0], excess=[0.0, 0.0])
    first = True
    for s in np.linspace(-1, 1, 9):
        phi = sign * (index + (s + 1) / 2) * float(DT)
        y = np.array([np.polynomial.polynomial.polyval(s, p) for p in polys])
        M = ((1 - s) * m0 + (1 + s) * m1) / 2
        Minv = np.linalg.inv(M)
        A0 = Minv @ (Q(phi, y) @ M - rate)
        e0 = np.linalg.eigvalsh((A0 + A0.T) / 2)
        lo, hi = e0[0], e0[-1]
        xlo = xhi = 0.0
        for d in dirs:
            for scale in (0.5, 1.0):
                A = Minv @ (Q(phi, y + M @ (scale * rho * d)) @ M - rate)
                e = np.linalg.eigvalsh((A + A.T) / 2)
                lo, hi = min(lo, e[0]), max(hi, e[-1])
                ex = np.linalg.eigvalsh(((A - A0) + (A - A0).T) / 2)
                xlo, xhi = min(xlo, ex[0]), max(xhi, ex[-1])
        if first:
            out["center"], out["ball"], first = [e0[0], e0[-1]], [lo, hi], False
        out["center"] = [min(out["center"][0], e0[0]), max(out["center"][1], e0[-1])]
        out["ball"] = [min(out["ball"][0], lo), max(out["ball"][1], hi)]
        out["excess"] = [min(out["excess"][0], xlo), max(out["excess"][1], xhi)]
    return {k: [float(a), float(b)] for k, (a, b) in out.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--label", type=F, default=F(474, 1000))
    parser.add_argument("--slabs", type=int, nargs="+", default=[1, 300])
    parser.add_argument("--signs", type=int, nargs="+", default=[1, -1],
                        help="the two directions agree by the phase-zero reflection symmetry")
    parser.add_argument("--radii", type=F, nargs="+",
                        default=[F(1, 10**5), F(3, 10**4), F(1, 10**3)])
    parser.add_argument("--pieces", type=int, nargs="+", default=[1, 4],
                        help="subdivisions per axis of the tube box for the second derivatives")
    parser.add_argument("--horner-pieces", type=int, nargs="*", default=[1, 2],
                        help="the same with harmonic Horner evaluation of the second derivatives")
    parser.add_argument("--output")
    args = parser.parse_args()
    tab = tables()
    horner2 = horner_second_data() if args.horner_pieces else None
    rows = []
    for sign in args.signs:
        for index, nominal, angles, start, end, data in references(float(args.label), sign, set(args.slabs)):
            # The central line: the existing enclosure with no spatial ball.
            clock = time.time()
            c_lo, c_hi, c_info = two_sided(symmetric_models(tab, nominal, angles, start, end, sign, (0, 0)))
            central_seconds = time.time() - clock
            for rho in args.radii:
                square, row_radii, op = frame_radii(start, end, rho)
                row = dict(sign=sign, slab=index, rho=float(rho), frame_norm_upper=float(op),
                           physical_box=[r / SCALE for r in row_radii], physical_square=square / SCALE,
                           central=dict(mu_lower=float(c_lo), mu_upper=float(c_hi), **c_info))
                for tag, radii, horner in (("existing_square", (square, square), None),
                                           ("existing_rows", row_radii, None),
                                           ("existing_horner_rows", row_radii, data)):
                    try:
                        lo, hi, info = two_sided(symmetric_models(tab, nominal, angles, start, end,
                                                                  sign, radii, horner))
                        row[tag] = dict(mu_lower=float(lo), mu_upper=float(hi), **info)
                    except ArithmeticError as error:
                        row[tag] = dict(failed=str(error))
                variants = [(("meanvalue" if n == 1 else f"meanvalue_{n}x{n}"), n, None)
                            for n in args.pieces]
                variants += [(("meanvalue_horner" if n == 1 else f"meanvalue_horner_{n}x{n}"), n, horner2)
                             for n in args.horner_pieces]
                for tag, pieces, method in variants:
                    clock = time.time()
                    K, hmax = lipschitz_constant(tab, nominal, angles, start, end, sign, row_radii,
                                                 pieces, method)
                    row[tag] = dict(
                        lipschitz=float(K), second_derivative_max=hmax,
                        mu_lower=float(c_lo - K * rho), mu_upper=float(c_hi + K * rho),
                        python_seconds=time.time() - clock)
                row["float"] = float_extremes(tab, nominal, angles, start, end, sign, index, float(rho))
                row["central_python_seconds"] = central_seconds
                rows.append(row)
                print(json.dumps(row), flush=True)
    if args.output:
        with open(args.output, "w") as out:
            json.dump(dict(label=str(args.label), rows=rows), out, indent=1)


if __name__ == "__main__":
    main()
