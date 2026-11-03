"""UNTRUSTED generator (N-34 module D3, notes/theory/dommaschk-qs-defect.md §4): the polynomial form
of the per-torus quasi-axisymmetry defect of the Dommaschk certification field on an invariant torus.

Flow form (`Design/DommaschkKamField`, `DommaschkKamIdent`): u = R - R0 (R0 = 29/32), c = cos 2 phi,
s = sin 2 phi, D = R^7 B_phi, n_R = R^8 B_R, n_z = R^8 B_z (physical components).  On an invariant
torus K(theta, phi) = (R, z)(theta, phi) with frequency (iota, 1), L = d_phi + iota d_theta, the
invariance equations are D L u = n_R, D L z = n_z.  With

    Q   = n_R^2 + R^2 D^2 + n_z^2                     (R^16 |B|^2 = Q)
    Q_u = 2 (n_R n_R,u + R D^2 + R^2 D D_u + n_z n_z,u),  Q_z = 2 (n_R n_R,z + R^2 D D_z + n_z n_z,z),
    Q_f = 2 (n_R n_R,f + R^2 D D_f + n_z n_z,f)          (f = phi: the formal derivative phiS)
    P_L = Q_u n_R + Q_z n_z + D Q_f                      (= D L Q on the torus)
    M_L = R P_L - 16 Q n_R                               (= R^17 D L|B|^2)
    N0  = R^8 M_L,   N1 = n_R M_L - Q (R Q_u - 16 Q),   N2 = n_z M_L - R Q Q_z,
    N_g = N0 + iota (N1 u_theta + N2 z_theta),

the Boozer toroidal derivative (N-34 §1, the A1 definition torusQADefect) is

    d_{phi_B}|B|^2 = [(1 + iota a) L|B|^2 - iota J d_theta|B|^2] / J  =  N_g / (Q R^17),
    torusQADefect  = d_{phi_B}|B|              = N_g / (2 Q^{3/2} R^9),

with a = B . d_theta K = (n_R u_theta + n_z z_theta)/R^8 and J = B . L K = Q/(R^8 D).

This script
 1. derives the formula symbolically (sympy, exact, independent of the straight-line program: the
    derivatives of |B|^2 and |B| are taken by sympy from Q/R^16 with D, n_R, n_z unknown functions);
 2. checks it exactly (Fractions) with the actual flow-form polynomials at rational points, against
    a direct route through the expanded Q (u-form and R-form);
 3. validates it numerically on the data torus C against the untrusted estimator `qs_defect.py`;
 4. reports the sizes of the expanded N0, N1, N2 (why the certificate uses the straight-line
    program and not the expanded polynomials);
 5. writes `PlasmaLean/Design/DommaschkKamCQSData.lean`: the phi-derivatives of D, n_R, n_z in
    u-form (`dDf`, `dnRf`, `dnZf`) and in R-form (`dDRf`, `dnRhf`, `dnZRf`), checked first with the
    Python mirror of the Lean operations (`emit_flowfield.l_phi`, `substR`).

(needs numpy and sympy: the venv /tmp/dqa-venv; run with -I)
usage: python -I emit_qs.py [--no-write] [--sizes-u] [--n 256]
"""
import argparse
import json
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_flowfield as EF                                   # noqa: E402

R0 = EF.R0
DEF_TORUS = os.path.join(HERE, 'results', '20261101T015838Z', 'torus_C_N96_M80.json')
OUT = os.path.join(REPO, 'PlasmaLean', 'Design', 'DommaschkKamCQSData.lean')


# ----------------------------------------------------------------------------------------------
# the straight-line program (generic in the ring operations)

def qs_nodes(lv, R, add, mul, sc):
    """The nodes of the defect numerator from the leaf values `lv` (keys D, Du, Dz, Df, nR, nRu, nRz,
    nRf, nZ, nZu, nZz, nZf) and R, with ring operations add (n-ary), mul, sc (scalar * x)."""
    D, nR, nZ = lv['D'], lv['nR'], lv['nZ']
    R2 = mul(R, R)
    DD = mul(D, D)
    Q = add(mul(nR, nR), mul(R2, DD), mul(nZ, nZ))
    Qu = sc(2, add(mul(nR, lv['nRu']), mul(R, DD), mul(R2, mul(D, lv['Du'])), mul(nZ, lv['nZu'])))
    Qz = sc(2, add(mul(nR, lv['nRz']), mul(R2, mul(D, lv['Dz'])), mul(nZ, lv['nZz'])))
    Qf = sc(2, add(mul(nR, lv['nRf']), mul(R2, mul(D, lv['Df'])), mul(nZ, lv['nZf'])))
    PL = add(mul(Qu, nR), mul(Qz, nZ), mul(D, Qf))
    ML = add(mul(R, PL), sc(-16, mul(Q, nR)))
    R4 = mul(R2, R2)
    N0 = mul(mul(R4, R4), ML)
    N1 = add(mul(nR, ML), sc(-1, mul(Q, add(mul(R, Qu), sc(-16, Q)))))
    N2 = add(mul(nZ, ML), sc(-1, mul(R, mul(Q, Qz))))
    return dict(Q=Q, Qu=Qu, Qz=Qz, Qf=Qf, PL=PL, ML=ML, N0=N0, N1=N1, N2=N2)


def num_add(*xs):
    s = xs[0]
    for x in xs[1:]:
        s = s + x
    return s


def num_ops():
    return num_add, (lambda a, b: a*b), (lambda k, a: k*a)


def poly_ops():
    return (lambda *ps: EF.padd(*ps)), EF.pmul, (lambda k, p: EF.pscale(p, Fr(k)))


def leaves_poly(P):
    """Leaf dict polynomials from D, nR, nZ (dict form, slot 0 = u or R)."""
    lv = {}
    for k, nm in (('D', 'D'), ('nR', 'nR'), ('nZ', 'nZ')):
        p = P[nm]
        lv[k] = p
        lv[k + 'u'] = EF.pdiff(p, 0)
        lv[k + 'z'] = EF.pdiff(p, 1)
        lv[k + 'f'] = EF.pphi(p)
    return lv


def peval(p, x):
    """Exact value of a dict polynomial at x = (x0, x1, c, s)."""
    tot = Fr(0)
    for (a, b, c, d), q in p.items():
        tot += q * x[0]**a * x[1]**b * x[2]**c * x[3]**d
    return tot


# ----------------------------------------------------------------------------------------------
# 1. symbolic derivation

def symbolic_check():
    import sympy as sp
    u, z, ph = sp.symbols('u z phi', real=True)
    iota, uth, zth = sp.symbols('iota u_theta z_theta', real=True)
    R = R0 + u
    Df, nRf, nZf = (sp.Function(n)(u, z, ph) for n in ('D', 'n_R', 'n_z'))
    # physical components and |B|^2 (independently of Q's definition)
    BR, BP, BZ = nRf/R**8, Df/R**7, nZf/R**8
    B2 = BR**2 + BP**2 + BZ**2
    Bn = sp.sqrt(B2)
    # leaf symbols for values and first derivatives at the torus point
    names = ['D', 'Du', 'Dz', 'Df', 'nR', 'nRu', 'nRz', 'nRf', 'nZ', 'nZu', 'nZz', 'nZf']
    S = {n: sp.Symbol(n, real=True) for n in names}
    rep = {}
    for F, k in ((Df, 'D'), (nRf, 'nR'), (nZf, 'nZ')):
        rep[sp.Derivative(F, u)] = S[k + 'u']
        rep[sp.Derivative(F, z)] = S[k + 'z']
        rep[sp.Derivative(F, ph)] = S[k + 'f']
    rep_vals = {Df: S['D'], nRf: S['nR'], nZf: S['nZ']}

    def at_pt(e):
        return e.subs(rep).subs(rep_vals)

    # torus derivatives: Lu = L u, Lz = L z eliminated by invariance D L u = n_R, D L z = n_z
    Lu, Lz = S['nR']/S['D'], S['nZ']/S['D']

    def L_of(h):      # L h = h_u L u + h_z L z + h_phi (chain rule along the torus)
        return at_pt(sp.diff(h, u))*Lu + at_pt(sp.diff(h, z))*Lz + at_pt(sp.diff(h, ph))

    def th_of(h):     # d_theta h = h_u u_theta + h_z z_theta
        return at_pt(sp.diff(h, u))*uth + at_pt(sp.diff(h, z))*zth

    BRv, BPv, BZv = at_pt(BR), at_pt(BP), at_pt(BZ)
    a = BRv*uth + BZv*zth                          # B . d_theta K, d_theta K = u_theta e_R + z_theta e_z
    J = BRv*Lu + BPv*R + BZv*Lz                    # B . L K,  L K = L u e_R + R e_phi + L z e_z
    G2 = ((1 + iota*a)*L_of(B2) - iota*J*th_of(B2))/J
    g1 = ((1 + iota*a)*L_of(Bn) - iota*J*th_of(Bn))/J
    # the straight-line program on the leaf symbols
    nd = qs_nodes(S, R, *num_ops())
    Ng = nd['N0'] + iota*(nd['N1']*uth + nd['N2']*zth)
    Qs = nd['Q']
    checks = {
        'B2 = Q/R^16': sp.simplify(at_pt(B2) - Qs/R**16),
        'J = Q/(R^8 D)': sp.simplify(J - Qs/(R**8*S['D'])),
        'a': sp.simplify(a - (S['nR']*uth + S['nZ']*zth)/R**8),
        'd_phiB |B|^2 = N_g/(Q R^17)': sp.simplify(sp.together(G2 - Ng/(Qs*R**17))),
    }
    # D L Q = P_L with Q as a function (product rule done by sympy)
    Qfun = nRf**2 + R**2*Df**2 + nZf**2
    checks['D L Q = P_L'] = sp.simplify(sp.expand(S['D']*L_of(Qfun) - nd['PL']))
    checks['R^17 D L|B|^2 = M_L'] = sp.simplify(sp.expand(R**17*S['D']*L_of(B2)) - nd['ML'])
    # |B| version (the A1 definition), with Q > 0, R > 0: replace sqrt(Q/R^16) = sqrt(Q)/R^8
    diff = sp.simplify(sp.together(g1 - Ng/(2*Qs*sp.sqrt(at_pt(B2))*R**17)))
    checks['torusQADefect = N_g/(2 Q R^17 |B|)'] = diff
    # and |B| = sqrt(Q)/R^8 for R > 0: N_g/(2 Q^{3/2} R^9)
    qpos, Rp = sp.Symbol('qpos', positive=True), sp.Symbol('Rp', positive=True)
    e = (sp.sqrt(qpos/Rp**16) - sp.sqrt(qpos)/Rp**8)
    checks['sqrt(Q/R^16) = sqrt(Q)/R^8 (R, Q > 0)'] = sp.simplify(e)
    bad = {k: v for k, v in checks.items() if v != 0}
    assert not bad, bad
    # linearity of N_g in (u_theta, z_theta) and its degree in iota
    P = sp.Poly(sp.expand(Ng), iota, uth, zth)
    assert P.total_degree() <= 2 and all(m[0] == m[1] + m[2] and m[1] + m[2] <= 1 for m in P.monoms()), \
        P.monoms()
    return sorted(checks)


# ----------------------------------------------------------------------------------------------
# 2. exact checks with the actual polynomials

def exact_point_checks(P, Rpoly, pts, form):
    """At rational (x0, z, c, s, u_theta, z_theta, iota): N_g/(Q R^17) (straight-line program, leaf
    derivatives) equals the defect computed from the expanded Q = n_R^2 + R^2 D^2 + n_z^2 with
    invariance L u = n_R/D, L z = n_z/D imposed."""
    t0 = time.time()
    lv = leaves_poly(P)
    Qe = EF.padd(EF.pmul(P['nR'], P['nR']), EF.pmul(EF.pmul(Rpoly, Rpoly), EF.pmul(P['D'], P['D'])),
                 EF.pmul(P['nZ'], P['nZ']))
    Qe_u, Qe_z, Qe_f = EF.pdiff(Qe, 0), EF.pdiff(Qe, 1), EF.pphi(Qe)
    for (x0, zz, c, s, uth, zth, iota) in pts:
        x = (x0, zz, c, s)
        R = x0 + R0 if form == 'u' else x0
        v = {k: peval(p, x) for k, p in lv.items()}
        nd = qs_nodes(v, R, *num_ops())
        Ng = nd['N0'] + iota*(nd['N1']*uth + nd['N2']*zth)
        # direct route
        Q, Qu, Qz, Qf = (peval(p, x) for p in (Qe, Qe_u, Qe_z, Qe_f))
        assert Q == nd['Q'] and Qu == nd['Qu'] and Qz == nd['Qz'] and Qf == nd['Qf']
        Lu, Lz = v['nR']/v['D'], v['nZ']/v['D']
        F_u = (Qu*R - 16*Q)/R**17
        F_z, F_f = Qz/R**16, Qf/R**16
        BR, BP, BZ = v['nR']/R**8, v['D']/R**7, v['nZ']/R**8
        a = BR*uth + BZ*zth
        J = BR*Lu + BP*R + BZ*Lz
        G = ((1 + iota*a)*(F_u*Lu + F_z*Lz + F_f) - iota*J*(F_u*uth + F_z*zth))/J
        assert G == Ng/(Q*R**17), form
        assert J == Q/(R**8*v['D'])
    return len(pts), time.time() - t0


# ----------------------------------------------------------------------------------------------
# 3. numerics on torus C

def numpy_poly(p, X0, Z, C, S, np):
    """Float evaluation of a dict polynomial (slot 0 = R or u) on arrays."""
    out = np.zeros_like(X0)
    cache = {}

    def pw(arr, key, k):
        if (key, k) not in cache:
            cache[(key, k)] = arr**k
        return cache[(key, k)]
    for (a, b, c, d), q in p.items():
        out += float(q)*pw(X0, 'x', a)*pw(Z, 'z', b)*pw(C, 'c', c)*pw(S, 's', d)
    return out


def numerics(P_R, torus, n):
    import numpy as np
    import qs_defect as QD
    from dfield import ExactField, Evaluator
    d = json.load(open(torus))
    ex = ExactField()
    assert d['candidate_sha256'] == ex.sha
    ev = Evaluator(ex)
    iota = float(d['iota'])
    G = QD.torus_grid(d, n, n)
    R, z, phi = G['R'], G['z'], G['phi']
    Rt, zt = G['R_t'], G['z_t']
    Rf, zf = 2*G['R_p'], 2*G['z_p']
    LR, Lz = Rf + iota*Rt, zf + iota*zt
    C, S = np.cos(2*phi), np.sin(2*phi)
    lv = leaves_poly(P_R)
    v = {k: numpy_poly(p, R, z, C, S, np) for k, p in lv.items()}
    nd = qs_nodes(v, R, num_add, (lambda a, b: a*b), (lambda k, a: k*a))
    Ng = nd['N0'] + iota*(nd['N1']*Rt + nd['N2']*zt)
    G2 = Ng/(nd['Q']*R**17)                       # d_{phi_B}|B|^2
    g_poly = Ng/(2*nd['Q']**1.5*R**9)             # torusQADefect
    # the estimator (qs_defect.analyse, same formulas, central differences for grad|B|)
    BR, BP, BZ = ev.B_cyl(R, phi, z)
    f, fR, fp, fz = QD.normB_and_grad(ev, R, phi, z)
    a = BR*Rt + BZ*zt
    J = BR*LR + BP*R + BZ*Lz
    g_est = (1 + iota*a)*(fR*LR + fp + fz*Lz)/J - iota*(fR*Rt + fz*zt)
    # the discrepancy is the estimator's central-difference error (h^2 truncation, then roundoff)
    fd_scan = {}
    for h in (1e-4, 1e-5, 1e-6):
        _, hR, hp, hz = QD.normB_and_grad(ev, R, phi, z, h=h)
        gh = (1 + iota*a)*(hR*LR + hp + hz*Lz)/J - iota*(hR*Rt + hz*zt)
        fd_scan[str(h)] = float(np.abs(g_poly - gh).max())
    # flow-form identities at the torus points
    res = dict(
        fd_step_scan=fd_scan,
        grid=[n, n], iota=iota,
        B2_vs_Q_over_R16=float(np.abs(f*f - nd['Q']/R**16).max()),
        J_vs_Q_over_R8D=float(np.abs(J - nd['Q']/(R**8*v['D'])).max()),
        invariance=float(max(np.abs(v['D']*LR - v['nR']).max(), np.abs(v['D']*Lz - v['nZ']).max())),
        sup_g_poly=float(np.abs(g_poly).max()), sup_g_est=float(np.abs(g_est).max()),
        max_abs_diff=float(np.abs(g_poly - g_est).max()),
        rel_diff=float(np.abs(g_poly - g_est).max()/np.abs(g_est).max()),
        sup_dphiB_B2=float(np.abs(G2).max()),
        l1_g=QD.fourier_l1(g_poly), l1_dphiB_B2=QD.fourier_l1(G2),
        B_min=float(f.min()),
        l1_dphiB_B2_over_2Bmin=QD.fourier_l1(G2)/(2*float(f.min())),
        Q_range=[float(nd['Q'].min()), float(nd['Q'].max())],
        D_min=float(v['D'].min()),
        node_sup={k: float(np.abs(val).max()) for k, val in nd.items()},
    )
    return res


# ----------------------------------------------------------------------------------------------
# 4/5. sizes, Lean data

def sizes(P, Rpoly):
    lv = leaves_poly(P)
    nd = qs_nodes(lv, Rpoly, *poly_ops())
    out = {}
    for k in ('Q', 'Qu', 'Qz', 'Qf', 'PL', 'ML', 'N0', 'N1', 'N2'):
        p = nd[k]
        out[k] = dict(terms=len(p), deg0=max(e[0] for e in p), degz=max(e[1] for e in p),
                      degcs=max(e[2] + e[3] for e in p),
                      den_bits=max(q.denominator.bit_length() for q in p.values()))
    return out


def lean_data(Lu, Lr, sizes_info):
    hdr = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamFieldData

/-!
# The `φ`-derivatives of the flow-form polynomials of the Dommaschk target (generated file)

**Generated** by `scripts/dommaschk_kam/emit_qs.py` (N-34 module D3; do not edit by hand).

The formal `φ`-derivatives `phiS p = −2s ∂_c p + 2c ∂_s p` (`DkPoly.phiS`, `c = cos 2φ`,
`s = sin 2φ`) of the flow-form polynomials `D = R⁷B_φ`, `n_R = R⁸B_R`, `n_z = R⁸B_z` of
`Design/DommaschkKamFieldData`, as sparse polynomials (terms sorted by exponent):

* in the variables `(u, z, c, s)`, `u = R − R₀`: `dDf = ∂_φD`, `dnRf = ∂_φn_R`, `dnZf = ∂_φn_z`;
* in the variables `(R, z, c, s)` (the form the admissibility chain evaluates): `dDRf = ∂_φD`,
  `dnRhf = ∂_φ(n_R/R)`, `dnZRf = ∂_φn_z`.

They are the leaves `D_φ`, `n_{R,φ}`, `n_{z,φ}` of the straight-line program of the QA-defect
numerator `N_g` (`Design/DommaschkKamCQSPoly`). The generator checks them with the Python mirror of
the Lean operations; the kernel checks are in `DommaschkKamCQSPoly` (`dDf_eq`, …, `substR_dDRf`, …).
Term counts: ''' + ', '.join(f'`{k}` {len(v)}' for k, v in list(Lu.items()) + list(Lr.items())) + '''.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Design.DommaschkKam DkPoly

'''
    docs = dict(
        dDf='`∂_φD` in `(u, z, c, s)` (`= phiS dD`)', dnRf='`∂_φn_R` in `(u, z, c, s)` (`= phiS dnR`)',
        dnZf='`∂_φn_z` in `(u, z, c, s)` (`= phiS dnZ`)', dDRf='`∂_φD` in `(R, z, c, s)` (`= phiS dDR`)',
        dnRhf='`∂_φ(n_R/R)` in `(R, z, c, s)` (`= phiS dnRh`)',
        dnZRf='`∂_φn_z` in `(R, z, c, s)` (`= phiS dnZR`)')
    body = ''
    for k, v in list(Lu.items()) + list(Lr.items()):
        body += EF.lean_sp(k, docs[k], v) + '\n'
    body += 'end PlasmaLean.Design.DommaschkKamC\n'
    return hdr + body


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--no-write', action='store_true')
    ap.add_argument('--sizes-u', action='store_true', help='also expand N0..N2 in u-form (slow)')
    ap.add_argument('--n', type=int, default=256)
    ap.add_argument('--torus', default=DEF_TORUS)
    ap.add_argument('--out', default=None, help='write the report as JSON')
    args = ap.parse_args()
    report = {}
    t0 = time.time()
    report['symbolic'] = symbolic_check()
    print('1. symbolic (sympy) checks pass:', report['symbolic'], f'({time.time() - t0:.1f} s)')

    cand, V = EF.load()
    P_R, c0 = EF.build(V)
    P_u = {k: EF.subst_R(v, R0) for k, v in P_R.items()}
    Ru = EF.padd(EF.mono(q=R0), EF.mono(a=1))
    pts = [(Fr(1, 50), Fr(-1, 70), Fr(3, 5), Fr(4, 5), Fr(1, 90), Fr(-2, 77), Fr(-29, 120)),
           (Fr(-3, 100), Fr(1, 40), Fr(-5, 13), Fr(12, 13), Fr(-1, 33), Fr(1, 61), Fr(-1, 4)),
           (Fr(1, 7), Fr(1, 9), Fr(2, 3), Fr(-1, 5), Fr(3, 7), Fr(-4, 9), Fr(5, 11))]   # c, s free
    report['exact_u'] = exact_point_checks(P_u, Ru, pts, 'u')
    ptsR = [(p[0] + R0,) + p[1:] for p in pts]
    report['exact_R'] = exact_point_checks(P_R, EF.mono(a=1), ptsR, 'R')
    print('2. exact rational checks (straight-line program vs expanded Q) pass:',
          report['exact_u'], report['exact_R'])

    report['numerics'] = numerics(P_R, args.torus, args.n)
    print('3. torus C numerics:', json.dumps(report['numerics'], indent=1))
    assert min(report['numerics']['fd_step_scan'].values()) < 1e-8

    report['sizes_R'] = sizes(P_R, EF.mono(a=1))
    print('4. expanded sizes (R-form):', json.dumps(report['sizes_R']))
    if args.sizes_u:
        report['sizes_u'] = sizes(P_u, Ru)
        print('   expanded sizes (u-form):', json.dumps(report['sizes_u']))

    # 5. Lean data, checked with the Python mirror of DkPoly
    L = {k: EF.to_list(v) for k, v in P_u.items()}
    Lu = {'dDf': EF.l_phi(L['D']), 'dnRf': EF.l_phi(L['nR']), 'dnZf': EF.l_phi(L['nZ'])}
    # R-form base data exactly as DommaschkKamFieldData (dDR, dnRh = n_R/R, dnZR)
    nRh = {(e[0] - 1,) + e[1:]: q for e, q in P_R['nR'].items()}
    assert all(e[0] >= 0 for e in nRh)
    Lr = {'dDRf': EF.l_phi(EF.to_list(P_R['D'])), 'dnRhf': EF.l_phi(EF.to_list(nRh)),
          'dnZRf': EF.l_phi(EF.to_list(P_R['nZ']))}
    src = open(os.path.join(REPO, 'PlasmaLean', 'Design', 'DommaschkKamFieldData.lean')).read()
    import re

    def parse_sp(name):
        i = src.index(f'def {name} : SP := [')
        j = src.index(']\n', i)
        ts = re.findall(r'⟨mkRat \((-?\d+)\)\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩', src[i:j])
        return [(Fr(int(a), int(b)), int(c), int(d), int(e), int(f)) for a, b, c, d, e, f in ts]
    for nm, k in (('dD', 'D'), ('dnR', 'nR'), ('dnZ', 'nZ')):
        assert parse_sp(nm) == L[k], nm
    assert parse_sp('dDR') == EF.to_list(P_R['D'])
    assert parse_sp('dnRh') == EF.to_list(nRh)
    assert parse_sp('dnZR') == EF.to_list(P_R['nZ'])
    for k, v in list(Lu.items()) + list(Lr.items()):
        assert EF.is_sorted(v) and all(t[0] != 0 for t in v), k
    # the R-form and u-form derivatives agree under R = R0 + u (mirror of `substR`)
    for kr, ku, shift in (('dDRf', 'dDf', 0), ('dnRhf', 'dnRf', 1), ('dnZRf', 'dnZf', 0)):
        pr = {(t[1] + shift, t[2], t[3], t[4]): t[0] for t in Lr[kr]}
        assert EF.to_list(EF.subst_R(pr, R0)) == Lu[ku], kr
    # mirror of the Lean `substR` (foldr merge (mulMono ⟨q,0,b,c,d⟩ (RpowL a)) acc)
    Rl = [(R0, 0, 0, 0, 0), (Fr(1), 1, 0, 0, 0)]

    def RpowL(n):
        acc = [(Fr(1), 0, 0, 0, 0)]
        for _ in range(n):
            acc = EF.l_mul(Rl, acc)
        return acc

    def substR(p):
        acc = []
        for t in reversed(p):
            acc = EF.l_merge(EF.l_mulMono((t[0], 0, t[2], t[3], t[4]), RpowL(t[1])), acc)
        return acc
    assert substR(Lr['dDRf']) == Lu['dDf']
    assert substR(EF.l_mulMono((Fr(1), 1, 0, 0, 0), Lr['dnRhf'])) == Lu['dnRf']
    assert substR(Lr['dnZRf']) == Lu['dnZf']
    print('5. phi-derivative data:', {k: len(v) for k, v in list(Lu.items()) + list(Lr.items())},
          '(Lean-mirror phiS / substR checks pass)')
    if not args.no_write:
        open(OUT, 'w').write(lean_data(Lu, Lr, report['sizes_R']))
        print('wrote', OUT)
    report['seconds'] = time.time() - t0
    if args.out:
        json.dump(report, open(args.out, 'w'), indent=1, default=str)


if __name__ == '__main__':
    main()
