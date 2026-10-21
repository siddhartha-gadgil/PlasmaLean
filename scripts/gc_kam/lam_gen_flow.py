"""UNTRUSTED generator of the identity proofs of PlasmaLean/Design/RationalStellaratorGCMuFlow.lean
(the mu > 0 passing guiding-centre flow form): computes linear_combination certificates with sympy
and splices the lemmas into the file between the markers `-- BEGIN GENERATED` / `-- END GENERATED`.
Every certificate is re-checked by Lean (`linear_combination`)."""
import sys, sympy as sp
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/gc_kam')

FILE = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/RationalStellaratorGCMuFlow.lean'
S = sp.symbols
u = S('u')
R = 1 + u
X = '(xB u z)'
# ---------------------------------------------------------------- atoms (symbol, Lean expression)
ATOMS = []
def atom(name, lean):
    s_ = sp.Symbol(name)
    ATOMS.append((name, lean))
    return s_
D = atom('D', 'PolyExpr.eval %s KamNewton.Dp' % X)
nR = atom('nR', 'PolyExpr.eval %s KamNewton.nRp' % X)
nZ = atom('nZ', 'PolyExpr.eval %s KamNewton.nZp' % X)
def pdA(base, lean, i):
    return atom(base + {0: '0', 1: '1', 'ph': 'ph'}[i],
                ('pd %s %d %s' % (X, i, lean)) if i != 'ph' else ('phiD %s %s' % (X, lean)))
D0, D1, Dph = [pdA('D', 'KamNewton.Dp', i) for i in (0, 1, 'ph')]
nR0, nR1, nRph = [pdA('nR', 'KamNewton.nRp', i) for i in (0, 1, 'ph')]
nZ0, nZ1, nZph = [pdA('nZ', 'KamNewton.nZp', i) for i in (0, 1, 'ph')]
P = atom('P', 'PolyExpr.eval %s PuP' % X)
P0, P1, Pph = [pdA('P', 'PuP', i) for i in (0, 1, 'ph')]
P4 = atom('P4', 'PolyExpr.eval %s P4P' % X)
P40, P41, P4ph = [pdA('P4', 'P4P', i) for i in (0, 1, 'ph')]
Q = atom('Q', 'PolyExpr.eval %s QPP4P' % X)
Q0, Q1, Qph = [pdA('Q', 'QPP4P', i) for i in (0, 1, 'ph')]
E = atom('E', 'PolyExpr.eval %s EpP' % X)
E0, E1, Eph = [pdA('E', 'EpP', i) for i in (0, 1, 'ph')]
E4 = atom('E4', 'PolyExpr.eval %s E4P' % X)
E40, E41, E4ph = [pdA('E4', 'E4P', i) for i in (0, 1, 'ph')]
V = atom('V', 'PolyExprS.eval %s eV' % X)
V4 = atom('V4', 'PolyExprS.eval %s eV4' % X)
hA = atom('hA', 'algebraMap ℂ FA (1 / 2)')
KD = atom('KD', 'PolyExprS.eval %s eKD' % X)
KR = atom('KR', 'PolyExprS.eval %s eKR' % X)
KZ = atom('KZ', 'PolyExprS.eval %s eKZ' % X)
qv = atom('qv', 'PolyExprS.eval %s eq' % X)
qR = atom('qR', 'PolyExprS.eval %s eqR' % X)
qz = atom('qz', 'PolyExprS.eval %s eqz' % X)
qph = atom('qph', 'PolyExprS.eval %s eqph' % X)
W3 = atom('W3', 'PolyExprS.eval %s eW3' % X)

def dq(i):
    d = {0: (D0, nR0, nZ0), 1: (D1, nR1, nZ1), 'ph': (Dph, nRph, nZph)}[i]
    t = 2 * nR * d[1] + 2 * R ** 2 * D * d[0] + 2 * nZ * d[2]
    if i == 0:
        t += 2 * R * D ** 2
    return t
qraw = nR ** 2 + R ** 2 * D ** 2 + nZ ** 2
Qd = {0: Q0, 1: Q1, 'ph': Qph}
Ed = {0: E0, 1: E1, 'ph': Eph}
E4d = {0: E40, 1: E41, 'ph': E4ph}
def dBm(i):
    return Qd[i] * (V * V4) + Q * (-(hA * V ** 3) * Ed[i] * V4 + V * (-(hA * V4 ** 3) * E4d[i]))
Bm = Q * (V * V4)
W = P * V

# relations: name -> (lhs - rhs) polynomial ; Lean facts are introduced before `set`
RELS = {
    'h_Q': Q - qv * P * P4,
    'h_Q0': Q0 - (dq(0) * P * P4 + qv * P0 * P4 + qv * P * P40),
    'h_Q1': Q1 - (dq(1) * P * P4 + qv * P1 * P4 + qv * P * P41),
    'h_Qph': Qph - (dq('ph') * P * P4 + qv * Pph * P4 + qv * P * P4ph),
    'h_E0': E0 - (dq(0) * P ** 2 + 2 * qv * P * P0),
    'h_E1': E1 - (dq(1) * P ** 2 + 2 * qv * P * P1),
    'h_Eph': Eph - (dq('ph') * P ** 2 + 2 * qv * P * Pph),
    'h_E40': E40 - (8 * R ** 7 * P4 ** 2 + 2 * R ** 8 * P4 * P40),
    'h_E41': E41, 'h_E4ph': E4ph, 'h_P1': P1, 'h_Pph': Pph, 'h_P41': P41, 'h_P4ph': P4ph,
    'hV': V ** 2 * (1 + (qv * P ** 2 - 1)) - 1,
    'hV4': V4 ** 2 * (1 + (R ** 8 * P4 ** 2 - 1)) - 1,
    'h_half': 2 * hA - 1,
    'hK': KD * dq('ph') + KR * dq(0) + KZ * dq(1) - 8 * R ** 2 * qv * (R ** 2 * D * qz - nZ * qph),
    'hKD': KD - R ** 2 * (R * nZ * qR - 8 * nZ * qv - R * nR * qz),
    'hKR': KR - (R ** 5 * D * qz - R ** 3 * nZ * qph),
    'hKZ': KZ - (R ** 3 * nR * qph - R ** 5 * D * qR + 8 * R ** 4 * D * qv),
    'hqR': qR - dq(0), 'hqz': qz - dq(1), 'hqph': qph - dq('ph'),
    'hW3': W3 - (P * V) ** 3,
}
PIVOTS = [('h_Q0', Q0), ('h_Q1', Q1), ('h_Qph', Qph), ('h_Q', Q), ('h_E0', E0), ('h_E1', E1),
          ('h_Eph', Eph), ('h_E40', E40), ('h_E41', E41), ('h_E4ph', E4ph), ('h_P1', P1),
          ('h_Pph', Pph), ('h_P41', P41), ('h_P4ph', P4ph), ('hW3', W3), ('hKD', KD), ('hKR', KR),
          ('hKZ', KZ), ('hqR', qR), ('hqz', qz), ('hqph', qph)]


def certify(T, pivots, rels, gens):
    coef = {}
    T = sp.expand(T)
    for nm in pivots:
        p = dict(PIVOTS)[nm]
        if not T.has(p):
            continue
        r = sp.expand(RELS[nm])
        a = sp.Poly(r, p).coeff_monomial(p)
        assert a == 1, (nm, a)
        ex = sp.expand(p - r)
        Tn = sp.expand(T.subs(p, ex))
        q_, rem = sp.div(sp.expand(T - Tn), r, p)
        assert rem == 0, nm
        coef[nm] = sp.expand(coef.get(nm, 0) + q_)
        T = Tn
    if T != 0:
        G = [sp.expand(RELS[n]) for n in rels]
        Qs, rem = sp.reduced(T, G, *gens)
        assert sp.expand(rem) == 0, ('remainder', len(str(rem)))
        for n, qq in zip(rels, Qs):
            coef[n] = sp.expand(coef.get(n, 0) + qq)
    return coef


def lean(e):
    return sp.sstr(sp.expand(e), order='none').replace('**', '^')


def wrap(text, indent=4, width=99):
    out, cur = [], ''
    for t in text.split(' '):
        cand = (cur + ' ' + t) if cur else t
        if len(cand) + (indent if out else 2) > width and cur:
            out.append(cur)
            cur = t
        else:
            cur = cand
    out.append(cur)
    return ('\n' + ' ' * indent).join(out)


def lc_line(coef):
    parts = []
    for k, v in coef.items():
        if v == 0:
            continue
        parts.append('(%s) * %s' % (lean(v), k))
    return 'linear_combination ' + ' + '.join(parts)


FACTS = {
    'h_Q': 'QPP4_val', 'h_Q0': 'QPP4_d0', 'h_Q1': 'QPP4_d1', 'h_Qph': 'QPP4_dph',
    'h_E': 'E_val', 'h_E0': 'E_d0', 'h_E1': 'E_d1', 'h_Eph': 'E_dph', 'h_E40': 'E4_d0',
    'h_E41': 'E4_d1', 'h_E4ph': 'E4_dph', 'h_E4': 'E4_val', 'h_P1': 'P_d1', 'h_Pph': 'P_dph',
    'h_P41': 'P4_d1', 'h_P4ph': 'P4_dph'}


def facts_block(used):
    out = []
    for nm in ['h_Q', 'h_Q0', 'h_Q1', 'h_Qph', 'h_E', 'h_E0', 'h_E1', 'h_Eph', 'h_E4', 'h_E40', 'h_E41',
               'h_E4ph', 'h_P1', 'h_Pph', 'h_P41', 'h_P4ph']:
        if nm in used or (nm == 'h_E' and 'hV' in used) or (nm == 'h_E4' and 'hV4' in used):
            out.append('  have %s := %s (xB u z)' % (nm, FACTS[nm]))
    for nm, stmt in [('hq', 'gc_eval_eq u z'), ('hKD', 'gc_eval_eKD u z'), ('hKR', 'gc_eval_eKR u z'),
                     ('hKZ', 'gc_eval_eKZ u z'), ('hqR', 'gc_eval_eqR u z'), ('hqz', 'gc_eval_eqz u z'),
                     ('hqph', 'gc_eval_eqph u z'), ('hW3', 'gc_eval_eW3 u z'), ('hK', 'gc_gradK u z'),
                     ('h_half', 'half_rel')]:
        if nm in used or nm == 'hq':
            out.append('  have %s := %s' % (nm, stmt))
    return out


SETS = None


def set_line(n, l):
    t = '  set %s := %s with hdef_%s' % (n, l, n)
    if len(t) > 100:
        t = '  set %s := %s\n    with hdef_%s' % (n, l, n)
    return t


def sets_block():
    return [set_line(n, l) for n, l in ATOMS]


def lemma(name, doc, stmt, hyps, T, rels, gens, pre=(), maxhb=None):
    pivs = [p for p, _ in PIVOTS]
    co = certify(T, pivs, rels, gens)
    co = {k: v for k, v in co.items() if v != 0}
    used = set(co)
    lines = []
    if maxhb:
        lines.append('set_option maxHeartbeats %d in' % maxhb)
    lines.append('set_option linter.unusedSimpArgs false in')
    lines.append('/-- %s -/' % doc)
    lines.append('theorem %s (u z : FA)%s :\n    %s := by' % (name, hyps, stmt))
    lines += list(pre)
    lines += facts_block(used)
    lines.append('  simp only [xB_zero] at *')
    pass
    # rewrite raw q into qv in the polynomial facts
    rq = [n for n in ['h_Q', 'h_Q0', 'h_Q1', 'h_Qph', 'h_E', 'h_E0', 'h_E1', 'h_Eph'] if n in used or
          (n == 'h_E' and 'hV' in used)]
    if rq:
        lines.append('  rw [← hq] at %s' % ' '.join(rq))
    if 'hV' in used:
        lines.append('  rw [h_E] at hV')
    if 'hV4' in used:
        lines.append('  rw [h_E4] at hV4')
    lines += sets_block()
    lines.append('  ' + wrap(lc_line(co), 4))
    return '\n'.join(lines) + '\n'


HV = ('\n    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)'
      '\n    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1)')
GENS = [KD, nR, nRph, hA, V, V4, qv, P, P4, KZ, qz, qph, P0, P40, D, nZ, D0, D1, Dph, nR0, nR1, nZ0,
        nZ1, nZph, u]
DBM = {0: 'PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm', 1: 'PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm',
       'ph': 'PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm'}
PRE_DBM = ['  simp only [deriv_eBm]', '  simp only [deriv_single, deriv_phiDir]']


def gen_lemmas():
    out = []
    # gradBm
    T = dBm('ph') * KD + dBm(0) * KR + dBm(1) * KZ
    stmt = ('%s * PolyExprS.eval (xB u z) eKD +\n      %s * PolyExprS.eval (xB u z) eKR +\n      %s * '
            'PolyExprS.eval (xB u z) eKZ = 0' % (DBM['ph'], DBM[0], DBM[1]))
    out.append(lemma('gcMu_gradBm', '`∇|B| · κ = 0` (`∇|B| ⊥ B × ∇|B|²`), at points with the node identities.',
                     stmt, HV, T, ['hK', 'hV', 'hV4', 'h_half'], GENS, PRE_DBM))
    # bmY_a : Bm * YD = R dBm0 Xb - R^2 dBm1 Xa
    YD = hA * (W3 * KD); YR = hA * (W3 * KR); YZ = hA * (W3 * KZ)
    Xa = R * (W * nR); Xb = R * (R * (W * nZ)); Xc = R * (R * (W * D))
    PRE_C = PRE_DBM + ['  simp only [eval_eBm, eval_eYD, eval_eYR, eval_eYZ, eval_eXa, eval_eXb, eval_eXc]']
    for nm, lhsY, rhs, stmt_r, doc in [
        ('gcMu_bmY_a', YD, R * dBm(0) * Xb - R ** 2 * dBm(1) * Xa,
         '(1 + u) * %s * PolyExprS.eval (xB u z) eXb -\n      (1 + u) ^ 2 * %s * PolyExprS.eval (xB u z) eXa' % (DBM[0], DBM[1]),
         '`|B| · ½W³κ_D = R ∂_u|B| · R²W n_z − R² ∂_z|B| · R W n_R`\n(the `D`-component of `|B| ½W³κ = R³W ∇|B| × (…)`).'),
        ('gcMu_bmY_b', YZ, R ** 2 * dBm('ph') * Xa - R ** 3 * dBm(0) * Xc,
         '(1 + u) ^ 2 * %s * PolyExprS.eval (xB u z) eXa -\n      (1 + u) ^ 3 * %s * PolyExprS.eval (xB u z) eXc' % (DBM['ph'], DBM[0]),
         '`|B| · ½W³κ_z = R² ∂_φ|B| · R W n_R − R³ ∂_u|B| · R² W D`.'),
        ('gcMu_bmY_c', YR, -(R * dBm('ph') * Xb - R ** 3 * dBm(1) * Xc),
         '-((1 + u) * %s * PolyExprS.eval (xB u z) eXb -\n      (1 + u) ^ 3 * %s *\n        PolyExprS.eval (xB u z) eXc)' % (DBM['ph'], DBM[1]),
         '`|B| · ½W³κ_R = −(R ∂_φ|B| · R² W n_z − R³ ∂_z|B| · R² W D)`.')]:
        T = Bm * lhsY - rhs
        Yn = {'gcMu_bmY_a': 'eYD', 'gcMu_bmY_b': 'eYZ', 'gcMu_bmY_c': 'eYR'}[nm]
        stmt = 'PolyExprS.eval (xB u z) eBm * PolyExprS.eval (xB u z) %s =\n      %s' % (Yn, stmt_r)
        hy = HV if nm != 'gcMu_bmY_c' else HV.split('\n    (hV4')[0]
        out.append(lemma(nm, doc, stmt, hy, T, ['hV', 'hV4', 'h_half'], GENS, PRE_C))
    return out



# ---------------------------------------------------------------- the main identities
rA, lA, l2, Nn, Bmv = S('rA lA l2 N Bm')
YD_, YR_, YZ_ = S('YD YR YZ')
dYDph, dYR0, dYZ1 = S('dYDph dYR0 dYZ1')
Xa_, Xb_, Xc_ = S('Xa Xb Xc')
dXa1, dXaph, dXb0, dXbph, dXc0, dXc1 = S('dXa1 dXaph dXb0 dXbph dXc0 dXc1')
dB0, dB1, dBph = S('dB0 dB1 dBph')
Pa_, Pb_, Pa1, Paph, Pb0, Pbph = S('Pa Pb Pa1 Paph Pb0 Pbph')
dB = {0: dB0, 1: dB1, 'ph': dBph}
MATOMS = [('rA', 'algebraMap ℂ FA (ρ : ℂ)'), ('lA', 'algebraMap ℂ FA (lm : ℂ)'),
          ('l2', 'algebraMap ℂ FA ((lm : ℂ) / 2)'), ('N', 'PolyExprS.eval (xB u z) (eN lm)'),
          ('Bm', 'PolyExprS.eval (xB u z) eBm'),
          ('YD', 'PolyExprS.eval (xB u z) eYD'), ('YR', 'PolyExprS.eval (xB u z) eYR'),
          ('YZ', 'PolyExprS.eval (xB u z) eYZ'),
          ('dYDph', 'PolyExprS.deriv (xB u z) (phiDir (xB u z)) eYD'),
          ('dYR0', 'PolyExprS.deriv (xB u z) (Pi.single 0 1) eYR'),
          ('dYZ1', 'PolyExprS.deriv (xB u z) (Pi.single 1 1) eYZ'),
          ('Xa', 'PolyExprS.eval (xB u z) eXa'), ('Xb', 'PolyExprS.eval (xB u z) eXb'),
          ('Xc', 'PolyExprS.eval (xB u z) eXc'),
          ('dXa1', 'PolyExprS.deriv (xB u z) (Pi.single 1 1) eXa'),
          ('dXaph', 'PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXa'),
          ('dXb0', 'PolyExprS.deriv (xB u z) (Pi.single 0 1) eXb'),
          ('dXbph', 'PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXb'),
          ('dXc0', 'PolyExprS.deriv (xB u z) (Pi.single 0 1) eXc'),
          ('dXc1', 'PolyExprS.deriv (xB u z) (Pi.single 1 1) eXc'),
          ('dB0', 'PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm'),
          ('dB1', 'PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm'),
          ('dBph', 'PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm'),
          ('Pa', 'PolyExpr.eval (xB u z) KamNewton.Pap'), ('Pb', 'PolyExpr.eval (xB u z) KamNewton.Pbp'),
          ('Pa1', 'pd (xB u z) 1 KamNewton.Pap'), ('Paph', 'phiD (xB u z) KamNewton.Pap'),
          ('Pb0', 'pd (xB u z) 0 KamNewton.Pbp'), ('Pbph', 'phiD (xB u z) KamNewton.Pbp')]
Fv = (1 - l2 * Bmv) * Nn
Sv = (1 - lA * Bmv) * Nn
def dF(i):
    return (0 - (0 * Bmv + l2 * dB[i])) * Nn + (1 - l2 * Bmv) * (-(hA * Nn ** 3) * (-lA * dB[i]))
def dS(i):
    return (0 - (0 * Bmv + lA * dB[i])) * Nn + (1 - lA * Bmv) * (-(hA * Nn ** 3) * (-lA * dB[i]))
MRELS = {
    'gB': dBph * KD + dB0 * KR + dB1 * KZ,
    'hYD': YD_ - hA * (W3 * KD), 'hYR': YR_ - hA * (W3 * KR), 'hYZ': YZ_ - hA * (W3 * KZ),
    'cA': Bmv * YD_ - (R * dB0 * Xb_ - R ** 2 * dB1 * Xa_),
    'cB': Bmv * YZ_ - (R ** 2 * dBph * Xa_ - R ** 3 * dB0 * Xc_),
    'cC': Bmv * YR_ + (R * dBph * Xb_ - R ** 3 * dB1 * Xc_),
    'hN': Nn ** 2 * (1 + -lA * Bmv) - 1, 'h_half': 2 * hA - 1, 'hl2': 2 * l2 - lA,
}


def main_cert(T, base, o0, o1, X, rels, gens):
    """T = (1 - rA X) o0 + rA X o1 + rest; rest = explicit combination (rels is a dict) or reduced."""
    Rm = sp.expand(T - (1 - rA * X) * o0 - rA * X * o1)
    co = {'o0': sp.expand(1 - rA * X), 'o1': sp.expand(rA * X)}
    if isinstance(rels, dict):
        tot = sum(v * MRELS[k] for k, v in rels.items())
        assert sp.expand(Rm - tot) == 0, ('explicit certificate fails', sp.expand(Rm - tot))
        for k, v in rels.items():
            co[k] = sp.expand(v)
        return co
    if Rm != 0:
        rels0 = [n for n in rels if n not in ('h_half', 'hl2')]
        G = [sp.expand(MRELS[n]) for n in rels0]
        Qs, rem = sp.reduced(Rm, G, *gens)
        for n, qq in zip(rels0, Qs):
            co[n] = sp.expand(qq)
        rem = sp.expand(rem)
        if rem != 0:
            k, r_ = sp.div(rem, l2 - hA * lA, l2)
            assert sp.expand(r_) == 0, ('main remainder', rem)
            co['hl2'] = sp.expand(hA * k)
            co['h_half'] = sp.expand(-l2 * k)
        tot = sum(v * MRELS[n] for n, v in co.items() if n not in ('o0', 'o1'))
        assert sp.expand(Rm - tot) == 0
        for n, v in co.items():
            assert all(sp.Rational(c).q == 1 for c in sp.Poly(v, *sorted(v.free_symbols, key=str)).coeffs()) if v.free_symbols else True, n
    return co


MSETS = None


def main_lemma(name, doc, stmt, hyps, T, o0, o1, X, rels, gens, olds, extra_haves, simp_extra=''):
    co = main_cert(T, None, o0, o1, X, rels, gens)
    lines = ['set_option linter.unusedSimpArgs false in', '/-- %s -/' % doc, 'theorem %s (ρ lm : ℝ) (u z : FA)%s :\n    %s := by' % (name, hyps, stmt)]
    lines += olds
    lines += [l for l in extra_haves if l.split(':=')[0].split()[1] in co or 'hN' in l and 'hN' in co]
    lines.append('  simp only [phiDS_eq_deriv, pdS, gcDM, gcNRM, gcNZM, gcPaM, gcPbM, gcPcM, gcD_eq, gcNR_eq,')
    lines.append('    gcNZ_eq, gcPa_eq, gcPb_eq, gcPc_eq, eF, eS, PolyExprS.deriv, PolyExprS.eval,')
    lines.append('    PolyExprS.deriv_ofPoly, PolyExprS.eval_ofPoly, deriv_eN, deriv_single, deriv_phiDir, map_neg,')
    lines.append('    Complex.ofReal_one, Complex.ofReal_zero, map_one, map_zero,')
    lines.append('   %s] at *' % simp_extra[1:])
    lines += [set_line(n, l) for n, l in ATOMS + MATOMS]
    lines.append('  ' + wrap(lc_line(co), 4))
    return '\n'.join(lines) + '\n'


def gen_main():
    out = []
    MG = [dB0, dB1, dBph, l2, hA, Nn, lA, Bmv, YD_, YR_, YZ_, KD, KR, KZ, W3, Xa_, Xb_, Xc_, rA, u]
    # divFree
    cF = hA * lA * Nn ** 3 * (1 - l2 * Bmv) - l2 * Nn
    DMph = Dph + (0 * (Fv * YD_) + rA * (dF('ph') * YD_ + Fv * dYDph))
    NRM = nR + rA * (Fv * YR_)
    NRM0 = nR0 + (0 * (Fv * YR_) + rA * (dF(0) * YR_ + Fv * dYR0))
    NZM1 = nZ1 + (0 * (Fv * YZ_) + rA * (dF(1) * YZ_ + Fv * dYZ1))
    T = R * DMph - 3 * NRM + R * NRM0 + R * NZM1
    o0 = R * Dph - 3 * nR + R * nR0 + R * nZ1
    o1 = R * (Dph + dYDph) - 3 * (nR + YR_) + R * (nR0 + dYR0) + R * (nZ1 + dYZ1)
    olds = ['  have o1 := gc_divFree 1 u z hV', '  have o0 := gc_divFree 0 u z hV',
            '  have gB := gcMu_gradBm u z hV hV4', '  have hYD := eval_eYD (xB u z)',
            '  have hYR := eval_eYR (xB u z)', '  have hYZ := eval_eYZ (xB u z)']
    stmt = ('(1 + u) * phiDS (xB u z) (gcDM ρ lm) - 3 * PolyExprS.eval (xB u z) (gcNRM ρ lm) +\n'
            '      (1 + u) * pdS (xB u z) 0 (gcNRM ρ lm) + (1 + u) * pdS (xB u z) 1 (gcNZM ρ lm) = 0')
    out.append(main_lemma('gcMu_divFree', '**Divergence-free identity** of the `μ > 0` passing flow form.',
                          stmt, HV, T, o0, o1, Fv, {'gB': rA * R * cF * hA * W3, 'hYD': rA * R * cF * dBph,
                          'hYR': rA * R * cF * dB0, 'hYZ': rA * R * cF * dB1}, MG, olds, [],
                          ', zero_mul, mul_zero, add_zero, zero_add, sub_zero, one_mul'))
    # flux_a
    PbM = Pb_ - rA * (Sv * Xb_)
    PbM0 = Pb0 - (0 * (Sv * Xb_) + rA * (dS(0) * Xb_ + Sv * dXb0))
    PaM1 = Pa1 - (0 * (Sv * Xa_) + rA * (dS(1) * Xa_ + Sv * dXa1))
    DM = D + rA * (Fv * YD_)
    T = R * PbM0 - 2 * PbM - R ** 2 * PaM1 - DM
    o0 = R * Pb0 - 2 * Pb_ - R ** 2 * Pa1 - D
    o1 = R * (Pb0 - dXb0) - 2 * (Pb_ - Xb_) - R ** 2 * (Pa1 - dXa1) - (D + YD_)
    HH = ['  have hN := hN', '  have h_half := half_rel', '  have hl2 := half_lm lm']
    olds = ['  have o1 := gc_flux_a 1 u z hV', '  have o0 := gc_flux_a 0 u z hV',
            '  have cA := gcMu_bmY_a u z hV hV4', '  have h_half := half_rel', '  have hl2 := half_lm lm']
    stmt = ('(1 + u) * pdS (xB u z) 0 (gcPbM ρ lm) - 2 * PolyExprS.eval (xB u z) (gcPbM ρ lm) -\n'
            '      (1 + u) ^ 2 * pdS (xB u z) 1 (gcPaM ρ lm) = PolyExprS.eval (xB u z) (gcDM ρ lm)')
    out.append(main_lemma('gcMu_flux_a', '**Flux primitive identity** (a) of the `μ > 0` passing flow form.',
                          stmt, HV + HN, T, o0, o1, Sv, ['cA', 'hN', 'h_half', 'hl2'], MG, olds, [],
                          ', zero_mul, mul_zero, add_zero, zero_add, sub_zero, one_mul'))
    # flux_b
    PaMph = Paph - (0 * (Sv * Xa_) + rA * (dS('ph') * Xa_ + Sv * dXaph))
    PcM0 = 0 - (0 * (Sv * Xc_) + rA * (dS(0) * Xc_ + Sv * dXc0))
    NZM = nZ + rA * (Fv * YZ_)
    T = R ** 2 * PaMph - R ** 3 * PcM0 - NZM
    o0 = R ** 2 * Paph - nZ
    o1 = R ** 2 * (Paph - dXaph) - R ** 3 * (0 - dXc0) - (nZ + YZ_)
    olds = ['  have o1 := gc_flux_b 1 u z hV', '  have o0 := gc_flux_b 0 u z hV',
            '  have cB := gcMu_bmY_b u z hV hV4', '  have h_half := half_rel', '  have hl2 := half_lm lm']
    stmt = ('(1 + u) ^ 2 * phiDS (xB u z) (gcPaM ρ lm) - (1 + u) ^ 3 * pdS (xB u z) 0 (gcPcM ρ lm) =\n'
            '      PolyExprS.eval (xB u z) (gcNZM ρ lm)')
    out.append(main_lemma('gcMu_flux_b', '**Flux primitive identity** (b) of the `μ > 0` passing flow form.',
                          stmt, HV + HN, T, o0, o1, Sv, ['cB', 'hN', 'h_half', 'hl2'], MG, olds, [],
                          ', zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, one_mul'))
    # flux_c
    PbMph = Pbph - (0 * (Sv * Xb_) + rA * (dS('ph') * Xb_ + Sv * dXbph))
    PcM1 = 0 - (0 * (Sv * Xc_) + rA * (dS(1) * Xc_ + Sv * dXc1))
    NRM = nR + rA * (Fv * YR_)
    T = R * PbMph - R ** 3 * PcM1 + NRM
    o0 = R * Pbph + nR
    o1 = R * (Pbph - dXbph) - R ** 3 * (0 - dXc1) + (nR + YR_)
    olds = ['  have o1 := gc_flux_c 1 u z', '  have o0 := gc_flux_c 0 u z',
            '  have cC := gcMu_bmY_c u z hV', '  have h_half := half_rel', '  have hl2 := half_lm lm']
    stmt = ('(1 + u) * phiDS (xB u z) (gcPbM ρ lm) - (1 + u) ^ 3 * pdS (xB u z) 1 (gcPcM ρ lm) =\n'
            '      -PolyExprS.eval (xB u z) (gcNRM ρ lm)')
    out.append(main_lemma('gcMu_flux_c', '**Flux primitive identity** (c) of the `μ > 0` passing flow form.',
                          stmt, HV.split('\n    (hV4')[0] + HN, T, o0, o1, Sv, ['cC', 'hN', 'h_half', 'hl2'], MG, olds, [],
                          ', zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, one_mul'))
    return out


HN = ('\n    (hN : PolyExprS.eval (xB u z) (eN lm) ^ 2 * (1 + -algebraMap ℂ FA (lm : ℂ) *'
      '\n      PolyExprS.eval (xB u z) eBm) = 1)')

if __name__ == '__main__':
    lem = gen_lemmas() + gen_main()
    s = open(FILE).read()
    a = s.index('-- BEGIN GENERATED')
    b = s.index('-- END GENERATED')
    s = s[:a] + '-- BEGIN GENERATED\n\n' + '\n'.join(lem) + '\n' + s[b:]
    open(FILE, 'w').write(s)
    print('ok')
