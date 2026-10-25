"""UNTRUSTED helper (pitch cell pipeline, see lc.py): exact validation of the bounds that the
generators write into the Lean modules Adm / Maj, against the rational lists that are emitted to
Lean (the `def B?Ml : List ℚ` / `E?Ml` literals of the Env modules).

Everything is recomputed with `fractions.Fraction` from the emitted Lean TEXT (not from the Python
data the generators used), so a wrong or stale constant, or a corrupted textual substitution, fails
here, before the Lean files are written, instead of in a Lean build hours later.

Checked:
  * every bound fact `show LHS ≤ RHS by ...` of the Adm module (the `qle (show ...)` facts) and every
    `fb (v I ...) (q := Q) ...` fact (`BLM I + ELM I ≤ Q`);
  * the torus constants `auM, azM, aRtM, aztM, aLRM, aLzM` of Adm dominate the emitted ball data of
    the high-resolution chain (`‖u‖ = BHM 4 + EHM 4`, ...), and equal the KAM constants `C` of the
    majorant script when given;
  * the bounds `aTQ` of the Maj module dominate these constants plus the Newton budget
    (`a0 + 3 μ`, the condition `cM_avecμ`).

Usage (stand-alone, on Lean files):
  python validate.py ENV_H.lean ENV_L.lean ADM.lean [MAJ.lean]
"""
import re
import sys
from fractions import Fraction as Fr

MU = Fr(1, 10 ** 11)
# variable indices of the high-resolution chain used by the Adm template (RationalStellaratorGCFamAdm)
H_IDX = {'U': 4, 'Z': 5, 'LRx': 6, 'LZx': 7, 'thU': 8, 'thZ': 9}


# ------------------------------------------------------------------ exact evaluation of Lean terms
TOK = re.compile(r'\s*(?:(\d+)|([A-Za-z_][A-Za-z0-9_]*)|(ℚ|ℝ)|(.))')


def tokens(s):
    out = []
    for m in TOK.finditer(s):
        num, ident, ty, op = m.groups()
        if num is not None:
            out.append(('n', int(num)))
        elif ident is not None:
            out.append(('i', ident))
        elif ty is not None:
            out.append(('t', ty))
        elif op is not None and not op.isspace():
            out.append(('o', op))
    return out


class Ev:
    """Recursive-descent evaluator of rational Lean terms: literals, `+ - * / ^`, parentheses,
    type ascriptions `(t : ℚ)` and list lookups `BHM i` (`= BHMl.getD i 0`)."""

    def __init__(self, lists):
        self.lists = lists

    def __call__(self, s):
        self.t, self.k = tokens(s), 0
        v = self.add()
        assert self.k == len(self.t), ('trailing tokens', s, self.t[self.k:])
        return v

    def peek(self):
        return self.t[self.k] if self.k < len(self.t) else (None, None)

    def eat(self, kind, val=None):
        tk = self.peek()
        assert tk[0] == kind and (val is None or tk[1] == val), ('parse error', tk, kind, val)
        self.k += 1
        return tk[1]

    def add(self):
        v = self.mul()
        while self.peek() in (('o', '+'), ('o', '-')):
            op = self.eat('o')
            w = self.mul()
            v = v + w if op == '+' else v - w
        return v

    def mul(self):
        v = self.unary()
        while self.peek() in (('o', '*'), ('o', '/')):
            op = self.eat('o')
            w = self.unary()
            v = v * w if op == '*' else v / w
        return v

    def unary(self):
        if self.peek() == ('o', '-'):
            self.eat('o')
            return -self.unary()
        return self.pow()

    def pow(self):
        b = self.atom()
        if self.peek() == ('o', '^'):
            self.eat('o')
            e = self.unary()          # right associative
            assert e.denominator == 1 and e >= 0, ('exponent', e)
            return b ** int(e)
        return b

    def atom(self):
        kind, val = self.peek()
        if kind == 'n':
            self.k += 1
            return Fr(val)
        if kind == 'i':
            self.k += 1
            name = val
            assert name + 'l' in self.lists, ('unknown list function', name)
            i = self.eat('n')
            lst = self.lists[name + 'l']
            return lst[i] if i < len(lst) else Fr(0)
        if (kind, val) == ('o', '('):
            self.k += 1
            v = self.add()
            if self.peek() == ('o', ':'):
                self.eat('o')
                self.eat('t')
            self.eat('o', ')')
            return v
        raise AssertionError(('parse error at', self.peek()))


def split_top(s, sep=','):
    """split at top-level occurrences of `sep` (outside parentheses/brackets)."""
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


LIST_DEF = re.compile(r'def (\w+l) : List ℚ :=\s*\[(.*?)\]\n', re.S)


def parse_lists(*texts):
    """the `def NAMEl : List ℚ := [...]` literals of Lean module texts, as lists of Fractions."""
    ev = Ev({})
    out = {}
    for txt in texts:
        for name, body in LIST_DEF.findall(txt):
            assert name not in out, ('duplicate list', name)
            out[name] = [ev(x) for x in split_top(body)]
    return out


# ------------------------------------------------------------------ the checks
SHOW = re.compile(r'show (.+?) by (?:decide \+kernel|decide_cbv|norm_num[^)]*|rfl)\)')
FB = re.compile(r'fb \(v (\d+) \(by norm_num\)\) \(q := ([^)]*)\)')


def check_bound_facts(adm, lists):
    """every `show A ≤ B by ...` and `fb (v i ..) (q := Q)` fact of the Adm text holds exactly."""
    ev = Ev(lists)
    bad, n = [], 0
    for lno, line in enumerate(adm.split('\n'), 1):
        for st in SHOW.findall(line):
            if '≤' not in st or '∀' in st:
                continue
            parts = st.split(' ≤ ')
            assert len(parts) == 2, ('cannot parse bound fact', lno, st)
            a, b = ev(parts[0]), ev(parts[1])
            n += 1
            if not a <= b:
                bad.append('line %d: %s  (LHS = %s ~ %.6g > RHS = %s ~ %.6g)' % (lno, st, a, float(a), b, float(b)))
        for i, q in FB.findall(line):
            n += 1
            a, b = ev('BLM %s + ELM %s' % (i, i)), ev(q)
            if not a <= b:
                bad.append('line %d: BLM %s + ELM %s ≤ %s  (%.6g > %.6g)' % (lno, i, i, q, float(a), float(b)))
    assert not bad, 'FALSE emitted bound facts:\n  ' + '\n  '.join(bad)
    return n


def adm_constants(adm):
    ev = Ev({})
    out = {}
    for nm in ['auM', 'azM', 'aRtM', 'aztM', 'aLRM', 'aLzM']:
        m = re.search(r'def %s : ℝ := (.*?) \+ μM\n' % nm, adm)
        assert m, ('constant not found', nm)
        out[nm] = ev(m.group(1))
    return out


def maj_aTQ(maj):
    m = re.search(r'def aTQ : Fin 6 → ℚ :=\s*!\[(.*?)\]\n', maj, re.S)
    assert m, 'aTQ not found'
    ev = Ev({})
    v = [ev(x) for x in split_top(m.group(1))]
    assert len(v) == 6
    return v


def check_constants(adm, lists, maj=None, C=None, idx=None):
    """the torus constants of Adm against the emitted ball data (and C, aTQ)."""
    idx = idx or H_IDX
    ev = Ev(lists)
    K = adm_constants(adm)
    need = {'auM': 'BHM %d + EHM %d' % (idx['U'], idx['U']),
            'azM': 'BHM %d + EHM %d' % (idx['Z'], idx['Z']),
            'aRtM': 'BHM %d' % idx['thU'], 'aztM': 'BHM %d' % idx['thZ'],
            'aLRM': '(BHM %d + EHM %d) / 2 ^ 96' % (idx['LRx'], idx['LRx']),
            'aLzM': '(BHM %d + EHM %d) / 2 ^ 96' % (idx['LZx'], idx['LZx'])}
    bad = []
    for nm, expr in need.items():
        v = ev(expr)
        if not v <= K[nm]:
            bad.append('%s = %s < %s = %s' % (nm, K[nm], expr, v))
    if C is not None:
        for nm, key in [('auM', 'au0'), ('azM', 'az0'), ('aRtM', 'aRt0'), ('aztM', 'azt0'),
                        ('aLRM', 'aLR0'), ('aLzM', 'aLz0')]:
            if K[nm] != Fr(C[key]):
                bad.append('%s = %s in Adm but %s = %s in the majorant constants' % (nm, K[nm], key, C[key]))
    if C is not None:
        # the remaining constants of `cM` (field bounds, D/W/T bounds, initial error)
        ev0 = Ev({})
        for pat, val in [(r'  bD := (.*)\n', C['fb']['Dt']), (r'  bDu := (.*)\n', C['fb']['Dtu']),
                         (r'  bDz := (.*)\n', C['fb']['Dtz']), (r'  bnR := (.*)\n', C['fb']['nRt']),
                         (r'  bnRu := (.*)\n', C['fb']['nRtu']), (r'  bnRz := (.*)\n', C['fb']['nRtz']),
                         (r'  bnZ := (.*)\n', C['fb']['nZt']), (r'  bnZu := (.*)\n', C['fb']['nZtu']),
                         (r'  bnZz := (.*)\n', C['fb']['nZtz']), (r'  cKb := (.*)\n', C['cKb']),
                         (r'  cLb := (.*)\n', C['cLb']), (r'def sDM : ℝ := (.*)\n', C['sD']),
                         (r'def sWM : ℝ := (.*)\n', C['sW']), (r'def tTM : ℝ := (.*)\n', C['tT']),
                         (r'def τM : ℝ := (.*)\n', C['tau']), (r'def e0M : ℝ := (.*)\n', C['e0'])]:
            m = re.search(pat, adm)
            assert m, ('constant not found', pat)
            if ev0(m.group(1)) != Fr(val):
                bad.append('%s = %s in Adm but %s in the majorant constants' % (pat.split(':')[0].strip(), m.group(1), val))
    if maj is not None:
        a = maj_aTQ(maj)
        for i, nm in [(0, 'auM'), (1, 'azM'), (4, 'aLRM'), (5, 'aLzM')]:
            if not K[nm] + 3 * MU <= a[i]:
                bad.append('aTQ %d = %s < %s + 3 μ' % (i, a[i], nm))
    assert not bad, 'inconsistent constants:\n  ' + '\n  '.join(bad)
    return K


def to_decide_cbv(txt, name='module'):
    """the small facts of the Adm/Exact templates without `decide +kernel` (policy of 25 October
    2026): bound facts `show a ≤ q by decide +kernel`, side conditions `(by decide +kernel)` and the
    two torsion-average entries (`  decide +kernel` on its own line) are proved by `decide_cbv`."""
    txt = txt.replace('(by decide +kernel)', '(by decide_cbv)').replace('  decide +kernel\n', '  decide_cbv\n')
    txt = txt.replace('by decide +kernel)', 'by decide_cbv)')
    left = re.findall(r'.*\bdecide\b(?!_).*', txt)
    assert not left, ('decide left in %s' % name, left[:5])
    return txt


def validate(env_h, env_l, adm, maj=None, C=None, idx=None):
    lists = parse_lists(env_h, env_l)
    for nm in ['BHMl', 'EHMl', 'BLMl', 'ELMl']:
        assert nm in lists, ('list not found', nm)
    n = check_bound_facts(adm, lists)
    K = check_constants(adm, lists, maj, C, idx)
    assert n > 20, ('too few bound facts found: the Adm format changed?', n)
    return n, K


if __name__ == '__main__':
    rd = lambda p: open(p).read()
    a = sys.argv[1:]
    n, K = validate(rd(a[0]), rd(a[1]), rd(a[2]), rd(a[3]) if len(a) > 3 else None)
    print('validated %d bound facts; constants %s' % (n, {k: str(v) for k, v in K.items()}))
