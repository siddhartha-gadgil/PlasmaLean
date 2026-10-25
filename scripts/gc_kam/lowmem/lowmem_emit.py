#!/usr/bin/env python3
"""Low-memory kernel checks for the family ball chains (untrusted generator).

Converts the generated check modules `Design/<PRE>Check<TAG><k>.lean` of one family
(`node3KN`, `norm3KN`, `center3KN` theorems, `Certificates/KronChebCompute`) into the low-memory
format of `Certificates/KronLowMemCompute` (`node3KS`, `norm3KS`, `center3KS` on the signed images
`KvS<T>`), and writes

  Design/<PRE>KvS<TAG>.lean        light: the signed images `KvS<T>` (one definition);
  Design/<PRE>CheckS<TAG><k>.lean  light: the low-memory checks `k<T>S_*`, `c<T>S_*` and the
                                   unchanged `ℓ¹` checks (default mode), or
  Design/<PRE>Check<TAG><k>.lean   the same, overwriting the old checks (`--inplace`);
  Design/<PRE>LowMem<TAG>.lean     heavy but cheap: `KvS<T>_toInt` and every original check
                                   theorem (same name, same statement) proved from the low-memory
                                   one by `node3KN_le_of_S`, `norm3KN_le_of_S`, `center3KN_le_of_S`
                                   (`Certificates/KronBallLowMem`). In default mode the theorems are
                                   in the sub-namespace `LowMem`; with `--inplace` they replace the
                                   old ones in the family namespace, so the chain modules only need
                                   to import `<PRE>LowMem<TAG>` instead of the check modules.

Nothing here is trusted: every generated statement is checked by Lean.

Usage:
  python3 scripts/gc_kam/lowmem/lowmem_emit.py PRE TAG [--inplace [--patch-chain]] [--only K1,...]
  python3 scripts/gc_kam/lowmem/lowmem_emit.py PRE TAG --test THEOREM ... [--out DIR]

  PRE  family prefix, e.g. RationalStellaratorGCMu, RationalStellaratorGCMu2,
       RationalStellaratorGCEw1, RationalStellaratorGCFam
  TAG  H or L

`--patch-chain` (with `--inplace`) adds `public import PlasmaLean.Design.<PRE>LowMem<TAG>` to
`Design/<PRE>Chain<TAG>.lean`, the only change the chain modules need. `--only` restricts the conversion to the listed check modules (the bridge then imports only
those). `--test` writes, for each named check theorem, a standalone (non-module) Lean file in DIR with a
local copy of `KvS<T>` and the low-memory check, for measuring memory with
`/usr/bin/time -l lake env lean DIR/<theorem>.lean` before migrating.
"""
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
DES = os.path.join(ROOT, 'PlasmaLean', 'Design')

HEADER = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

'''

def wrapdoc(text):
    """Wrap the paragraphs of a module docstring at 100 characters."""
    import textwrap
    out = []
    for para in text.strip('\n').split('\n\n'):
        lines = para.split('\n')
        if lines[0].startswith('* '):
            items, cur = [], []
            for ln in lines:
                if ln.startswith('* ') and cur:
                    items.append(' '.join(cur)); cur = []
                cur.append(ln.strip())
            items.append(' '.join(cur))
            out.append('\n'.join(textwrap.fill(it, 100, subsequent_indent='  ') for it in items))
        elif lines[0].startswith('#'):
            out.append(para)
        else:
            out.append(textwrap.fill(' '.join(l.strip() for l in lines), 100))
    return '\n\n'.join(out)


THM = re.compile(r'(?P<pre>(?:set_option [^\n]*\n)*/-- (?P<doc>[^\n]*?) -/\n)'
                 r'theorem (?P<name>\w+) : (?P<stmt>.*?) := by\n  decide \+kernel\n', re.S)


def check_modules(pre, tag):
    mods = []
    k = 1
    while os.path.exists(os.path.join(DES, '%sCheck%s%d.lean' % (pre, tag, k))):
        mods.append('%sCheck%s%d' % (pre, tag, k))
        k += 1
    if not mods:
        sys.exit('no check modules %sCheck%s*' % (pre, tag))
    return mods


def parse(mod):
    s = open(os.path.join(DES, mod + '.lean')).read()
    ns = re.search(r'^namespace (\S+)$', s, re.M).group(1)
    imports = re.findall(r'^public import (\S+)$', s, re.M)
    thms = [m.groupdict() for m in THM.finditer(s)]
    if len(thms) != len(re.findall(r'^theorem ', s, re.M)):
        sys.exit('%s: unexpected theorem format' % mod)
    return s, ns, imports, thms


def suffix(thms):
    for t in thms:
        m = re.match(r'(?:node3KN|norm3KN|center3KN)\b.*?\bKv(\w+)\b', t['stmt'])
        if m:
            return m.group(1)
    sys.exit('no Kronecker check found')


def kvs_def(T):
    return '''/-- **The signed Kronecker images of the variable polynomials** (`w ↦ 2^{b W R}`): stored
families with fast widths by `famS`, every other variable by its integer image `Kv%(T)s`. -/
def KvS%(T)s (b W R : Nat) (i : Nat) : SInt :=
  if kind%(T)s i = 6 ∧ bMin%(T)s i ≤ b ∧ wMin%(T)s i ≤ W then
    famS b W R N%(T)s M%(T)s D%(T)s (c0%(T)s i) (odd%(T)s i) dd%(T)s dr%(T)s dw%(T)s (fam%(T)s i)
  else SInt.ofInt (Kv%(T)s b W R i)
''' % {'T': T}


def low_stmt(stmt, T):
    """The low-memory statement and the kind of check (or None)."""
    for old, new, kind in (('node3KN', 'node3KS', 'n'), ('norm3KN', 'norm3KS', 'm'),
                           ('center3KN', 'center3KS', 'c')):
        if stmt.startswith(old + ' '):
            body = re.sub(r'\bKv%s\b' % T, 'KvS%s' % T, stmt[len(old):], count=1)
            return new + body, kind
    return stmt, None


def low_name(name, T):
    # k<T>_x -> k<T>S_x, c<T>_x -> c<T>S_x
    return re.sub(r'^([kc])%s_' % T, r'\g<1>%sS_' % T, name)


def emit_kvs(pre, tag, T, ns, kvmod):
    mod = '%sKvS%s' % (pre, tag)
    doc = wrapdoc('''# Low-memory Kronecker images (`Design/%s`)

The signed images `KvS%s` of the variables of `Design/%s` for the low-memory kernel checks
(`Certificates/KronLowMemCompute`). Their integer values are the images `Kv%s` (`KvS%s_toInt`,
`Design/%sLowMem%s`). Light module. Generated by `scripts/gc_kam/lowmem/lowmem_emit.py`.
''' % (kvmod, T, kvmod, T, T, pre, tag))
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % kvmod,
           'public import PlasmaLean.Certificates.KronLowMemCompute\n', '''
/-!
%s
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronLowMem

''' % (doc, ns), kvs_def(T), '\nend %s\n' % ns]
    open(os.path.join(DES, mod + '.lean'), 'w').write(''.join(out))
    return mod


def emit_check(pre, tag, T, mod, newmod, kvsmod, sub):
    s, ns, imports, thms = parse(mod)
    out = [HEADER]
    out += ['public import %s\n' % i for i in imports]
    out.append('public import PlasmaLean.Design.%s\n' % kvsmod)
    doc = wrapdoc('''# Low-memory kernel checks (`Design/%s`)

The checks of `Design/%s` in the low-memory format (`Certificates/KronLowMemCompute`): each `k*S_*`,
`c*S_*` theorem is one kernel evaluation of `node3KS`, `norm3KS` or `center3KS` on the signed images
`KvS%s`, with the original bound; the `ℓ¹` checks are unchanged%s. `Design/%sLowMem%s` derives the
original statements from them. Light module. Generated by `scripts/gc_kam/lowmem/lowmem_emit.py`.
''' % (mod, mod, T, '' if not sub else ' (all in the namespace `%s`)' % sub, pre, tag))
    out.append('''
/-!
%s
-/

@[expose] public section

-- check the theorems one at a time (bounded memory per process)
set_option Elab.async false

namespace %s%s

open PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronLowMem

''' % (doc, ns, '.' + sub if sub else ''))
    for t in thms:
        stmt, kind = low_stmt(t['stmt'], T)
        name = low_name(t['name'], T) if kind else t['name']
        pre_ = t['pre']
        if kind:
            pre_ = pre_.replace('/-- Kernel check', '/-- Low-memory kernel check')
        out.append('%stheorem %s : %s := by\n  decide +kernel\n\n' % (pre_, name, stmt))
    out.append('end %s%s\n' % (ns, '.' + sub if sub else ''))
    open(os.path.join(DES, newmod + '.lean'), 'w').write(''.join(out))
    return thms, ns


def ints(xs):
    return [x for x in xs]


def bridge_proof(t, T, kind):
    """The proof of an original check from its low-memory version."""
    a = t['stmt'].split('≤')[0].split()
    low = low_name(t['name'], T)
    if kind == 'n':
        # node3KN S N M D Wt Kv tr c' dd de n b W R Kw dr L fuel Ki Kj
        tr = a[7]
        m = re.match(r'node3KN \S+ \S+ \S+ \S+ \S+ \S+ \S+ (\(-?\d+ : Int\)) (.*)$',
                     t['stmt'].split('≤')[0].strip())
        c = m.group(1)
        dd, de, n, b, W, R, Kw, dr, L, fuel, Ki, Kj = [int(x) for x in m.group(2).split()]
        lname = 'l' + t['name'][1:]
        return ('node3KN_le_of_S box%s (l1%s %d) %s %d %d %d %s %d %d %d %d %d %d %d %d %d %d %d _\n'
                '    (kron%s %d %d %d) (KvS%s_toInt %d %d %d) (by decide +kernel) %s %s'
                % (T, T, R, tr, dd, de, n, c, W - 1, R - 1, Kw - 1, b, W, Kw, dr, L, fuel, Ki, Kj,
                   T, b, W, R, T, b, W, R, lname, low))
    if kind == 'm':
        # norm3KN Wt Kv N M tr (w) b W R Kw dr L fuel Ki Kj
        m = re.match(r'norm3KN \S+ \S+ \S+ \S+ (\S+) (\([^)]*\)) (.*)$',
                     t['stmt'].split('≤')[0].strip())
        tr, w = m.group(1), m.group(2)
        b, W, R, Kw, dr, L, fuel, Ki, Kj = [int(x) for x in m.group(3).split()]
        lname = 'l' + t['name'][1:]
        return ('norm3KN_le_of_S box%s (l1%s %d) %s %s %d %d %d %d %d %d %d %d %d %d %d _\n'
                '    (kron%s %d %d %d) (KvS%s_toInt %d %d %d) (by decide +kernel) %s %s'
                % (T, T, R, tr, w, W - 1, R - 1, Kw - 1, b, W, Kw, dr, L, fuel, Ki, Kj,
                   T, b, W, R, T, b, W, R, lname, low))
    # center3KN Kv N M i b W R Kw dr L fuel Ki Kj
    m = re.match(r'center3KN \S+ \S+ \S+ (.*)$', t['stmt'].split('≤')[0].strip())
    i, b, W, R, Kw, dr, L, fuel, Ki, Kj = [int(x) for x in m.group(1).split()]
    lname = 'cl' + t['name'][1:]
    return ('center3KN_le_of_S box%s (l1%s %d) %d %d %d %d %d %d %d %d %d _\n'
            '    (kron%s %d %d %d) (KvS%s_toInt %d %d %d) (by decide +kernel) %s %s'
            % (T, T, R, i, b, W, Kw, dr, L, fuel, Ki, Kj, T, b, W, R, T, b, W, R, lname, low))


def emit_bridge(pre, tag, T, ns, checks, kvsmod, inplace):
    mod = '%sLowMem%s' % (pre, tag)
    out = [HEADER, 'public import PlasmaLean.Design.%sEnv%s\n' % (pre, tag),
           'public import PlasmaLean.Certificates.KronBallLowMem\n',
           'public import PlasmaLean.Design.%s\n' % kvsmod]
    out += ['public import PlasmaLean.Design.%s\n' % m for m, _ in checks]
    sub = '' if inplace else 'LowMem'
    doc = wrapdoc('''# The low-memory kernel checks prove the original checks (`Design/%sCheck%s*`)

* `KvS%s_toInt`: the signed images `KvS%s` are the Kronecker images `Kv%s` (`famS_toInt`);
* every check theorem of `Design/%sCheck%s*`, with its original name and statement%s, proved from
  its low-memory version by `node3KN_le_of_S`, `norm3KN_le_of_S` or `center3KN_le_of_S`.

No heavy kernel evaluation (only degree conditions). Generated by
`scripts/gc_kam/lowmem/lowmem_emit.py`.
''' % (pre, tag, T, T, T, pre, tag, '' if inplace else ' (in the namespace `LowMem`)'))
    out.append('''
/-!
@DOC@
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronLowMem

/-- **The signed images are the Kronecker images.** -/
theorem KvS%s_toInt (b W R i : ℕ) : (KvS%s b W R i).toInt = Kv%s b W R i := by
  unfold KvS%s
  split_ifs with h
  · obtain ⟨hk, hb, hw⟩ := h
    have hi := lt_of_kind%s hk
    rw [Kv%s_k6 hk, ite_eq_left ⟨hb, hw⟩,
      famS_toInt (static%s i hi hk) ((dyn%s i hi hk).mono hb hw)]
  · exact SInt.toInt_ofInt _

'''.replace('@DOC@', doc) % (ns, T, T, T, T, T, T, T, T))
    if sub:
        out.append('namespace %s\n\n' % sub)
    for _, thms in checks:
        for t in thms:
            stmt, kind = low_stmt(t['stmt'], T)
            if not kind:
                continue
            out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
                       'set_option exponentiation.threshold 4096 in\n')
            out.append('/-- %s (from the low-memory check). -/\n' % t['doc'].rstrip('.'))
            out.append('theorem %s : %s :=\n  %s\n\n' % (t['name'], t['stmt'], bridge_proof(t, T, kind)))
    if sub:
        out.append('end %s\n\n' % sub)
    out.append('end %s\n' % ns)
    open(os.path.join(DES, mod + '.lean'), 'w').write(''.join(out))
    return mod


def emit_tests(pre, tag, names, outdir):
    os.makedirs(outdir, exist_ok=True)
    for mod in check_modules(pre, tag):
        s, ns, imports, thms = parse(mod)
        T = suffix(thms)
        for t in thms:
            if t['name'] not in names:
                continue
            stmt, kind = low_stmt(t['stmt'], T)
            src = ['import %s\n' % i for i in imports]
            src.append('import PlasmaLean.Certificates.KronLowMemCompute\n\nset_option Elab.async false\n\n')
            src.append('namespace %s\n\nopen PlasmaLean.Certificates.KronBallCheb '
                       'PlasmaLean.Certificates.KronLowMem\n\n' % ns)
            src.append(kvs_def(T) + '\n')
            src.append('set_option maxRecDepth 100000 in\ntheorem %s : %s := by\n  decide +kernel\n\n'
                       % (low_name(t['name'], T), stmt))
            src.append('end %s\n' % ns)
            open(os.path.join(outdir, t['name'] + '.lean'), 'w').write(''.join(src))
            print('wrote', os.path.join(outdir, t['name'] + '.lean'), '(from %s)' % mod)


def main():
    args = sys.argv[1:]
    if len(args) < 2:
        sys.exit(__doc__)
    pre, tag = args[0], args[1]
    if '--test' in args:
        i = args.index('--test')
        outdir = args[args.index('--out') + 1] if '--out' in args else '/tmp/lowmem_test'
        names = [a for a in args[i + 1:] if not a.startswith('--') and a != outdir]
        emit_tests(pre, tag, names, outdir)
        return
    inplace = '--inplace' in args
    mods = check_modules(pre, tag)
    if '--only' in args:
        keep = {int(k) for k in args[args.index('--only') + 1].split(',')}
        mods = [m for m in mods if int(m[len('%sCheck%s' % (pre, tag)):]) in keep]
    for m in mods:
        if 'KronLowMem' in open(os.path.join(DES, m + '.lean')).read():
            sys.exit('%s is already in the low-memory format; nothing to do' % m)
    _, ns, imports, thms0 = parse(mods[0])
    T = suffix(thms0)
    kvmod = '%sKv%s' % (pre, tag)
    if not os.path.exists(os.path.join(DES, kvmod + '.lean')):
        sys.exit('no module %s' % kvmod)
    kvsmod = emit_kvs(pre, tag, T, ns, kvmod)
    checks = []
    for mod in mods:
        k = int(mod[len('%sCheck%s' % (pre, tag)):])
        newmod = mod if inplace else '%sCheckS%s%d' % (pre, tag, k)
        thms, _ = emit_check(pre, tag, T, mod, newmod, kvsmod, '' if inplace else 'LowMem')
        checks.append((newmod, thms))
    bridge = emit_bridge(pre, tag, T, ns, checks, kvsmod, inplace)
    print('wrote %s, %d check modules, %s' % (kvsmod, len(checks), bridge))
    if inplace and '--patch-chain' in args:
        chain = os.path.join(DES, '%sChain%s.lean' % (pre, tag))
        c = open(chain).read()
        line = 'public import PlasmaLean.Design.%s\n' % bridge
        if line not in c:
            last = list(re.finditer(r'^public import [^\n]*\n', c, re.M))[-1]
            c = c[:last.end()] + line + c[last.end():]
            open(chain, 'w').write(c)
            print('patched', os.path.basename(chain))


if __name__ == '__main__':
    main()
