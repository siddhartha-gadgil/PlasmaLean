#!/usr/bin/env python3
"""Kronecker ball checks as explicit proof terms (untrusted generator, Phase 16).

Converts the low-memory check modules `Design/<PRE>Check<TAG><k>.lean` of one family
(`node3KS`, `norm3KS`, `center3KS` theorems proved by `decide +kernel`,
`Certificates/KronLowMemCompute`) into the proof-term format of `Certificates/KronProof`:

* every `node3KS`/`norm3KS`/`center3KS … ≤ Kb` check is proved by `kron_proof` (signed-image,
  reading and comparison certificate, `chebKV_le_of_cert`);
* every other check, a strict bound `a < c` on natural numbers (the `ℓ¹` checks `nodeL1N …`,
  `L<T> i`, `ExN.majN …`), is proved by `kron_lt` (one kernel fact `Nat.ble (a + 1) c = true`).

The statements, names and namespaces are unchanged, so nothing downstream changes. A check module
gains `public import PlasmaLean.Certificates.KronProof` and a `meta import` of each of its imports
(the tactic evaluates the witness from the data definitions at elaboration time).

With `--inplace` the remaining `decide +kernel` side conditions of the family's bridge
`Design/<PRE>LowMem<TAG>` (`nodeDims3N`, …), chain `Design/<PRE>Chain<TAG>` (degree conditions,
image equations, rational bounds, list conditions), environment `Design/<PRE>Env<TAG>` and output
module `Design/<PRE>Out<TAG>` are replaced by `kernel_fact` (`Certificates/KernelFact`: explicit
proof terms with kernel-fact leaves).

Check modules still in the two-dimensional format (`nodeK`, `normK`, `centerK` of
`Certificates/KronBallGrid`: the `Torus` and `NegTorus` families) are converted by `convert2d`:
every such check is proved by `kron2_proof` (`Certificates/KronProof2D`: block sums of the digit
reading `pdig` as kernel facts, default blocks of `2^3` rows, `--block D` to change), every strict
`ℓ¹` bound by `kron_lt`.

Nothing here is trusted: every generated proof is checked by the Lean kernel.

Usage:
  python3 scripts/gc_kam/proofterm/proofterm_emit.py PRE TAG [--only K1,...] [--inplace]
          [--block D] [--out DIR]

  PRE  family prefix, e.g. RationalStellaratorGCMu, RationalStellaratorGCEw1
  TAG  H or L

Default: writes `Design/<PRE>CheckP<TAG><k>.lean` with the theorems in the sub-namespace
`ProofTerm` (side by side with the old modules, for measuring); `--out DIR` writes there instead.
`--inplace`: rewrites `Design/<PRE>Check<TAG><k>.lean` itself and patches the bridge and the chain
(the migration step; files already converted are left alone, so it can be rerun).
`--block D`: block level of the reading certificate (`kron_proof D`, default 9 = 512 rows).

Planning (for scripts/workstation/tasks/proofterm-migrate.sh):
  python3 scripts/gc_kam/proofterm/proofterm_emit.py --plan modules|entrypoints|outputs|tags PRE...
prints the Lean modules to build (dependencies first: `KronProof`, `KernelFact`, then per family
`KvS<T>`, the check modules, `LowMem<T>`, `Chain<T>` and every module up to the family's top
theorem module that imports them), the top theorems, the files rewritten by `--inplace`, or the
tags `H`/`L` of each family.
"""
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
DES = os.path.join(ROOT, 'PlasmaLean', 'Design')

THM = re.compile(r'(?P<pre>(?:set_option [^\n]*\n)*)(?P<doc>/-- [^\n]*? -/\n)'
                 r'theorem (?P<name>\w+) : (?P<stmt>.*?) := by\n  decide \+kernel\n', re.S)
BIG = ('node3KS ', 'norm3KS ', 'center3KS ')


def check_modules(pre, tag):
    mods, k = [], 1
    while os.path.exists(os.path.join(DES, '%sCheck%s%d.lean' % (pre, tag, k))):
        mods.append(k)
        k += 1
    if not mods:
        sys.exit('no check modules %sCheck%s*' % (pre, tag))
    return mods


def convert(src, mod, block, sub):
    """The proof-term version of the source of one low-memory check module."""
    if 'KronLowMem' not in src:
        sys.exit('%s: not in the low-memory format (run lowmem_emit.py first)' % mod)
    if 'kron_proof' in src or 'kron_lt' in src:
        return None
    imports = re.findall(r'^public import (\S+)$', src, re.M)
    n_thm = len(re.findall(r'^theorem ', src, re.M))
    thms = list(THM.finditer(src))
    if len(thms) != n_thm:
        sys.exit('%s: unexpected theorem format' % mod)
    tac = 'kron_proof' if block == 9 else 'kron_proof %d' % block

    def rep(m):
        stmt = m.group('stmt')
        if stmt.startswith(BIG):
            proof = tac
        elif re.search(r'\s<\s', stmt) and '≤' not in stmt:
            proof = 'kron_lt'
        else:
            sys.exit('%s: no proof-term rule for %s' % (mod, m.group('name')))
        opts = ''.join(l + '\n' for l in m.group('pre').splitlines()
                       if 'maxRecDepth' not in l)
        doc = m.group('doc').replace('/-- Low-memory kernel check', '/-- Proof-term check') \
                            .replace('/-- Kernel check', '/-- Proof-term check')
        return '%s%stheorem %s : %s := by\n  %s\n' % (opts, doc, m.group('name'), stmt, proof)

    out = THM.sub(rep, src)
    last = list(re.finditer(r'^public import [^\n]*\n', out, re.M))[-1]
    extra = 'public import PlasmaLean.Certificates.KronProof\n' + \
        ''.join('meta import %s\n' % i for i in imports)
    out = out[:last.end()] + extra + out[last.end():]
    out = re.sub(r'/-!\n# .*?-/', '''/-!
# Kronecker ball checks as proof terms (`Design/%s`)

Each `node3KS`, `norm3KS`, `center3KS` check is proved by an explicit certificate built by
`kron_proof` (`Certificates/KronProof`: signed image, digit reading, final comparison), each `ℓ¹`
check by the kernel fact `Nat.ble (a + 1) c = true` (`kron_lt`); no `decide`. The statements are
those of the low-memory checks. Light module. Generated by
`scripts/gc_kam/proofterm/proofterm_emit.py`.
-/''' % mod, out, count=1, flags=re.S)
    out = re.sub(r'^open (PlasmaLean\.Certificates\.KronBallCheb PlasmaLean\.Certificates\.KronLowMem)$',
                 r'open \1\n  PlasmaLean.Certificates.KronProof', out, count=1, flags=re.M)
    if sub:
        out = re.sub(r'^namespace (\S+)$', r'namespace \1.%s' % sub, out, count=1, flags=re.M)
        out = re.sub(r'^end (\S+)\n*$', r'end \1.%s\n' % sub, out, count=1, flags=re.M)
    return out


BIG2D = ('nodeK ', 'normK ', 'centerK ')


def convert2d(src, mod, block, sub):
    """The proof-term version of a two-dimensional check module (`nodeK`, `normK`, `centerK` of
    `Certificates/KronBallGrid`; the `Torus` and `NegTorus` families): each such check is proved by
    `kron2_proof` (`Certificates/KronProof2D`), each strict `ℓ¹` bound by `kron_lt`."""
    if 'kron2_proof' in src or 'kron_lt' in src:
        return None
    imports = re.findall(r'^public import (\S+)$', src, re.M)
    n_thm = len(re.findall(r'^theorem ', src, re.M))
    thms = list(THM.finditer(src))
    if len(thms) != n_thm:
        sys.exit('%s: unexpected theorem format' % mod)
    tac = 'kron2_proof' if block == 3 else 'kron2_proof %d' % block

    def rep(m):
        stmt = m.group('stmt')
        if stmt.startswith(BIG2D):
            proof = tac
        elif re.search(r'\s<\s', stmt) and '≤' not in stmt:
            proof = 'kron_lt'
        else:
            sys.exit('%s: no proof-term rule for %s' % (mod, m.group('name')))
        opts = ''.join(l + '\n' for l in m.group('pre').splitlines()
                       if 'maxRecDepth' not in l)
        doc = m.group('doc').replace('/-- Kernel check', '/-- Proof-term check')
        return '%s%stheorem %s : %s := by\n  %s\n' % (opts, doc, m.group('name'), stmt, proof)

    out = THM.sub(rep, src)
    last = list(re.finditer(r'^public import [^\n]*\n', out, re.M))[-1]
    extra = 'public import PlasmaLean.Certificates.KronProof2D\n' + \
        ''.join('meta import %s\n' % i for i in imports)
    out = out[:last.end()] + extra + out[last.end():]
    out = re.sub(r'Each theorem is one kernel evaluation \(`decide \+kernel`\) of exact integer '
                 r'arithmetic on the data of\n',
                 'Each theorem is an explicit proof term (`kron2_proof` of `Certificates/KronProof2D`: '
                 'block sums\nof the digit reading as kernel facts; `kron_lt` for the `ℓ¹` bounds) '
                 'on the data of\n', out, count=1)
    out = out.replace('# Kernel checks of', '# Proof-term checks of', 1)
    if sub:
        out = re.sub(r'^namespace (\S+)$', r'namespace \1.%s' % sub, out, count=1, flags=re.M)
        out = re.sub(r'^end (\S+)\n*$', r'end \1.%s\n' % sub, out, count=1, flags=re.M)
    return out


def patch_side(path):
    """Replace `decide +kernel` by `kernel_fact` in a bridge or chain module (or None if none)."""
    if not os.path.exists(path):
        return None
    src = open(path).read()
    if 'decide +kernel' not in src:
        return None
    return kernel_fact_text(src)


def kernel_fact_text(src):
    """The side conditions of a generated (non-check) module as `kernel_fact` proof terms: every
    `decide +kernel` becomes `kernel_fact`, the module imports `Certificates/KernelFact`, and long
    declarations get a scoped heartbeat budget. Used by the generators (`lam_emit_lean.py`,
    `fam_emit_lean.py`, ...) for the modules they write other than the check modules."""
    out = src
    # the family-image equations `Kv… = famPack …` (stage 8): `fampack_cert`
    if 'fampack_cert' in out and 'import PlasmaLean.Certificates.FamPackCert' not in out:
        last = list(re.finditer(r'^public import [^\n]*\n', out, re.M))[-1]
        out = out[:last.end()] + 'public import PlasmaLean.Certificates.FamPackCert\n' + out[last.end():]
    if 'decide +kernel' not in out:
        return out
    out = out.replace('decide +kernel', 'kernel_fact')
    if 'import PlasmaLean.Certificates.KernelFact' not in out:
        last = list(re.finditer(r'^public import [^\n]*\n', out, re.M))[-1]
        out = out[:last.end()] + 'public import PlasmaLean.Certificates.KernelFact\n' + out[last.end():]
    return scope_heartbeats(out)


HB_MIN_USES = 150  # declarations with at least this many `kernel_fact` side conditions


def scope_heartbeats(text):
    """Give each long declaration (many `kernel_fact` side conditions, each a few hundred
    heartbeats of elaboration) a scoped heartbeat budget, as the first option of its
    `set_option ... in` chain with the reason right after it (Mathlib's linter format). No
    unscoped options."""
    lines = text.split('\n')
    decl = re.compile(r'^(private |protected |noncomputable )*(theorem|lemma|def) ')
    starts = [k for k, l in enumerate(lines) if decl.match(l)]
    inserts = {}
    for n, k in enumerate(starts):
        end = starts[n + 1] if n + 1 < len(starts) else len(lines)
        uses = sum(l.count('kernel_fact') for l in lines[k:end])
        if uses < HB_MIN_USES:
            continue
        j = k
        while j > 0 and (lines[j - 1].startswith('set_option ') or lines[j - 1].startswith('/--')
                         or (lines[j - 1].strip() and not decl.match(lines[j - 1])
                             and not lines[j - 1].startswith('end ')
                             and lines[j - 1].rstrip().endswith('-/'))):
            j -= 1
        if 'set_option maxHeartbeats' in lines[j]:
            continue
        hb = max(400000, 2000 * uses)
        inserts[j] = ['set_option maxHeartbeats %d in' % hb,
                      '-- %d `kernel_fact` side conditions, each a small proof term to elaborate' % uses]
    out = []
    for k, l in enumerate(lines):
        out += inserts.get(k, [])
        out.append(l)
    return '\n'.join(out)


# top theorem module and main theorem of each family (prefix without `RationalStellaratorGC`)
TOPS = {
    'Mu': ('RationalStellaratorGCMuFamily', 'alpha_gc_passing_confined_forever'),
    'Mu2': ('RationalStellaratorGCMuWide', 'alpha_gc_passing_confined_forever_wide'),
    'Ew1': ('RationalStellaratorGCEwFamily', 'alpha_gc_confined_forever_energy_window'),
    'Ew2': ('RationalStellaratorGCEwFamily', 'alpha_gc_confined_forever_energy_window'),
    'Ew3': ('RationalStellaratorGCEwFamily', 'alpha_gc_confined_forever_energy_window'),
    'Ew4': ('RationalStellaratorGCEwFamily', 'alpha_gc_confined_forever_energy_window'),
    'Fam': ('RationalStellaratorGCFamily', 'alpha_gc_confined_forever_robust'),
}


def top_of(pre):
    """The top theorem module and the main theorem of a family."""
    short = pre[len('RationalStellaratorGC'):]
    if short in TOPS:
        mod, thm = TOPS[short]
    elif re.fullmatch(r'Mu\d+', short):  # further pitch cells (lambda-cell.sh)
        mod, thm = pre + 'Confined', '%s.rationalStellarator_gc_mu_confined_forever' % short
    else:
        sys.exit('unknown family %s' % pre)
    return 'PlasmaLean.Design.' + mod, 'PlasmaLean.Design.RationalStellaratorGC.' + thm


def tags_of(pre):
    return [t for t in 'HL' if os.path.exists(os.path.join(DES, '%sCheck%s1.lean' % (pre, t)))]


def imports_of(mod):
    path = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
    if not os.path.exists(path):
        return []
    return [m for m in re.findall(r'^(?:public )?(?:meta )?import (\S+)', open(path).read(), re.M)
            if m.startswith('PlasmaLean.')]


def family_files(pre):
    """The modules of a family rewritten by `--inplace` (checks, bridges, chains, and the
    environment and output modules whose side conditions `patch_side` converts)."""
    out = []
    for t in tags_of(pre):
        out += ['%sCheck%s%d' % (pre, t, k) for k in check_modules(pre, t)]
        out += [m for m in ('%sLowMem%s' % (pre, t), '%sChain%s' % (pre, t),
                            '%sEnv%s' % (pre, t), '%sOut%s' % (pre, t))
                if os.path.exists(os.path.join(DES, m + '.lean'))]
    return ['PlasmaLean.Design.' + m for m in out]


def plan(what, pres):
    if what == 'tags':
        return ' '.join('%s:%s' % (p, ''.join(tags_of(p))) for p in pres)
    if what == 'entrypoints':
        return ' '.join(dict.fromkeys(top_of(p)[1] for p in pres))
    if what == 'outputs':
        return ' '.join(m.replace('.', '/') + '.lean' for p in pres for m in family_files(p))
    changed = [m for p in pres for m in family_files(p)]
    mods = ['PlasmaLean.Certificates.KronProof', 'PlasmaLean.Certificates.KernelFact']
    for p in pres:
        mods += ['PlasmaLean.Design.%sKvS%s' % (p, t) for t in tags_of(p)]
    seen, order = set(), []

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in imports_of(m):
            visit(d)
        order.append(m)
    for p in pres:
        visit(top_of(p)[0])
    dirty = set(changed)
    for m in order:
        if m in dirty or any(d in dirty for d in imports_of(m)):
            dirty.add(m)
            mods.append(m)
    return ' '.join(dict.fromkeys(mods))


def main():
    args = sys.argv[1:]
    if args[:1] == ['--plan']:
        print(plan(args[1], args[2:]))
        return
    if len(args) < 2:
        sys.exit(__doc__)
    pre, tag = args[0], args[1]
    inplace = '--inplace' in args
    block = int(args[args.index('--block') + 1]) if '--block' in args else 9
    block2d = int(args[args.index('--block') + 1]) if '--block' in args else 3
    outdir = args[args.index('--out') + 1] if '--out' in args else DES
    ks = check_modules(pre, tag)
    if '--only' in args:
        keep = {int(k) for k in args[args.index('--only') + 1].split(',')}
        ks = [k for k in ks if k in keep]
    for k in ks:
        mod = '%sCheck%s%d' % (pre, tag, k)
        src = open(os.path.join(DES, mod + '.lean')).read()
        # two-dimensional checks (`nodeK`, `centerK`: Torus, NegTorus) or low-memory 3D checks
        conv = convert2d if ('KronLowMem' not in src and re.search(r'\b(nodeK|centerK) ', src)) \
            else convert
        blk = block2d if conv is convert2d else block
        if inplace:
            new, path = conv(src, mod, blk, ''), os.path.join(DES, mod + '.lean')
        else:
            newmod = '%sCheckP%s%d' % (pre, tag, k)
            new = conv(src, mod, blk, 'ProofTerm')
            path = os.path.join(outdir, newmod + '.lean')
        if new is None:
            print('skipped', mod, '(already converted)')
            continue
        open(path, 'w').write(new)
        print('wrote', os.path.relpath(path, ROOT))
    if inplace and '--only' not in args:
        for side in ('LowMem', 'Chain', 'Env', 'Out'):
            path = os.path.join(DES, '%s%s%s.lean' % (pre, side, tag))
            new = patch_side(path)
            if new is not None:
                open(path, 'w').write(new)
                print('patched', os.path.relpath(path, ROOT))


if __name__ == '__main__':
    main()
