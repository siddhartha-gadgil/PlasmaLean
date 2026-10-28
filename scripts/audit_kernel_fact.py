#!/usr/bin/env python3
"""Audit of the `kernel_fact` leaves.

`kernel_fact` (LeanTheory/Certificates/KernelFact.lean) proves a closed fact by an explicit proof
term whose leaves are kernel facts: `Nat.le_of_ble_eq_true x y rfl`, `lt_of_ble_succ x y rfl`,
`Nat.ne_of_beq_eq_false a c rfl`, `Rat.blt … = b` and `Eq.refl a : a = c`, each wrapped in
`@id P pf` (`mkExpectedTypeHint`).  What the kernel evaluates at a leaf is the statement `P`.

For every module containing `kernel_fact`, this script runs a small Lean program that imports the
built module, walks the proof terms of the module's declarations, finds the leaves, and estimates
the size of each leaf from the definitions its statement mentions (no profiler):

* the LeanTheory definitions reachable from `P` by unfolding (transitively, through definition
  values), their number, the longest unfolding chain (`depth`) and the bits of the literals they
  contain;
* `rec`: whether a reachable LeanTheory definition recurses (`*.rec`, `*.brecOn`,
  `WellFounded.fix`, or a core list traversal such as `List.map`, `List.foldl`, `List.range`).

Classes:
* `a`  closed facts on literals: no LeanTheory definition reachable (`2 ≤ 3`, `x < 2^k`, the
  length of a literal list);
* `a-data` facts on data definitions without recursion (`NLM ≤ 2^ddLM`, `(famLM 4).length = 6`,
  a literal read by `List.getD`);
* `b`  opaque: the leaf unfolds a recursive LeanTheory definition into a computation (a checker,
  an image `famPack`/`famTB`, a fold over a list). Ranked by `--time` (kernel check of the leaf
  alone, `Environment.addDecl`) when given, else by the number of reachable definitions.

Usage:
  python3 scripts/audit_kernel_fact.py [--default-only] [--time] [--modules M1,M2] [--out FILE]

Builds nothing: every module must be built (`lake build`).  One Lean process per module.
"""
import argparse
import collections
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

LEAN_TEMPLATE = r'''
import %(mod)s
import LeanTheory.Certificates.KernelFact
open Lean Meta

namespace AuditKF

/-- Recursion markers among used constants. -/
def recMarker (n : Name) : Bool :=
  match n with
  | .str _ s => s == "rec" || s == "brecOn" || s == "binductionOn" ||
      n == ``WellFounded.fix || n == ``List.map || n == ``List.foldl || n == ``List.foldr ||
      n == ``List.range || n == ``List.zipWith || n == ``List.flatMap || n == ``List.all ||
      n == ``List.any || n == ``List.filter || n == ``List.sum || n == ``List.replicate ||
      n == ``Nat.fold || n == ``Nat.repeat || n == ``Nat.all || n == ``Nat.any
  | _ => false

/-- Bits of the natural-number literals of an expression. -/
partial def litBits (e : Expr) : Nat :=
  go e 0
where go (e : Expr) (acc : Nat) : Nat :=
  match e with
  | .lit (.natVal n) => acc + Nat.log2 n + 1
  | .app f a => go a (go f acc)
  | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
  | .letE _ t v b _ => go b (go v (go t acc))
  | .mdata _ b | .proj _ _ b => go b acc
  | _ => acc

/-- Owned by a LeanTheory module. -/
def owned (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`LeanTheory).isPrefixOf env.allImportedModuleNames[idx.toNat]!
  | none => false

structure CInfo where
  bits : Nat
  isRec : Bool
  uses : Array Name

/-- Per-constant data of a LeanTheory definition. -/
def cinfo (env : Environment) (cache : IO.Ref (Std.HashMap Name CInfo)) (n : Name) :
    IO CInfo := do
  if let some c := (← cache.get)[n]? then return c
  let c : CInfo := match env.find? n with
    | some (.defnInfo d) =>
      let used := d.value.getUsedConstants
      { bits := litBits d.value, isRec := used.any recMarker,
        uses := used.filter fun m => owned env m }
    | _ => { bits := 0, isRec := false, uses := #[] }
  cache.modify (·.insert n c)
  return c

/-- Longest unfolding chain from `n`, recording the reachable definitions. -/
partial def visit (env : Environment) (cache : IO.Ref (Std.HashMap Name CInfo))
    (seen : IO.Ref (Std.HashSet Name)) (memo : IO.Ref (Std.HashMap Name Nat)) (n : Name)
    (fuel : Nat) : IO Nat := do
  if let some d := (← memo.get)[n]? then return d
  if fuel = 0 then return 0
  seen.modify (·.insert n)
  memo.modify (·.insert n 1)
  let ci ← cinfo env cache n
  let mut d := 0
  for m in ci.uses do
    d := max d (← visit env cache seen memo m (fuel - 1))
  memo.modify (·.insert n (d + 1))
  return d + 1

/-- Closure statistics: reachable LeanTheory definitions, depth, bits, recursion. -/
def closure (env : Environment) (cache : IO.Ref (Std.HashMap Name CInfo))
    (roots : Array Name) : IO (Nat × Nat × Nat × Bool) := do
  let seen ← IO.mkRef (Std.HashSet.emptyWithCapacity 64 : Std.HashSet Name)
  let memo ← IO.mkRef (Std.HashMap.emptyWithCapacity 64 : Std.HashMap Name Nat)
  let mut depth := 0
  for r in roots do depth := max depth (← visit env cache seen memo r 64)
  let s ← seen.get
  let mut bits := 0
  let mut anyRec := false
  for n in s do
    let ci ← cinfo env cache n
    bits := bits + ci.bits
    anyRec := anyRec || ci.isRec
  return (s.size, depth, bits, anyRec)

/-- The `@id P pf` leaves of an expression (shared subterms visited once). -/
partial def walk (visited : IO.Ref (Std.HashSet Expr)) (leaves : IO.Ref (Array (Expr × Expr)))
    (e : Expr) : IO Unit := do
  if (← visited.get).contains e then return
  visited.modify (·.insert e)
  match e with
  | .app f a =>
    if e.isAppOfArity ``id 2 then
      leaves.modify (·.push (e.appFn!.appArg!, e.appArg!))
    walk visited leaves f; walk visited leaves a
  | .lam _ t b _ | .forallE _ t b _ => walk visited leaves t; walk visited leaves b
  | .letE _ t v b _ => walk visited leaves t; walk visited leaves v; walk visited leaves b
  | .mdata _ b | .proj _ _ b => walk visited leaves b
  | _ => pure ()

def leafKind (pf : Expr) : Option String :=
  match pf.getAppFn with
  | .const ``Nat.le_of_ble_eq_true _ => some "le"
  | .const ``LeanTheory.Certificates.KronProof.lt_of_ble_succ _ => some "lt"
  | .const ``Nat.ne_of_beq_eq_false _ => some "ne"
  | .const ``Eq.refl _ => some "eq"
  | _ => none

def esc (s : String) : String := (s.replace "\t" " ").replace "\n" " "

def run (modName : Name) (doTime : Bool) : MetaM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? modName | throwError "module not found"
  let cache ← IO.mkRef ({} : Std.HashMap Name CInfo)
  let decls := env.header.moduleData[idx.toNat]!.constNames
  let mut nLeaf := 0
  for dn in decls do
    let some ci := env.find? dn | continue
    let some v := ci.value? (allowOpaque := true) | continue
    let leaves0 ← IO.mkRef (#[] : Array (Expr × Expr))
    let visited ← IO.mkRef (Std.HashSet.emptyWithCapacity 1024 : Std.HashSet Expr)
    walk visited leaves0 v
    let leaves := (← leaves0.get).filterMap fun (P, pf) =>
      match leafKind pf with
      | some k => if !P.hasLooseBVars && !P.hasFVar then some (P, pf, k) else none
      | none => none
    let mut j := 0
    for (P, pf, k) in leaves do
      j := j + 1
      nLeaf := nLeaf + 1
      let roots := P.getUsedConstants.filter fun m => owned env m &&
        (match env.find? m with | some (.defnInfo _) => true | _ => false)
      let (n, depth, bits, isRec) ← closure env cache roots
      let cls := if roots.isEmpty then "a" else if isRec then "b" else "a-data"
      let mut ms : Float := -1
      if doTime && cls == "b" then
        let tv : TheoremVal := { name := `auditKFtmp, levelParams := ci.levelParams, type := P, value := pf }
        let decl := Declaration.thmDecl tv
        let t0 ← IO.monoNanosNow
        let ok := match env.addDeclCore 0 100000 decl none with
          | Except.ok _ => true
          | Except.error _ => false
        let t1 ← IO.monoNanosNow
        ms := if ok then (t1 - t0).toFloat / 1.0e6 else -2
      let head := match P.getAppFn with | .const c _ => c.toString | _ => "?"
      let top := esc (String.intercalate "," (roots.map toString).toList)
      IO.println s!"LEAF\t{dn}\t{j}\t{k}\t{cls}\t{n}\t{depth}\t{bits}\t{ms}\t{head}\t{top}"
  IO.println s!"DONE\t{modName}\t{nLeaf}"

end AuditKF

#eval AuditKF.run `%(mod)s %(time)s
'''


def module_path(mod):
    return os.path.join(ROOT, mod.replace('.', '/') + '.lean')


def imports(mod):
    p = module_path(mod)
    if not os.path.exists(p):
        return None
    return re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)', open(p).read(), re.M)


def default_closure():
    seen, st = set(), ['LeanTheory']
    while st:
        m = st.pop()
        if m in seen:
            continue
        im = imports(m)
        if im is None:
            continue
        seen.add(m)
        st += im
    return seen


def kf_modules():
    """Modules using `kernel_fact`, with the number of source occurrences."""
    out = {}
    for dp, _, fs in os.walk(os.path.join(ROOT, 'LeanTheory')):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            src = open(p).read()
            # tactic uses only (not the docstrings of KernelFact itself)
            n = len(re.findall(r'(?<![`\w])kernel_fact(?![`\w])', src))
            if n and not p.endswith('Certificates/KernelFact.lean'):
                mod = os.path.relpath(p, ROOT)[:-5].replace('/', '.')
                out[mod] = n
    return out


def run_module(mod, do_time):
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False, dir='/tmp') as f:
        f.write(LEAN_TEMPLATE % {'mod': mod, 'time': 'true' if do_time else 'false'})
        path = f.name
    try:
        r = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)
    leaves, done = [], False
    for line in r.stdout.splitlines():
        parts = line.split('\t')
        if parts[0] == 'LEAF':
            _, decl, j, kind, cls, n, depth, bits, ms, head, top = parts
            leaves.append(dict(module=mod, decl=decl, j=int(j), kind=kind, cls=cls, n=int(n),
                               depth=int(depth), bits=int(bits), ms=float(ms), head=head,
                               top=top.split(',') if top else []))
        elif parts[0] == 'DONE':
            done = True
    if not done:
        sys.stderr.write('audit failed for %s:\n%s\n' % (mod, (r.stdout + r.stderr)[-2000:]))
    return leaves


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--default-only', action='store_true')
    ap.add_argument('--time', action='store_true', help='time the kernel check of class-b leaves')
    ap.add_argument('--modules', default='')
    ap.add_argument('--out', default=os.path.join(ROOT, '.lake', 'kernel_fact_audit.jsonl'))
    ap.add_argument('--report-only', action='store_true', help='summarize an existing --out file')
    args = ap.parse_args()

    src = kf_modules()
    dflt = default_closure()
    mods = sorted(src)
    if args.default_only:
        mods = [m for m in mods if m in dflt]
    if args.modules:
        mods = args.modules.split(',')

    if not args.report_only:
        with open(args.out, 'w') as out:
            for i, m in enumerate(mods):
                ls = run_module(m, args.time)
                for l in ls:
                    out.write(json.dumps(l) + '\n')
                out.flush()
                sys.stderr.write('[%d/%d] %s: %d leaves\n' % (i + 1, len(mods), m, len(ls)))

    leaves = [json.loads(l) for l in open(args.out)]
    report(leaves, src, dflt)


def short(decl):
    parts = [x for x in decl.split('.') if x]
    while len(parts) > 1 and (parts[-1].startswith('_proof') or parts[-1].startswith('proof_')
                              or parts[-1] == '_private' or parts[-1].isdigit()):
        parts.pop()
    return parts[-1]


def report(leaves, src, dflt):
    print('# kernel_fact audit')
    for scope, pred in (('default build', lambda m: m in dflt), ('overall', lambda m: True)):
        ls = [l for l in leaves if pred(l['module'])]
        uses = sum(n for m, n in src.items() if pred(m))
        c = collections.Counter(l['cls'] for l in ls)
        print('%s: %d source uses in %d modules; %d leaves: a %d, a-data %d, b (opaque) %d'
              % (scope, uses, sum(1 for m in src if pred(m)), len(ls), c['a'], c['a-data'], c['b']))
    print('\n## per module (leaves: a / a-data / b; b kernel ms)')
    per = collections.defaultdict(collections.Counter)
    pms = collections.Counter()
    for l in leaves:
        per[l['module']][l['cls']] += 1
        if l['cls'] == 'b' and l['ms'] > 0:
            pms[l['module']] += l['ms']
    for m in sorted(per, key=lambda m: -per[m]['b']):
        c = per[m]
        print('%-62s %s %5d / %5d / %5d  %8.0f' % (m.replace('LeanTheory.', ''),
              'D' if m in dflt else ' ', c['a'], c['a-data'], c['b'], pms[m]))
    print('\n## opaque (class b) leaves, grouped by module and the definitions they unfold')
    grp = collections.defaultdict(list)
    for l in leaves:
        if l['cls'] == 'b':
            sig = (l['module'], l['kind'], ','.join(sorted(set(l['top']))))
            grp[sig].append(l)

    def weight(g):
        ms = sum(max(l['ms'], 0) for l in g)
        return (ms, max(l['n'] for l in g))
    for sig in sorted(grp, key=lambda s: weight(grp[s]), reverse=True):
        g = grp[sig]
        ms, n = weight(g)
        print('%5d  %-50s %-3s defs<=%-4d depth<=%-3d ms %8.1f  [%s]  e.g. %s'
              % (len(g), sig[0].replace('LeanTheory.Design.', ''), sig[1], n,
                 max(l['depth'] for l in g), ms, sig[2][:120], short(g[0]['decl'])))


if __name__ == '__main__':
    main()
