"""Attach physical mirror-height brackets to one signed field line through a Q-16 birth.

Without --paired, check the two reusable implications on any sufficiently long
enclosed path with the archived rows. With a paired manifest, discharge those
hypotheses for all brackets reached by that particular birth passage.
"""
import argparse
import fcntl
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, key_of, save


INDICES = (316, 324)
PACKAGE = 'SignedMirrorCache'


def merge_import_roots(cache, roots, keys):
    """Lean uses the first directory for each package, so unify disjoint modules."""
    target = cache/'imports'/key_of(keys)
    target.mkdir(parents=True, exist_ok=True)
    with (target/'lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for root in roots:
            for obj in root.glob('*/*.olean*'):
                link = target/obj.relative_to(root)
                link.parent.mkdir(exist_ok=True)
                actual = obj.resolve(strict=True)
                if link.is_symlink():
                    if link.resolve(strict=True) != actual and digest(link) != digest(actual):
                        raise ValueError(f'conflicting Lean modules: {link.relative_to(target)}')
                else:
                    link.symlink_to(actual)
    return target


def bracket_theorem(i, first=False):
    block, offset = divmod(i, 16)
    h = str(i == 324).lower()
    tag_name = 'first' if first else 'hits'
    property_name = 'FirstBoth' if first else 'HitsBoth'
    history = (f'\n    (below : ∀ t ∈ Set.Icc (-({i}:ℝ)/64) ({i}/64), '
               f'strength t (y t) < DommaschkFirstMirrorLaunchSign.height {h})') if first else ''
    src = f"""
/-- A single enclosed physical path takes this value in both signed directions. -/
theorem {tag_name}{i} {{n : ℕ}} {{fs bs : State}} {{fr br : List Step}} {{x : Plane}}
    {{y : ℝ → Plane}} (path : Path n fs bs fr br x y) (reached : {i} < n)
    (hf : {i} < fr.length) (hb : {i} < br.length)
    (rf : fr[{i}] = DommaschkPositionFramesFwd.block{block}[{offset}])
    (rb : br[{i}] = DommaschkPositionFramesBack.block{block}[{offset}]){history} :
    {property_name} ({i}/64) ({i+1}/64) (DommaschkFirstMirrorLaunchSign.height {h}) y := by
  have stop : ({i} : ℝ) + 1 = {i+1} := by norm_num
  constructor
"""
    for back, rows, val, limit, eq, tag in (
            ('false', 'fr', 'y t', 'hf', 'rf', 'fwd'), ('true', 'br', 'y (-t)', 'hb', 'rb', 'back')):
        fn = 'y' if back == 'false' else '(fun t => y (-t))'
        src += f"""  · obtain ⟨cont, prev, tube⟩ := path.at_row reached {back} {limit}
    change ContinuousOn {fn} (Set.Icc ({i}/64) ((({i} : ℝ)+1)/64)) at cont
    change ∀ t ∈ Set.Icc ({i}/64) ((({i} : ℝ)+1)/64),
      {val} ∈ (physicalSlab prev {rows}[{i}] ({i}/64)).tube t at tube
    rw [stop] at cont
    rw [stop, {eq}] at tube
"""
        if not first:
            src += f'    simpa using DommaschkMirrorBracket{i}.{tag}_hit cont tube\n'
            continue
        angle = 't' if tag == 'fwd' else '(-t)'
        coeff = '1' if tag == 'fwd' else '(-1)'
        src += f'''    have field_cont : ContinuousOn (fun t => strength {angle} ({val}))
        (Set.Icc ({i}/64) ({i+1}/64)) := by
      have radial (t : ℝ) (ht : t ∈ Set.Icc ({i}/64) ({i+1}/64)) : 0 < ({val}) 0 := by
        apply DommaschkMirrorBracketSlab.positive_radius (hx := tube t ht)
        · rwa [show ({i}/64:ℝ) + 1/64 = {i+1}/64 by norm_num]
        · kernel_fact
        · kernel_fact
      simpa using continuousOn_strength cont {coeff} radial
    refine Fields.TrajectorySlabs.first_contact_in_bracket (by norm_num) (by norm_num) ?_ field_cont ?_
    · intro t ht
      exact below {angle} ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
    · have endpoint := tube ({i+1}/64) (by constructor <;> norm_num)
      simpa [DommaschkMirrorEndpointSign.oriented] using
        DommaschkMirrorSign{i}Right.{tag}_tube_sign endpoint
'''
    return src


def implications():
    name = 'DommaschkSignedMirrorBrackets'
    src = 'module\npublic import PlasmaLean.Design.DommaschkSignedObservable\n'
    src += ''.join(f'public import MirrorBracketCache.DommaschkMirrorBracket{i}\n' for i in INDICES)
    src += f'''
/-! # Two-sided level contacts along one enclosed physical field line -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkMirrorTubeCrossing
set_option linter.style.longLine false
'''
    for i in INDICES:
        src += bracket_theorem(i) + bracket_theorem(i, first=True)
    theorems = [f'{tag}{i}' for i in INDICES for tag in ('hits','first')]
    return name, src + f'\nend PlasmaLean.Design.{name}\n', theorems


def from_birth(n):
    indices = [i for i in INDICES if i < n]
    f, b = f'DommaschkPhysicalPrefix{n:03}', f'DommaschkBackwardPrefix{n:03}'
    name = f'DommaschkSignedMirrorBirth{n:03}'
    props = [f'HitsBoth ({i}/64) ({i+1}/64) (DommaschkFirstMirrorLaunchSign.height '
             + str(i == 324).lower() + ') y' for i in indices]
    src = f'''module
public import {PACKAGE}.DommaschkSignedMirrorBrackets
public import PairedPrefixCache.DommaschkPairedPrefix{n:03}

/-! # Paired physical mirror contacts from every admitted Q-16 birth -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable
set_option maxRecDepth 8192
set_option linter.style.longLine false

theorem contacts_from_birth :
    BirthWith (fun x => ∃ y, Path {n} {f}.exitState {b}.exitState {f}.rows {b}.rows x y ∧
      {' ∧ '.join(props)}) := by
  apply birth_with DommaschkPairedPrefix{n:03}.exists_nested_paired
  intro x y path
'''
    if len(indices) == 2:
        src += '  constructor\n'
    for i in indices:
        lead = '  · ' if len(indices) == 2 else '  '
        length = f'(by change {i} < {n}; norm_num)'
        src += lead + (f'exact DommaschkSignedMirrorBrackets.hits{i} path (by norm_num) '
                       f'{length} {length} rfl rfl\n')
    return name, src + f'\nend PlasmaLean.Design.{name}\n', ['contacts_from_birth']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--brackets', required=True, type=Path)
    parser.add_argument('--paired', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/signed-mirrors')
    args = parser.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    lean = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix'))/'bin/lean'),
                           lean_path=lake('printenv', 'LEAN_PATH'))
    version = lake('lean', '--version')
    identity = [version, digest(RECORD), digest(DESIGN/'DommaschkSignedObservable.trace')]
    roots = []
    for i in INDICES:
        name = f'DommaschkMirrorBracket{i}'
        row, = [r for r in json.loads(args.brackets.read_text())['brackets'] if r['module'] == name]
        deps = list(map(Path, row['import_paths']))
        admitted(deps[0], name, row['key'])
        roots.extend(deps)
        identity.append(row['key'])
    decl = implications()
    library = merge_import_roots(args.cache, roots, identity)
    base, record = compile_modules(args.cache/decl[0], [decl], [library], identity, lean, PACKAGE)
    roots = [base, library]
    if args.paired:
        paired = json.loads(args.paired.read_text())
        n = paired['slabs_per_direction']
        if n <= INDICES[0] or paired['packet_sha256'] != digest(RECORD):
            parser.error('the paired trajectory must cover the first bracket in this archive')
        deps = list(map(Path, paired['import_paths']))
        admitted(deps[0], f'DommaschkPairedPrefix{n:03}', paired['key'])
        decl = from_birth(n)
        parents = [record['key'], paired['key'], version]
        library = merge_import_roots(args.cache, [*roots, *deps], parents)
        base, record = compile_modules(args.cache/decl[0], [decl], [library], parents, lean,
                                       'SignedMirrorBirthCache')
        roots = [base, library]
    result = {k:v for k,v in record.items() if k != 'artifacts'}
    result.update(import_paths=list(map(str, roots)), packet_sha256=digest(RECORD))
    if args.output:
        save(args.output, result)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
