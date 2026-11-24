"""Compose the exact two-direction integral budgets on the same N-108 physical path."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_row_time_clearance import PACKAGE as ROW_PACKAGE, name as row_name
from verify_signed_mirror_passage import merge_import_roots


BLOCK = 'RowFlightBlockCache'
FINAL = 'RowFlightBudgetCache'
N = 316
SIZE = 16
BLOCKS = (N+SIZE-1)//SIZE
BASE = '''@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkRowFlightBudget
open DommaschkMirrorTubeCrossing
set_option maxRecDepth 16384
'''
PATH = '''Path 325 DommaschkPhysicalPrefix325.exitState DommaschkBackwardPrefix325.exitState
      DommaschkPhysicalPrefix325.rows DommaschkBackwardPrefix325.rows x y'''


def header(name, imports):
    return ('module\npublic import PlasmaLean.Design.DommaschkRowFlightBudget\n'
            'public import FullBandFlightCache.DommaschkFullBandFlight325\n'
            + ''.join(f'public import {m}\n' for m in imports)+'\n'+BASE.format(name=name))


def block_name(k):
    return f'DommaschkRowFlightBlock{k:02}'


def block_module(k, rows):
    start = SIZE*k
    stop = min(N, start+SIZE)
    name = block_name(k)
    src = header(name, [f'{ROW_PACKAGE}.{row_name(i)}' for i in range(start, stop)])
    src += f'\nprivate abbrev Pilot (x : Plane) (y : ℝ → Plane) := {PATH}\n'
    for i in range(start, stop):
        q = rows[i]['q']
        src += f'''
private theorem row{i} {{x : Plane}} {{y : ℝ → Plane}} (path : Pilot x y) :
    Budget y ({i} / 64) ({i+1} / 64) {q} := by
  have lo : ((({i} : ℕ) : ℝ)) / 64 = ({i} : ℝ) / 64 := by norm_num
  have hi : ((({i} : ℕ) : ℝ) + 1) / 64 = ({i+1} : ℝ) / 64 := by norm_num
  rw [← lo, ← hi]
  apply from_row (i := {i}) path (by norm_num) (by change {i} < 325; norm_num)
    (by change {i} < 325; norm_num) (by norm_num)
'''
        for direction, factor in [('fwd', 'one_mul'), ('back', 'neg_one_mul')]:
            src += f'''  · rw [lo, hi]
    intro prev t x ht hx
    simp only [{factor}]
    with_unfolding_all exact {row_name(i)}.{direction}_tube_below ht hx
'''
    total = sum(r['q'] for r in rows.values())
    composition = f'(row{start} path)' + ''.join(f'\n    |>.append (row{i} path)'
                                                  for i in range(start+1, stop))
    src += f'''
theorem bounded {{x : Plane}} {{y : ℝ → Plane}} (path : {PATH}) :
    Budget y ({start} / 64) ({stop} / 64) {total} :=
  {composition}

end PlasmaLean.Design.{name}
'''
    return name, src, ['bounded']


def final_module():
    name = 'DommaschkRowFlightBudget325'
    src = header(name, [f'{BLOCK}.{block_name(k)}' for k in range(BLOCKS)])
    src += f'''open DommaschkSignedBirthApproach DommaschkMirrorBandPassage
open DommaschkFullBandFlightBounds

theorem central {{x : Plane}} {{y : ℝ → Plane}} (path : {PATH}) : Budget y 0 a 5916 := by
  have bound := ({block_name(0)}.bounded path)'''
    src += ''.join(f'\n    |>.append ({block_name(k)}.bounded path)' for k in range(1, BLOCKS))
    src += f'''
  simpa only [zero_div, a] using bound

/-- The physical first-mirror flight time has the stated bounds for each height on
the same signed field line through the original nested-torus birth. -/
theorem from_birth : ThroughBirth (fun φ y => Passage φ y ∧ WholeTime φ y) := by
  obtain ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, each⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, passage⟩ := each φ small
  have region : ∀ t ∈ Set.Icc (-b) b, DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [b, Nat.cast_ofNat, neg_div] using DommaschkSignedTraceDomain.on_path path
      (by norm_num) (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have prior := DommaschkFullBandFlightBounds.on_path path passage region
    (DommaschkMirrorHeightBand325.all_slopes path) (by
      simpa only [a, Nat.cast_ofNat, neg_div] using path.below_on (k := 316)
        (by norm_num) rfl rfl DommaschkCoreSubmirror316Of325.fwd_checked
        DommaschkCoreSubmirror316Of325.back_checked)
  exact ⟨y, start, passage, complete prior region (central path)⟩

end PlasmaLean.Design.{name}
'''
    return name, src, ['central', 'from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--flight', type=Path, required=True)
    p.add_argument('--rows', type=Path, default=ROOT/'.lake/row-time-clearance/rows')
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/row-flight-budget')
    p.add_argument('--blocks', type=int, nargs='+', default=list(range(BLOCKS)))
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if min(a.blocks) < 0 or max(a.blocks) >= BLOCKS or len(a.blocks) != len(set(a.blocks)):
        p.error(f'expected distinct blocks from 0 to {BLOCKS-1}')
    if a.output and set(a.blocks) != set(range(BLOCKS)):
        p.error('the all-height theorem requires every spatial block and every row')

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    packet, version = digest(RECORD), lake('lean', '--version')
    prior = json.loads(a.flight.read_text())
    parents = list(map(Path, prior['import_paths']))
    if (prior['lean_version'], prior['packet_sha256']) != (version, packet):
        p.error('wrong physical packet or Lean version for the full-band result')
    admitted(parents[0], 'DommaschkFullBandFlight325', prior['key'])
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    common = [packet, version, prior['key'], digest(DESIGN/'DommaschkRowFlightBudget.trace')]
    packages, blocks, row_roots, all_keys = [], [], [], []
    for k in sorted(a.blocks):
        rows = {}
        for i in range(k*SIZE, min((k+1)*SIZE, N)):
            r = json.loads((a.rows/f'{i:03}.json').read_text())
            if (r['index'], r['lean_version'], r['packet_sha256']) != (i, version, packet):
                raise ValueError(f'invalid spatial row {i}')
            admitted(Path(r['import_paths'][0]), row_name(i), r['key'])
            rows[i] = r
        ids = [r['key'] for r in rows.values()]
        roots = [Path(r['import_paths'][0]) for r in rows.values()]
        shared = merge_import_roots(a.cache, roots, [ROW_PACKAGE, *ids])
        decl = block_module(k, rows)
        base, rec = compile_modules(a.cache/decl[0], [decl], [shared, *parents],
                                    [common, *ids], env, BLOCK)
        packages.append(base)
        row_roots.append(shared)
        blocks.append(dict(index=k, key=rec['key'], q_sum=sum(r['q'] for r in rows.values())))
        all_keys.extend(ids)
        print(f'{decl[0]}: {rec["key"]}', flush=True)
    if a.output:
        if sum(b['q_sum'] for b in blocks) != 5916:
            raise ValueError('unexpected full budget')
        keys = [r['key'] for r in blocks]
        overlay = merge_import_roots(a.cache, [*packages, *row_roots], [BLOCK, *keys, *all_keys])
        decl = final_module()
        root, result = compile_modules(a.cache/decl[0], [decl], [overlay, *parents], [common, keys],
                                       env, FINAL)
        report = {k: v for k, v in result.items() if k != 'artifacts'}
        report.update(packet_sha256=packet, lean_version=version, flight_key=prior['key'], blocks=blocks,
                      q_sum=5916, rows=N, import_paths=[str(r) for r in [root, overlay, *parents]])
        save(a.output, report)
        print(f'{decl[0]}: {result["key"]}', flush=True)


if __name__ == '__main__':
    main()
