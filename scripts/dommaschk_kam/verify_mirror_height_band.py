"""Assemble closed-slab slope bounds into the true first mirror branches on a continuum of heights."""

import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


ROWS = range(316, 325)
PACKAGE = 'MirrorBandSlabCache'


def row_source(i):
    name = f'DommaschkMirrorBandRow{i}'
    tube = f'DommaschkMirrorSlope{i}ClosedTube'
    text = f'''module
public import MirrorSlopeClosedTubeCache.{tube}
public import PlasmaLean.Design.DommaschkSignedMirrorBand

/-! # Closed-cell outward slope at both signed physical tubes of this pilot row -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedMirrorBand DommaschkMirrorTubeCrossing
open Set
set_option maxRecDepth 16000
'''
    for direction, sign, cleanup in [('fwd', '1', 'one_mul'), ('back', '(-1)', 'neg_one_mul')]:
        text += f'''
theorem {direction} : SlabSlope {tube}.row_{direction} {sign}
    ({i} / 64) ({i+1} / 64) (1 / 400) := by
  intro t ht y prev hx field
  have d := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t field
  obtain ⟨v, lower, derivative⟩ := {tube}.{direction}_transverse
    (y := fun a => coordinates (y a)) (prev := prev) ht
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx)
    (d.congr_deriv (coordinates.apply_symm_apply _))
  refine ⟨v, lt_of_le_of_lt (by norm_num) lower, ?_⟩
  simp only [{cleanup}]
  with_unfolding_all exact derivative
'''
    return name, text + f'\nend PlasmaLean.Design.{name}\n', ['fwd', 'back']


def assembly():
    name = 'DommaschkMirrorHeightBand325'
    text = 'module\npublic import SignedMirrorBirthCache.DommaschkFirstMirrorBirth325\n'
    for i in ROWS:
        text += f'public import {PACKAGE}.DommaschkMirrorBandRow{i}\n'
    text += f'''
/-! # A single signed birth path with continuous first mirror times for every intermediate height -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkSignedMirrorBand
open DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign Set
set_option maxRecDepth 16384

private abbrev Pilot (x : Plane) (y : ℝ → Plane) :=
  Path 325 DommaschkPhysicalPrefix325.exitState DommaschkBackwardPrefix325.exitState
    DommaschkPhysicalPrefix325.rows DommaschkBackwardPrefix325.rows x y
'''
    for i in ROWS:
        text += f'''
private theorem row{i} {{x : Plane}} {{y : ℝ → Plane}} (path : Pilot x y) :
    Rates y ({i} / 64) ({i+1} / 64) (1 / 400) := by
  have lo : ((({i} : ℕ) : ℝ)) / 64 = ({i} : ℝ) / 64 := by norm_num
  have hi : ((({i} : ℕ) : ℝ) + 1) / 64 = ({i+1} : ℝ) / 64 := by norm_num
  rw [← lo, ← hi]
  apply attach (i := {i}) path (by norm_num) (by change {i} < 325; norm_num)
    (by change {i} < 325; norm_num)
  · rw [lo, hi]
    with_unfolding_all exact DommaschkMirrorBandRow{i}.fwd
  · rw [lo, hi]
    with_unfolding_all exact DommaschkMirrorBandRow{i}.back
'''
    combined = '(row316 path)' + ''.join(f'.append (row{i} path)' for i in list(ROWS)[1:])
    text += f'''
theorem all_slopes {{x : Plane}} {{y : ℝ → Plane}}
    (path : Path 325 DommaschkPhysicalPrefix325.exitState DommaschkBackwardPrefix325.exitState
      DommaschkPhysicalPrefix325.rows DommaschkBackwardPrefix325.rows x y) :
    Rates y (316 / 64) (325 / 64) (1 / 400) :=
  {combined}

/-- One path from the prescribed birth supplies ordered continuous first-mirror functions of
the entire field height interval, with quantitative separation and transverse crossings. -/
theorem from_birth :
    BirthWith (fun x => ∃ y, Path 325 DommaschkPhysicalPrefix325.exitState
      DommaschkBackwardPrefix325.exitState DommaschkPhysicalPrefix325.rows
      DommaschkBackwardPrefix325.rows x y ∧ Branches y) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, each⟩ :=
    DommaschkFirstMirrorBirth325.contacts_from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ hφ => ?_⟩
  obtain ⟨sign, approach, hs, clock, entry, ode, y, path, lower, upper⟩ := each φ hφ
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  obtain ⟨⟨p, hp, ep, _⟩, ⟨b, hb, eb, _⟩⟩ := upper
  exact ⟨sign, approach, hs, clock, entry, ode, y, path,
    branches path (by norm_num) region lower ⟨⟨p, hp, ep⟩, b, hb, eb⟩ (all_slopes path)⟩

end PlasmaLean.Design.{name}
'''
    text = text.replace('  ' + combined, '  ' + combined.replace('.append', '\n    |>.append'))
    return name, text, ['all_slopes', 'from_birth']


def passage():
    name = 'DommaschkRegularMirrorHeightBand325'
    source = f'''module
public import PlasmaLean.Design.DommaschkMirrorBandPassage
public import MirrorHeightBandBirthCache.DommaschkMirrorHeightBand325

/-! # Regular mirror birth and finite physical one-way flight at every admitted height -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkSignedObservable DommaschkSignedBirthApproach DommaschkMirrorBandPassage
set_option maxRecDepth 16384

/-- One signed field line goes through the actual torus-interpolated birth and
supports the regular arclength wells, finite flights and true action for the whole height band. -/
theorem from_birth : ThroughBirth (fun φ y =>
    ∃ x, Path 325 DommaschkPhysicalPrefix325.exitState DommaschkBackwardPrefix325.exitState
      DommaschkPhysicalPrefix325.rows DommaschkBackwardPrefix325.rows x y ∧ Passage φ y) := by
  apply from_birthWith DommaschkMirrorHeightBand325.from_birth (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  intro φ small x y path band
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  exact ⟨x, path, on_path path (by norm_num) (small.trans (by norm_num)) region band⟩

end PlasmaLean.Design.{name}
'''
    return name, source, ['from_birth']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--slopes', required=True, nargs='+', type=Path)
    parser.add_argument('--first-contacts', type=Path,
                        help='combine all nine rows on the paired 325-row Q-16 birth path')
    parser.add_argument('--passage-output', type=Path,
                        help='also certify all-height regular births, finite flights and action')
    parser.add_argument('--area-output', type=Path,
                        help='certify the exact area of the regular birth rectangle on the pilot')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/mirror-height-band')
    args = parser.parse_args()
    if args.passage_output and not args.first_contacts:
        parser.error('--passage-output needs the actual first contacts and all nine rows')
    if args.area_output and not args.passage_output:
        parser.error('--area-output needs --passage-output on the same birth family')
    rows = {}
    for path in args.slopes:
        data = json.loads(path.read_text())
        i = data['index']
        if i not in ROWS or i in rows or data['part'] != 'closed-tube':
            parser.error(f'require distinct closed slope certificates in rows 316–324, got row {i}')
        rows[i] = data
    if args.first_contacts and set(rows) != set(ROWS):
        parser.error(f'missing closed-slab proofs {sorted(set(ROWS) - set(rows))}')

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    version, packet = lake('lean', '--version'), digest(RECORD)
    common = [version, packet, digest(DESIGN / 'DommaschkSignedMirrorBand.trace')]
    imports, manifests, keys = [], [], []
    for i, data in sorted(rows.items()):
        sources = list(map(Path, data['import_paths']))
        admitted(sources[0], f'DommaschkMirrorSlope{i}ClosedTube', data['key'])
        decl = row_source(i)
        base, rec = compile_modules(args.cache / decl[0], [decl], sources,
                                    [common, data['key']], env, PACKAGE)
        imports.extend([base, *sources])
        keys.append(rec['key'])
        manifests.append({'index': i, 'key': rec['key'], 'slope_key': data['key']})
    result = dict(packet_sha256=packet, lean_version=version, squared_slope='1/400', rows=manifests)
    if args.first_contacts:
        first = json.loads(args.first_contacts.read_text())
        if first['packet_sha256'] != packet:
            parser.error('first contacts must come from the original pilot packet')
        sources = list(map(Path, first['import_paths']))
        admitted(sources[0], 'DommaschkFirstMirrorBirth325', first['key'])
        identity = [common, keys, first['key']]
        overlay = merge_import_roots(args.cache, imports + sources, identity)
        decl = assembly()
        root, rec = compile_modules(args.cache / decl[0], [decl], [overlay], identity, env,
                                    'MirrorHeightBandBirthCache')
        result.update({key: value for key, value in rec.items() if key != 'artifacts'})
        result.update(first_contacts_key=first['key'], import_paths=[str(root), str(overlay)])
    if args.output:
        save(args.output, result)
    if args.passage_output:
        applications = passage()
        checks = [version, packet, result['key'], digest(DESIGN / 'DommaschkMirrorBandPassage.trace')]
        final_root, accepted = compile_modules(args.cache / applications[0], [applications],
                                               [root, overlay], checks, env, 'RegularMirrorBandCache')
        physical = {key: value for key, value in accepted.items() if key != 'artifacts'}
        physical.update(packet_sha256=packet, lean_version=version, band_key=result['key'],
                        import_paths=[str(final_root), str(root), str(overlay)])
        save(args.passage_output, physical)
        if args.area_output:
            name = 'DommaschkRegularBirthArea325'
            body = '''module
public import PlasmaLean.Design.DommaschkMirrorBirthArea
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

@[expose] public section
namespace PlasmaLean.Design.DommaschkRegularBirthArea325

/-- The same nested pilot tori carry a rectangle of known positive area in angle and height. -/
theorem from_birth : DommaschkMirrorBirthArea.AreaBound :=
  DommaschkMirrorBirthArea.of_passage DommaschkRegularMirrorHeightBand325.from_birth
    (fun _ _ h => let ⟨_, _, passage⟩ := h; passage)

end PlasmaLean.Design.DommaschkRegularBirthArea325
'''
            area_keys = [version, packet, physical['key'], digest(DESIGN / 'DommaschkMirrorBirthArea.trace')]
            area_imports = [final_root, root, overlay]
            area_root, area = compile_modules(args.cache / name, [(name, body, ['from_birth'])],
                                              area_imports, area_keys, env, 'MirrorBirthAreaCache')
            report = {key: value for key, value in area.items() if key != 'artifacts'}
            report.update(packet_sha256=packet, passage_key=physical['key'],
                          import_paths=[str(path) for path in [area_root, *area_imports]])
            save(args.area_output, report)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
