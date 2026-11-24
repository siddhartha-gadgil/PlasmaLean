"""Attach three ordered field margins and the calibrated pilot to their original phase-zero births."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS
from verify_grouped_mirror_exclusion import FINAL
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


LABELS = ('q0r478', 'q0r523', 'q0r531')
THEORY = 'DommaschkOriginalBirthMargin'


def source(counts, records):
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    family, cal = 'DommaschkCommonEndpointTraces' + suffix, 'DommaschkCalibratedFamily' + suffix
    name = 'DommaschkOriginalBirthMargins' + suffix
    imports = '\n'.join('public import ' + FINAL + '.' + r['module'] for r in records.values())
    src = f'''module
public import PlasmaLean.Design.{THEORY}
public import CalibratedFamilyCache.{cal}
{imports}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkFirstMirrorLaunchSign
open DommaschkEndpointTraceFamily DommaschkOriginalBirthMargin DommaschkSignedObservable
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open {family} (checkpoint)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false
'''
    observations = []
    lemmas = []
    for e, record in records.items():
        n, archive = counts[e], record['module']
        k = min(n, record['groups'][-1]['stop'])
        drop = Fraction(record['drop'])
        target = f'(↑(height false - ({drop})) : ℝ)'
        observation = f'AtBirth .{e} (checkpoint .{e}) {k} {target} uC zC uA zA φ'
        observations.append(observation)
        lemmas.append(e + '_of_passage')
        src += f'''
theorem {lemmas[-1]} {{uC zC uA zA : FA}} {{φ : ℝ}} (small : |φ| ≤ 1/2^19)
    (path : (checkpoint .{e}).Passage .{e} uC zC uA zA φ) :
    {observation} := by
  apply from_passage rfl path (small.trans (by change 1/2^19 ≤ ({n}:ℝ)/64; norm_num))
    (by norm_num) (by change {k} ≤ {n}; norm_num) rfl rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  · with_unfolding_all exact ({archive}.fwd_below (MirrorEndpoint.start .{e})).take {k}
  · with_unfolding_all exact ({archive}.back_below (MirrorEndpoint.start .{e})).take {k}
'''
    props = ' ∧\n           '.join(observations)
    src += f'''
/-- The fixed torus pair supports all eight signed passages. On three of the same section's
other radii the trajectories pass through the specified original birth and have strict margins. -/
theorem from_common_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      (∀ e φ, |φ - azimuth e.opposite| ≤ e.width → (checkpoint e).Passage e uC zC uA zA φ) ∧
      ∀ φ, |φ| ≤ 1/2^19 →
        (∃ x y, y φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧
           Path (checkpoint .q0r470).length (checkpoint .q0r470).forwardExit
             (checkpoint .q0r470).backwardExit (checkpoint .q0r470).forwardRows
             (checkpoint .q0r470).backwardRows x y ∧ {cal}.Observed φ y) ∧
           {props} := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,calibrate⟩ := {cal}.same_embedded_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,each,fun φ small => ⟨calibrate φ small,?_,?_,?_⟩⟩
'''
    for e in records:
        src += f'''  · exact {e}_of_passage small (each .{e} φ
      (by simpa [MirrorEndpoint.width,MirrorEndpoint.opposite,azimuth] using small))
'''
    return name, src + f'\nend PlasmaLean.Design.{name}\n', [*lemmas, 'from_common_tori']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--calibrated', type=Path, required=True)
    parser.add_argument('--clearances', type=Path, nargs=3, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/common-original-margins')
    args = parser.parse_args()
    cal = json.loads(args.calibrated.read_text())
    counts = cal['lengths_each_direction']
    if set(counts) != set(ENDPOINTS) or any(type(n) is not int or not 1 <= n <= 391 for n in counts.values()):
        parser.error('expected the eight original endpoint lengths')
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    if cal['module'] != 'DommaschkCalibratedFamily' + suffix:
        parser.error('expected the original calibrated common torus family')
    keys, roots = [], []

    def authenticate(report, exports):
        paths = list(map(Path, report['import_paths']))
        marker = admitted(paths[0], report['module'], report['key'])
        if any(f"PlasmaLean.Design.{report['module']}.{t}" not in marker['theorems'] for t in exports):
            parser.error('missing expected theorem in the local kernel receipt')
        keys.append(marker['key'])
        roots.extend(paths)

    authenticate(cal, ['same_embedded_tori'])
    records = {r['endpoint'].lower(): r for r in (json.loads(f.read_text()) for f in args.clearances)}
    if set(records) != set(LABELS):
        parser.error('expected one distinct clearance for each secondary phase-zero launch')
    records = {e: records[e] for e in LABELS}
    for e, record in records.items():
        drop = Fraction(record['drop'])
        total = record['groups'][-1]['stop']
        name = f'Dommaschk{e.upper()}Drop{drop.numerator}Over{drop.denominator}SubmirrorPrefix{total:03}'
        if (record['module'] != name or not 1 <= total <= 391 or drop <= 0
                or record['packet_sha256'] != digest(load(int(e[3:]))[1])):
            parser.error(f'wrong original ordered field clearance for {e}')
        authenticate(record, ['fwd_below','back_below'])

    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()

    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    keys.extend([digest(DESIGN/(THEORY+'.trace')), lake('lean','--version')])
    overlay = merge_import_roots(args.cache, roots, keys)
    item = source(counts, records)
    base, rec = compile_modules(args.cache/item[0], [item], [overlay], keys, args, 'CommonOriginalMarginsCache')
    result = {k:v for k,v in rec.items() if k != 'artifacts'}
    result.update(lengths_each_direction=counts, calibrated_key=cal['key'],
                  margins={e:{'ordered_key':r['key'], 'drop':r['drop'],
                              'observed_length':min(counts[e],r['groups'][-1]['stop'])}
                           for e,r in records.items()}, import_paths=[str(base),str(overlay)])
    save(args.output, result)
    print(item[0], rec['key'], flush=True)


if __name__ == '__main__':
    main()
