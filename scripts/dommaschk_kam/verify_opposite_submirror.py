"""Certify one shared 16-row field enclosure on four opposite-section launch sectors."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
import gzip
import json
from math import ceil
from pathlib import Path
import subprocess

from bounce_mirror_pilot import Model, SCALE, angle_models
from emit_position_slabs import step
from emit_sparse_taylor_slab import RECORD, ROOT
from screen_mirror_prefix_signs import gap_model
from verify_backward_physical_prefix import compile_modules, union
from verify_common_endpoint_traces import ENDPOINTS
from verify_grouped_mirror_exclusion import GAPS, compose, gap
from verify_mirror_endpoint_signs import header
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_signed_mirror_passage import merge_import_roots


LABELS = ('q1r456', 'q1r464', 'q1r509', 'q1r517')
COUNT = 16
MODEL = 'DommaschkOppositeLaunch016'
ROWS = 'OppositeSubmirrorRows'
FINAL = 'OppositeSubmirrorBirths'
THEORY = 'DommaschkOppositeMirrorExclusion'


def read_packet(label):
    path = RECORD.with_name(f'bounce_frame_q1_u{label[3:]}.json.gz')
    data = json.loads(gzip.decompress(path.read_bytes()))
    trs = data['traces']
    if (data['section_in_half_pi'] != 1 or F(data['launch_u']) != F(int(label[3:]), 1000)
            or data['coordinate_denominator'] != SCALE or data['step'] != '1/64'
            or [t['direction'] for t in trs] != [-1, 1]):
        raise ValueError(f'incorrect physical row archive for {label}')
    return trs, digest(path)


def shared_group(traces):
    """Fit one common polynomial clock. Each original row retains its own error radius."""
    inputs = []
    for i in range(COUNT):
        waves = angle_models(F(2*i+1,128),F(1,128),F(0))
        points = []
        for label in LABELS:
            for tr in traces[label]:
                row = tr['steps'][i]
                if row['index'] != i:
                    raise ValueError('noncontiguous position records')
                r, z = (Model(c, row['physical_radius_out']) for c in row['coefficients'])
                points.append((r, z.integer(tr['direction']), -waves[2], -waves[1]))
        inputs.append(points)
    group = []
    mid = (COUNT - 1) // 2
    for axis in range(4):
        originals = [p[axis].a for p in inputs[mid]]
        center = [(min(values) + max(values)) // 2 for values in zip(*originals, strict=True)]
        transformed = compose(center, COUNT-1-2*mid, COUNT)
        radius = 0
        for i, rows in enumerate(inputs):
            local = compose(transformed, F(2*i+1-COUNT, COUNT), F(1, COUNT))
            for row in rows:
                own = row[axis]
                difference = sum(abs(a-b) for a,b in zip(own.a,local,strict=True))
                radius = max(radius, ceil(own.e + difference))
        group.append(Model(transformed,radius))
    return group


def row_source(label, traces):
    name = 'DommaschkOppositeSubmirror'+label.upper()
    deps = [GAPS+'.'+MODEL, 'PlasmaLean.Design.'+THEORY]
    deps.extend(f'PlasmaLean.Design.DommaschkHarmonicBlock{i:02}' for i in range(COUNT//8))
    text = header(name,deps)
    text += ('open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing '
             'DommaschkOppositeMirrorExclusion Real\n')
    theorems = []
    for tr in traces:
        back = tr['direction'] == -1
        side = 'back' if back else 'fwd'
        signed_t = '(-t)' if back else 't'
        steps = []
        for i in range(COUNT):
            row = f'{side}{i:03}'
            steps.append(row)
            packet = f'(DommaschkHarmonicBlock{i//8:02}.packet {i%8})'
            text += f'def {row} : Step := {step(tr["steps"][i])}\n'
            text += f'''private theorem {row}_fits : FitsRow (i := {i}) {packet} {str(back).lower()} {row}
    ({F(2*i+1-COUNT,COUNT)}) ({F(1,COUNT)}) {MODEL}.group := by
  constructor <;> kernel_fact
'''
        for k in (5, COUNT):
            names = '['+', '.join(steps[:k])+']'
            text += f'''theorem {side}{k}_below (entry : State) :
    OnTubes (fun t x => strength (π / 2 + {signed_t}) x < DommaschkFirstMirrorLaunchSign.height false)
      entry 0 {names} := by
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) / 64 by norm_num]
'''
            for i, row in enumerate(steps[:k]):
                text += f'''  refine OnTubes.cons_at {i} ?_ ?_
  · intro t ht x hx
    apply {row}_fits.below {MODEL}.below (hx := hx)
    simpa only [Nat.cast_add, Nat.cast_one] using ht
'''
            text += '  trivial\n'
            theorems.append(f'{side}{k}_below')
    return name, text+f'end PlasmaLean.Design.{name}\n', theorems


def ground_source(family, calibrated, counts, modules):
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    name = 'DommaschkOppositeSubmirrorBirths'+suffix
    text = header(name, ['CalibratedFamilyCache.'+calibrated,
                         *[ROWS+'.'+m for m in modules]])
    text += f'''open Real Set Certificates.PositionFrameSlabs DommaschkOppositeMirrorExclusion
open DommaschkMirrorLaunch DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open {family} (checkpoint)
'''
    sizes = {label: COUNT if counts[label] >= COUNT else 5 for label in LABELS}
    if any(counts[e] < sizes[e] for e in LABELS):
        raise ValueError('each opposite-sector family must already cover five rows each way')
    theorems = []
    for label, mod in zip(LABELS, modules, strict=True):
        k = sizes[label]
        text += f'''theorem {label}_of_passage {{uC zC uA zA : FA}} {{φ : ℝ}}
    (path : (checkpoint .{label}).Passage .{label} uC zC uA zA φ) :
    SubmirrorBirth (checkpoint .{label}) .{label} {k} (DommaschkFirstMirrorLaunchSign.height false)
      uC zC uA zA φ := by
  apply from_passage path (by norm_num)
    (by change {k} ≤ {counts[label]}; norm_num) (by change {k} ≤ {counts[label]}; norm_num)
  · with_unfolding_all exact {mod}.fwd{k}_below _
  · with_unfolding_all exact {mod}.back{k}_below _
'''
        theorems.append(label+'_of_passage')
    text += '''theorem from_common_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      (∀ φ, |φ| ≤ 1 / 2 ^ 19 → ∃ y, y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) ∧
'''
    text += f'        {calibrated}.Observed φ y) ∧\n      ∀ φ : ℝ, |φ - π/2| ≤ 1 / 2 ^ 20 →\n        '
    text += ' ∧\n        '.join(f'SubmirrorBirth (checkpoint .{e}) .{e} {sizes[e]} '
             f'(DommaschkFirstMirrorLaunchSign.height false) uC zC uA zA φ' for e in LABELS)
    text += f''' := by
  obtain ⟨uC,zC,uA,zA,R,z,C,A,ic,ia,nested,ec,ea,_,each,cal⟩ := {calibrated}.same_embedded_tori
  refine ⟨uC,zC,uA,zA,R,z,C,A,ic,ia,nested,ec,ea,?_,?_⟩
  · intro φ small
    obtain ⟨_,y,start,_,result⟩ := cal φ small
    exact ⟨y,start,result⟩
  · intro φ small
    exact ⟨'''
    text += ',\n      '.join(f'{e}_of_passage (each .{e} φ (by simpa [MirrorEndpoint.width, '
            f'MirrorEndpoint.opposite, azimuth] using small))' for e in LABELS)
    text += f'⟩\nend PlasmaLean.Design.{name}\n'
    return name, text, [*theorems, 'from_common_tori']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--calibrated', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, choices=(1,2), default=1)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/opposite-submirror')
    args = parser.parse_args()
    original = json.loads(args.calibrated.read_text())
    counts = original['lengths_each_direction']
    if set(counts) != set(ENDPOINTS) or any(type(n) is not int or not 1 <= n <= 391 for n in counts.values()):
        parser.error('expected the eight physical endpoint row counts')
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    calibrated = 'DommaschkCalibratedFamily'+suffix
    if original['module'] != calibrated:
        parser.error('expected the common calibrated pilot family')
    roots = list(map(Path, original['import_paths']))
    admitted(roots[0], calibrated, original['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.cache = args.cache.resolve()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    traces, packets = {}, {}
    for label in LABELS:
        traces[label], packets[label] = read_packet(label)
    group = shared_group(traces)
    margin = gap_model(*group).bound()[1]
    if margin >= 0:
        raise ValueError(f'common field enclosure meets the first mirror height: {margin}')
    args.keys = [packets,lake('lean','--version')]
    field = gap(MODEL,group,args)
    overlay = union(args.cache,field)
    row_keys = [*args.keys, field[-1][1]['key'], digest(DESIGN/(THEORY+'.trace')),
                *[digest(DESIGN/f'DommaschkHarmonicBlock{i:02}.trace') for i in range(COUNT//8)]]
    def verify(label):
        declaration = row_source(label,traces[label])
        return compile_modules(args.cache/declaration[0],[declaration],[overlay],row_keys,args,ROWS)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        checked = list(pool.map(verify,LABELS))
    names = [r['module'] for _,r in checked]
    ground = ground_source('DommaschkCommonEndpointTraces'+suffix,calibrated,counts,names)
    keys = [original['key'],*[r['key'] for _,r in checked]]
    imports = merge_import_roots(args.cache,[*roots,overlay,*[r for r,_ in checked]],keys)
    root,record = compile_modules(args.cache/ground[0],[ground],[imports],keys,args,FINAL)
    report = {k:v for k,v in record.items() if k!='artifacts'}
    report.update(packets=packets,group_key=field[-1][1]['key'],rows_keys=dict(zip(LABELS,keys[1:],strict=True)),
                  group_upper=str(margin),calibrated_key=original['key'],
                  import_paths=list(map(str,[root,imports])))
    save(args.output,report)
    print(ground[0],record['key'],flush=True)


if __name__ == '__main__':
    main()
