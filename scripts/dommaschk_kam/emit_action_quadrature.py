"""Emit Lean action-quadrature certificates from fresh, directed field-line runs.

One 72-bit record contains a one-sided density bound, a one-sided bound for
max(2*(h-B),0), and an integer square-root witness. One Lean proof term per
48-panel slab checks all three columns, the number of panels and their mass.
Negative-going slabs and their panels are reversed into increasing physical angle.
"""
import argparse
from fractions import Fraction as F
from itertools import islice
from math import ceil, floor, isqrt
from pathlib import Path
import json

from bounce_action_pilot import PanelPolynomial, TARGET, sqrt_nonnegative
from bounce_common_section import common_section_inputs
from bounce_launch_box import Box, S
from bounce_local_graph import BRACKETS
from bounce_mirror_pilot import HEIGHTS, Model, certified_segments, pilot_inputs
from bounce_phase_chart import chart_inputs
from bounce_phase_frame import framed_segments
from bounce_phase_strength import ShiftedStrength


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'PlasmaLean' / 'Design'
PACK = ROOT / 'scripts/dommaschk_kam/results/bounce_local_graphs_20261123.json'
STEP = F(1, 64)
PANELS = 48
SPATIAL = 2**20
GAP = 2**26
DIGIT = 2**24


def as_lean(x):
    return f'({x.numerator} / {x.denominator} : ℝ)'


def panel_row(segment, data, strength, h, upper, splits):
    tube, angles, fields = segment.fields(data)
    radius = tube[0]
    den, nr, nz = fields
    r2 = radius*radius
    r4 = r2*r2
    r8 = r4*r4
    r16 = r8*r8
    ut = radius*den
    u = ut*ut + nr*nr + nz*nz
    if strength is None:
        gap = u - r16*Model.rational(h*h)
    else:
        gap, = strength.numerators(tube, angles, fields, [h])
    den, r8, r16, u, num = map(PanelPolynomial, (den, r8, r16, u, -gap))
    direction = range(splits) if segment.sign == 1 else reversed(range(splits))
    packed, total = 0, 0
    for j, n in enumerate(direction):
        left, right = F(2*n, splits)-1, F(2*(n+1), splits)-1
        t = Box(floor(left*S), ceil(right*S))
        root = sqrt_nonnegative(u.on(t))
        mag = root/r8.on(t)
        ds = root/den.on(t)
        raw = num.on(t)
        clipped = Box(max(0,raw.lo),max(0,raw.hi))
        speed2 = Box(2*S,2*S)*(clipped/(r16.on(t)*(Box.rational(h)+mag)))
        if upper:
            a = ceil(F(ds.hi*SPATIAL, S))
            g = ceil(F(speed2.hi*GAP, S))
            y = isqrt(g*(SPATIAL**2//GAP))
            y += int(y*y < g*(SPATIAL**2//GAP))
            assert g*SPATIAL**2 <= y*y*GAP
        else:
            a = floor(F(ds.lo*SPATIAL, S))
            g = floor(F(speed2.lo*GAP, S))
            y = isqrt(g*(SPATIAL**2//GAP))
            assert y*y*GAP <= g*SPATIAL**2
        if not all(0 <= x < DIGIT for x in (a,g,y)):
            raise ArithmeticError('panel column exceeds its unsigned 24-bit digit')
        packed += (a + DIGIT*g + DIGIT**2*y) << (72*j)
        total += a*y
    return packed, total*(PANELS//splits)


def generate(section, radius, dest):
    source = json.loads(PACK.read_text())
    record, = [r for r in source['sections'][section]['endpoints'] if F(r['launch_radius']) == radius]
    index = record['height_index']
    height = HEIGHTS[index]
    upper = radius == BRACKETS[section][index][0]
    half_width = F(record['phase_half_width'])
    assert record['section_in_half_pi'] == section and list(map(F,record['heights'])) == list(HEIGHTS)
    assert F(record['step']) == STEP and record['panels_per_step'] == PANELS
    inputs, _ = common_section_inputs(half_width, F(0), radius, section)
    strength = ShiftedStrength(inputs[0])
    ends = [F(c['brackets'][index][1]) for c in record['crossings']]
    assert [c['direction'] for c in record['crossings']] == [-1, 1]
    groups = sample(inputs, strength, ends, height, upper, F(49, 8))
    name = f'DommaschkActionQ{section}R{int(radius*1000)}'
    write_table(groups, height, upper, name, f'section {section}π/2, launch radius {radius}', dest)


def sample(inputs, strength, ends, height, upper, limit, *, origin=(), jitter=F(0),
           builder=framed_segments, splits=PANELS):
    assert splits in (8, PANELS)
    groups = []
    for sign, end in zip((-1, 1), ends, strict=True):
        nsteps = int(end/STEP)
        assert end == nsteps*STEP
        trace = builder(*inputs, sign, STEP, ceil(limit/STEP), jitter, origin)
        rows = [panel_row(s, inputs[0], strength, height, upper, splits) for s in islice(trace, nsteps)]
        assert len(rows) == nsteps
        if sign == -1:
            rows.reverse()
        groups.append(rows)
    return groups


def face(sector, outer, dest):
    result_dir = PACK.parent
    radius = F(27, 50) if outer else F(11, 25)
    upper = not outer
    index = int(upper)
    if sector.startswith('sym'):
        q = int(sector[-1])
        source = json.loads((result_dir/'bounce_phase_faces_20261123.json').read_text())
        row, = [s for record in source['runs'] if (s := record['result'])['section_in_half_pi'] == q
                and F(s['face_u']) == radius and F(s['step']) == STEP]
        width = F(row['phase_half_width'])
        inputs, _ = common_section_inputs(width, F(0), radius, q)
        origin, limit = (), F(6)
        label = f'section {q}π/2'
    else:
        q = int(sector[-1])
        broad = sector.startswith('broad')
        source = json.loads((result_dir/'bounce_phase_chart_20261123.json').read_text())
        sector_record, = [r for r in source['records'] if r['quadrant'] == q and r['face_only'] == broad]
        width = F(sector_record['phase_half_width'])
        row, = [r for r in sector_record['faces'] if F(r['face_u']) == radius]
        limit = F(sector_record['trace_limit'])
        inputs_at, origin = chart_inputs(q, F(sector_record['chart_center']), width)
        inputs, _ = inputs_at(radius)
        label = f'chart {q}π/4 + arctan(1/2)'
    assert F(row['step']) == STEP and row['panels_per_step'] == 8
    assert list(map(F, row['heights'])) == list(HEIGHTS)
    if 'extents' in row:
        assert [t['direction'] for t in row['extents']] == [-1, 1]
        key = 'forbidden_cap' if upper else 'accessible_core_end'
        ends = [F(t[key]) for t in row['extents']]
    else:
        ends = [F(t[index]) for t in row['cutoff_abs_phi']]
    groups = sample(inputs, ShiftedStrength(inputs[0]), ends, HEIGHTS[index], upper, limit,
                    origin=origin, splits=8)
    name = 'DommaschkAction' + sector.capitalize() + ('Outer' if outer else 'Inner')
    write_table(groups, HEIGHTS[index], upper, name,
                f'{label}, half-width {width}, radius {radius}', dest, splits=8)


def mirror(common, index, dest):
    source = json.loads((PACK.parent/'bounce_mirror_cell_20261123.json').read_text())
    record = source[('common_section_' if common else '') + 'action_step_1_64']
    width, radial = F(record['alpha_half_width']), F(record['u_half_width'])
    assert F(record['step']) == STEP and record['panels_per_step'] == 8
    assert list(map(F, record['heights'])) == list(HEIGHTS)
    inputs = common_section_inputs(width, radial)[0] if common else pilot_inputs(width, radial)
    ends = [F(t[index]) for t in record['cutoff_abs_phi']]
    groups = sample(inputs, None, ends, HEIGHTS[index], index == 0, F(21, 4),
                    jitter=F(0) if common else width, builder=certified_segments, splits=8)
    coordinate = 'Common' if common else 'Birth'
    name = 'DommaschkActionMirror' + coordinate + ('High' if index else 'Low')
    write_table(groups, HEIGHTS[index], index == 0, name,
                f'{coordinate.lower()} angle, phase half-width {width}, radial half-width {radial}',
                dest, splits=8)


def write_table(groups, height, upper, name, label, dest, splits=PANELS):
    rows = groups[0] + groups[1]
    mass = sum(x for _, x in rows)
    bound = F(mass,SPATIAL**2)*STEP/PANELS
    margin = TARGET-bound if upper else bound-TARGET
    if margin <= 0:
        raise ArithmeticError('directed integral fails its required endpoint sign')
    start = f'(-{len(groups[0])} / 64 : ℝ)'
    end = f'({len(groups[1])} / 64 : ℝ)'
    side = 'true' if upper else 'false'
    def row_term(p, mass):
        data = f'0x{p:x}' if splits == PANELS else f'repeatSix 8 0x{p:x}'
        return f'  ⟨{data}, {mass}, rfl⟩'

    chunks = ',\n'.join(row_term(p, v) for p, v in rows)
    text = f'''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Action panels for {label}
Generated by `scripts/dommaschk_kam/emit_action_quadrature.py`. Each slab includes
the kernel proof of its 48 directed square-root tests and its exact weighted sum.
-/

@[expose] public section
namespace PlasmaLean.Design.{name}
open PlasmaLean.Certificates.MirrorActionQuadrature

set_option linter.style.longLine false
set_option maxRecDepth 8192

/-- Ordered slab witnesses in increasing absolute angle; the section is the angular origin. -/
noncomputable def slabs : List (Block {side}) := [
{chunks}]

/-- Exact finite certificate, including the number of slabs and comparison with the target. -/
theorem checked : Packet {side} slabs {len(groups[0])} {len(groups[1])}
    {TARGET.numerator} {TARGET.denominator} := by
  constructor
  · rfl
  · change {'total slabs * '+str(TARGET.denominator)+' < '+str(TARGET.numerator)+' * 3072 * 1099511627776' if upper else str(TARGET.numerator)+' * 3072 * 1099511627776 < total slabs * '+str(TARGET.denominator)}
    kernel_fact

/-- The clipped action has the strict required sign on any trace with the exported
primitive density and parallel-speed bounds. These two pointwise physical enclosures
are the interface to the trajectory checker. -/
theorem endpoint {{f w : ℝ → ℝ}}
    (phys : Covers {side} w f {as_lean(height)} {start} slabs)
    (hw : ∀ t ∈ Set.Icc {start} {end}, 0 ≤ w t)
    (contF : ContinuousOn f (Set.Icc {start} {end}))
    (contW : ContinuousOn w (Set.Icc {start} {end})) :
    {'PlasmaLean.Kinetic.MirrorHeightAction.action f w '+start+' '+end+' '+as_lean(height)+' < '+as_lean(TARGET) if upper else as_lean(TARGET)+' < PlasmaLean.Kinetic.MirrorHeightAction.action f w '+start+' '+end+' '+as_lean(height)} := by
  exact checked.sound (h := {as_lean(height)}) (by norm_num) phys hw contF contW

end PlasmaLean.Design.{name}
'''
    path = dest / f'{name}.lean'
    path.write_text(text)
    print(f'{path.name}: {len(rows)} slabs, {len(rows)*PANELS} panels, margin {float(margin):.9g}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    case = parser.add_mutually_exclusive_group(required=True)
    case.add_argument('--section', type=int, choices=[0, 1], help='N-60 endpoint, with --u')
    case.add_argument('--face', choices=['sym0', 'sym1', 'chart0', 'chart1', 'chart2', 'chart3',
                                         'broad1', 'broad2'], help='N-59 sector, with --u')
    case.add_argument('--mirror', choices=['birth', 'common'], help='N-57 cell, with --height')
    parser.add_argument('--u', type=F)
    parser.add_argument('--height', type=int, choices=[0, 1])
    parser.add_argument('--output-dir', type=Path, default=DEST)
    args = parser.parse_args()
    if args.mirror:
        if args.height is None or args.u is not None:
            parser.error('--mirror requires --height')
        mirror(args.mirror == 'common', args.height, args.output_dir)
    elif args.face:
        if args.u not in (F(11, 25), F(27, 50)):
            parser.error('--face requires --u 11/25 or 27/50')
        face(args.face, args.u == F(27, 50), args.output_dir)
    else:
        if args.u not in sum(BRACKETS[args.section], ()):
            parser.error('radius must be a bracket endpoint at the selected section')
        generate(args.section, args.u, args.output_dir)
