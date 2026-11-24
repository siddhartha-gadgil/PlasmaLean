"""Verify the seven-harmonic, two-spatial-variable evaluator used by the original action packet."""
import argparse
from collections import defaultdict
from dataclasses import replace
from fractions import Fraction as F
import gzip
import json
from math import comb
from pathlib import Path
import subprocess

from bounce_collar import S, harmonic_terms
from bounce_mirror_pilot import HEIGHTS, Model, R0, R0M, SCALE, ZERO, polynomial_data
from bounce_phase_strength import ShiftedStrength
from emit_sparse_taylor_slab import RECORD, ROOT, model_literal
from replay_physical_action_archive import segment
from screen_sparse_reference_defects import sparse_fields
from verify_backward_physical_prefix import compile_modules, union
from verify_physical_trace_slabs import DESIGN, digest, save


DATA_PACKAGE = 'NativeActionDataCache'
INPUT_PACKAGE = 'NativeActionInputCache'
FIELD_PACKAGE = 'NativeActionFieldCache'
OUTPUT_PACKAGE = 'NativeActionModelCache'
WAVES = ('one', 'sin1', 'cos1', 'sin2', 'cos2', 'sin3', 'cos3')
FIELDS = ('D', 'NR', 'NZ', 'Shift')
SP_FIELDS = ('dD', 'dnR', 'dnZ', f'(DommaschkCompensatedAction.shiftedD ({HEIGHTS[0]}))')


def header(name, imports):
    return ('module\n' + ''.join('public import ' + imp + '\n' for imp in imports)
            + '\n@[expose] public section\nnamespace PlasmaLean.Design.' + name
            + '\nopen Certificates.TrajectoryTaylorModel DommaschkKam DommaschkBounceTaylor\n'
            + 'open DommaschkHarmonicHorner DommaschkNativeActionModel\n'
            + 'set_option linter.all false\nset_option maxRecDepth 16384\n'
            + 'set_option maxHeartbeats 0\nset_option Elab.async false\n\n')


def footer(name):
    return '\nend PlasmaLean.Design.' + name + '\n'


def static_data():
    native = polynomial_data()
    models = [group[0] for group in native] + [ShiftedStrength(native).diff[0]]
    polynomials = list(sparse_fields())
    polynomials.append(polynomials[0] + [
        (-HEIGHTS[0]*comb(7, j)*R0**(7-j), (j, 0, 0, 0)) for j in range(8)])
    return weighted_channels(polynomials, models)


def weighted_channels(polynomials, models):
    result = []
    for p, groups in zip(polynomials, models, strict=True):
        exact = defaultdict(F)
        for q, (u, z, c, s) in p:
            for k, weight in harmonic_terms(c, s):
                if weight.lo != weight.hi:
                    raise ValueError('inexact Fourier basis weight')
                exact[k, u, z] += q*F(weight.lo, S)
        channels = []
        for k, rows in groups.items():
            table = []
            for z, row in zip(reversed(range(len(rows))), rows, strict=True):
                pairs = []
                for u, m in zip(reversed(range(len(row))), row, strict=True):
                    q = exact.pop((k, u, z), 0)
                    if len(m.a) != 1 or abs(SCALE*q-m.a[0]) > m.e:
                        raise ValueError('native spatial weight misses the exact coefficient')
                    pairs.append((q, m))
                table.append(pairs)
            channels.append((k, table))
        if any(exact.values()):
            raise ValueError('unrepresented harmonic coefficient')
        result.append(channels)
    return result


def emit_static(k, channels):
    return emit_static_field('DommaschkNativeActionData' + FIELDS[k], SP_FIELDS[k], channels)


def emit_static_field(name, target, channels):
    src = header(name, ['PlasmaLean.Design.DommaschkNativeActionModel'])
    rows = []
    for w, group in channels:
        rnames = []
        for j, row in enumerate(group):
            rn = f'row{w}_{j}'
            digits = [f'⟨({q}), ({m.a[0]}), {m.e}, by kernel_fact⟩' for q, m in row]
            src += f'def {rn} : List Weight := [\n  ' + ',\n  '.join(digits) + ']\n'
            rnames.append(rn)
        src += f'def channel{w} : WeightedRows := [' + ', '.join(rnames) + ']\n'
        rows.append(f'(.{WAVES[w]}, channel{w})')
    src += 'def channels : WeightedChannels := [' + ', '.join(rows) + ']\n\n'
    src += f'''theorem physical_identity (u z θ : ℝ) :
    value u z θ (exactChannels channels) = evR u z (Real.cos θ) (Real.sin θ) {target} := by
  rw [← expand_sound]
  exact congrArg (evR u z (Real.cos θ) (Real.sin θ))
    (sameTerms_sound (p := expand (exactChannels channels)) (q := {target}) (by kernel_fact))
'''
    return name, src + footer(name), ['physical_identity']


def verify_static(a, data):
    out = []
    for i in a.fields:
        module = emit_static(i, data[i])
        name = module[0]
        result = compile_modules(a.cache/name, [module], [],
                                 [DATA_PACKAGE, digest(DESIGN/'DommaschkNativeActionModel.trace')],
                                 a, DATA_PACKAGE)
        out.append(result)
        print(f'{name}: {result[1]["wall_seconds"]} seconds, {result[1]["peak_rss_kib"]} KiB', flush=True)
    return out


def row_inputs(i, trace, secondary=None):
    item = segment(trace, i)
    if secondary is not None:
        item = replace(item, outgoing_radius=max(item.outgoing_radius, secondary['steps'][i]['physical_radius_out']))
    (r, z), angles = item.models()
    return r, r - R0M, z, angles


def signed_prefix(i, sign, paired):
    dr = 'Paired' if paired else ('Forward' if sign == 1 else 'Backward')
    return f'DommaschkNativeAction{dr}{i:03}'


def emit_input(i, sign, ins, paired=False):
    r, u, z, angles = ins
    name = signed_prefix(i, sign, paired) + 'Inputs'
    tag = 'Fwd' if sign == 1 else 'Back'
    harmonic = f'DommaschkHarmonicBlock{i//8:02}'
    phi = 't' if sign == 1 else '(-t)'
    back = 'false' if sign == 1 else 'true'
    imports = ['PlasmaLean.Design.DommaschkNativeActionModel',
                        'PlasmaLean.Design.DommaschkPreMirrorSigns',
                        'PlasmaLean.Design.' + harmonic, 'PlasmaLean.Design.DommaschkPositionFrames' + tag]
    if paired:
        imports.append('PlasmaLean.Design.DommaschkPositionFramesBack')
    src = header(name, imports)
    src += 'open Certificates.PositionFrameSlabs Certificates.TrajectoryHarmonicPacket\n'
    src += f'def row : Step := DommaschkPositionFrames{tag}.block{i//16}[{i%16}]\n'
    for n, m in [('radius', r), ('displacement', u), ('vertical', z)]:
        src += f'def {n} : Model := {model_literal(m)}\n'
    src += 'def phase : Wave → Model\n'
    for j, w in enumerate(WAVES):
        src += f'  | .{w} => {model_literal(angles[j])}\n'
    src += 'def coords : Inputs := ⟨displacement, vertical, phase .cos1, phase .sin1⟩\n'
    # These models use the original direction itself, including its signed z coefficients.
    src += f'''theorem space {{prev : State}} {{t : ℝ}} {{x : Plane}}
    (hx : x ∈ (physicalSlab prev row ({i}/64)).tube t) :
    radius.Mem (128*t-{2*i+1}) (x 0) ∧ displacement.Mem (128*t-{2*i+1}) (x 0 - dkR0) ∧
    vertical.Mem (128*t-{2*i+1}) (x 1) := by
  have h : DommaschkPreMirrorSigns.Matches false row radius coords := by
    constructor
    · apply eq_of_beq; kernel_fact
    · apply eq_of_beq; kernel_fact
    · apply eq_of_beq; kernel_fact
    · kernel_fact
    · kernel_fact
    · kernel_fact
  have clock : coord ({i}/64) t = 128*t-{2*i+1} := by unfold coord; ring
  simpa only [clock, coords, Bool.false_eq_true, ↓reduceIte] using h.mem hx

theorem angles {{t : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64)) (w : Wave) :
    (phase w).Mem (128*t-{2*i+1}) (w.value (2*{phi})) := by
  cases w
  · have h : Matches (constant 1) (phase .one) := {MATCH}
    rw [← h.eq]
    simpa only [Wave.value, Rat.cast_one] using constant_mem 1 (128*t-{2*i+1})
'''
    for n in range(1, 7):
        k, sine = (n-1)//2, 'true' if n%2 else 'false'
        argument = f'(2*{phi})' if k==0 else f'({k+1}*(2*{phi}))'
        src += f'''  · have ht' : t ∈ Set.Icc ((({i}:ℕ):ℝ)/64) (((({i}:ℕ):ℝ)+1)/64) := by
      norm_num at ht ⊢; exact ht
    have h := Certificates.TrajectoryHarmonicPacket.physical
      (i := {i}) ({harmonic}.packet {i%8}) {back} ({k} : Fin 3) {sine} ht'
    rw [show (2*((({i} : ℕ) : ℝ))+1) = {2*i+1} by norm_num,
      show 2*((({k}:Fin 3).val : ℝ)+1)*(if {back} then -t else t) = {argument} by norm_num <;> ring] at h
    exact h
'''
    thms = ['space', 'angles']
    if paired:
        src += f'''def backRow : Step := DommaschkPositionFramesBack.block{i//16}[{i%16}]
theorem back_space {{prev : State}} {{t : ℝ}} {{x : Plane}}
    (hx : x ∈ (physicalSlab prev backRow ({i}/64)).tube t) :
    radius.Mem (128*t-{2*i+1}) (x 0) ∧ displacement.Mem (128*t-{2*i+1}) (x 0 - dkR0) ∧
    vertical.Mem (128*t-{2*i+1}) (-(x 1)) := by
  have h : DommaschkPreMirrorSigns.Matches true backRow radius coords := by
    constructor
    · apply eq_of_beq; kernel_fact
    · apply eq_of_beq; kernel_fact
    · apply eq_of_beq; kernel_fact
    · kernel_fact
    · kernel_fact
    · kernel_fact
  have clock : coord ({i}/64) t = 128*t-{2*i+1} := by unfold coord; ring
  simpa only [clock, coords, ↓reduceIte] using h.mem hx
'''
        thms.append('back_space')
    return name, src + footer(name), thms


MATCH = 'by constructor <;> apply eq_of_beq <;> kernel_fact'


def horner_proof(variable, models, name, *, degree=None):
    acc, *rest = models
    prefix='DommaschkVariableHorner.' if degree is not None else ''
    src = ''
    lines = []
    for j, c in enumerate(rest):
        acc = (acc*variable if degree is None else acc.product(variable,degree)) + c
        v = f'{name}_at{j+1}'
        src += f'private def {v} : Model := {model_literal(acc)}\n'
        lines.append(f'  apply {prefix}Steps.cons (v := {v}) ({MATCH})\n')
    src += f'def {name} : Model := {model_literal(acc)}\n'
    return acc, src, ''.join(lines) + f'  exact {prefix}Steps.nil _\n'


def emit_field(i, sign, k, channels, ins, input_name, paired=False):
    name = signed_prefix(i, sign, paired) + FIELDS[k]
    data = 'DommaschkNativeActionData' + FIELDS[k]
    return emit_horner_field(name, SP_FIELDS[k], channels, ins, data, input_name, DATA_PACKAGE, INPUT_PACKAGE)


def emit_horner_field(name, symbol, channels, ins, data, input_name, data_package, input_package, *, degree=None):
    _, u, z, angles = ins
    extra=['PlasmaLean.Design.DommaschkVariableHorner'] if degree is not None else []
    prefix='DommaschkVariableHorner.' if degree is not None else ''
    run=prefix+'Run'+(f' (⟨{degree},80⟩ : Format)' if degree is not None else '')
    format_arg=f' (F := ⟨{degree},80⟩)' if degree is not None else ''
    src = header(name, [data_package+'.'+data, input_package+'.'+input_name,*extra])
    src += f'open {input_name}\n'
    amplitudes = {}
    for w, group in channels:
        row_values = []
        for j, row in enumerate(group):
            rn, coeffs = f'amp{w}row{j}', f'{data}.row{w}_{j}'
            y, defs, proof = horner_proof(u, [m for _, m in row], rn,degree=degree)
            row_values.append(y)
            src += defs + f'''private theorem {rn}_run : {run} displacement ({coeffs}.map Weight.model) {rn} := by
  apply {prefix}Run.cons
{proof}'''
        amp = f'amp{w}'
        model, defs, proof = horner_proof(z, row_values, amp,degree=degree)
        amplitudes[w] = model
        src += defs + f'private theorem {amp}_run : {run} vertical [' + ', '.join(
            f'{amp}row{j}' for j in range(len(group))) + f'] {amp} := by\n  apply {prefix}Run.cons\n' + proof
        src += f'''private theorem {amp}_sound {{s u z : ℝ}} (hs : |s| ≤ 1)
    (hu : displacement.Mem s u) (hz : vertical.Mem s z) :
    {amp}.Mem s (rowsValue u z (exactRows {data}.channel{w})) := by
  apply {prefix}rows_mem {amp}_run hs hz
'''
        for j in range(len(group)):
            src += f'  refine .cons ?_ ?_\n  · exact {prefix}row_mem {amp}row{j}_run hs hu\n'
        src += '  exact .nil\n'
    partial = ZERO
    tails = []
    for w, _ in reversed(channels):
        partial = (amplitudes[w]*angles[w] if degree is None else amplitudes[w].product(angles[w],degree)) + partial
        src += f'private def tail{w} : Model := {model_literal(partial)}\n'
        tails.append(f'tail{w}')
    src += f'''def model : Model := {model_literal(partial)}
theorem sound {{s u z θ : ℝ}} (hs : |s| ≤ 1) (hu : displacement.Mem s u)
    (hz : vertical.Mem s z) (ha : ∀ w, (phase w).Mem s (w.value θ)) :
    model.Mem s (evR u z (Real.cos θ) (Real.sin θ) {symbol}) := by
  rw [← {data}.physical_identity]
'''
    for (w, _), tail in zip(channels, list(reversed(tails))[1:] + ['(constant 0)'], strict=True):
        src += f'  apply {prefix}channel_cons{format_arg} (tail := {tail}) hs (amp{w}_sound hs hu hz) (ha .{WAVES[w]}) ?_ ({MATCH})\n'
    src += '  simpa only [exactChannels, List.map_nil, value, Rat.cast_zero] using constant_mem 0 s\n'
    return (name, src + footer(name), ['sound']), partial


def emit_physical(i, sign, ins, inp, field_results, values, paired=False):
    name = signed_prefix(i, sign, paired)
    phi = 't' if sign == 1 else '(-t)'
    providers = [field[1]['module'] for field in field_results]
    geometry = 'DommaschkNativeActionReflection' if paired else 'DommaschkNativeActionGeometry'
    src = header(name, ['PlasmaLean.Design.'+geometry, INPUT_PACKAGE+'.'+inp,
                        *[FIELD_PACKAGE+'.'+p for p in providers]])
    src += 'open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkMirrorTubeCrossing\n'
    src += 'open DommaschkFirstMirrorLaunchSign DommaschkNativeActionGeometry\n'
    src += f'abbrev row := {inp}.row\n'
    cols = dict(zip(('den', 'nr', 'nz', 'shifted'), values, strict=True))
    cols['radius'] = ins[0]
    src += f'def den : Model := {providers[0]}.model\n'
    hw = Model.rational(HEIGHTS[0]**2 - HEIGHTS[1]**2)
    cols['coefficient'] = hw
    src += f'def coefficient : Weight := ⟨(height false)^2-(height true)^2, ({hw.a[0]}), {hw.e}, by kernel_fact⟩\n'
    operations = [
        ('r2', '*', 'radius', 'radius'), ('r4', '*', 'r2', 'r2'), ('r8', '*', 'r4', 'r4'),
        ('r16', '*', 'r8', 'r8'), ('rd', '*', 'radius', 'den'), ('rdSq', '*', 'rd', 'rd'),
        ('nrSq', '*', 'nr', 'nr'), ('nzSq', '*', 'nz', 'nz'), ('poloidal', '+', 'rdSq', 'nrSq'),
        ('u', '+', 'poloidal', 'nzSq'), ('twoD', '+', 'den', 'den'),
        ('minusShift', '-', 'shifted', None), ('plus', '+', 'twoD', 'minusShift'),
        ('scaledShift', '*', 'r2', 'shifted'), ('torGap', '*', 'scaledShift', 'plus'),
        ('radGap', '+', 'torGap', 'nrSq'), ('base', '+', 'radGap', 'nzSq'),
        ('adjust', '*', 'r16', 'coefficient'), ('gap', '+', 'base', 'adjust'),
        ('num', '-', 'gap', None)]
    checked = []
    for key, op, x, y in operations:
        if op == '*':
            m, proof = cols[x]*cols[y], f'checked_product (out := {key}) hs h_{x} h_{y}'
        elif op == '+':
            m, proof = cols[x]+cols[y], f'checked_sum (out := {key}) h_{x} h_{y}'
        else:
            m, proof = -cols[x], f'checked_neg (out := {key}) h_{x}'
        cols[key] = m
        src += f'def {key} : Model := {model_literal(m)}\n'
        checked.append(f'  have h_{key} := {proof} ({MATCH})\n')
    def conclusion(phase):
        return f'''    0 < x 0 ∧ den.Mem (128*t-{2*i+1}) (atPoint dD (x 0) {phase} (x 1)) ∧
    r8.Mem (128*t-{2*i+1}) ((x 0)^8) ∧ r16.Mem (128*t-{2*i+1}) ((x 0)^16) ∧
    u.Mem (128*t-{2*i+1}) ((x 0)^16 * (strength {phase} x)^2) ∧
    num.Mem (128*t-{2*i+1}) ((x 0)^16 * (((height true : ℚ) : ℝ)^2-(strength {phase} x)^2)) := by
'''
    def hypotheses(thm, row):
        return f'''theorem {thm} {{prev : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {row} ({i}/64)).tube t) :
'''
    def positivity(row):
        return f'''  have hr : 0 < x 0 := DommaschkMirrorBracketSlab.positive_radius (a := {i}/64) (r := {row})
    (by rwa [show ({i}/64:ℝ)+1/64 = {i+1}/64 by norm_num]) hx (by kernel_fact) (by kernel_fact)
'''
    if paired:
        src += f'''abbrev backRow := {inp}.backRow
private theorem at_coordinates {{t : ℝ}} {{x : Plane}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hr : 0 < x 0) (h_radius : {inp}.radius.Mem (128*t-{2*i+1}) (x 0))
    (hu : {inp}.displacement.Mem (128*t-{2*i+1}) (x 0-dkR0))
    (hz : {inp}.vertical.Mem (128*t-{2*i+1}) (x 1)) :
'''
    else:
        src += hypotheses('physical', 'row')
    src += conclusion(phi) + f'''  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
'''
    if paired:
        src += f'  have ha := {inp}.angles ht\n'
    else:
        src += f'''  obtain ⟨h_radius,hu,hz⟩ := {inp}.space hx
  have ha := {inp}.angles ht
''' + positivity('row')
    src += f'  have h_coefficient := coefficient.mem (128*t-{2*i+1})\n'
    for key, provider, target in zip(('den', 'nr', 'nz', 'shifted'), providers, SP_FIELDS, strict=True):
        if key == 'shifted':
            target = '(DommaschkCompensatedAction.shiftedD (height false))'
        src += f'  have h_{key} := {provider}.sound hs hu hz ha\n'
        src += f'  change {provider}.model.Mem _ (atPoint {target} (x 0) {phi} (x 1)) at h_{key}\n'
    src += ''.join(checked)
    src += f'''  refine ⟨hr, h_den, ?_, ?_, ?_, ?_⟩
  · convert h_r8 using 1 <;> ring
  · convert h_r16 using 1 <;> ring
  · rw [← squared_numerator hr]
    convert h_u using 1 <;> ring
  · rw [← compensated_numerator hr {phi} (height false) (height true)]
    change num.Mem _ (-(_ + _ * (((height false)^2 - (height true)^2 : ℚ) : ℝ))) at h_num
    convert h_num using 1 <;> ring
'''
    thms = ['physical']
    if paired:
        src += hypotheses('physical', 'row') + conclusion('t') + positivity('row') + f'''  obtain ⟨r,u,z⟩ := {inp}.space hx
  exact at_coordinates ht hr r u z
'''
        src += hypotheses('backward_physical', 'backRow') + conclusion('(-t)') + positivity('backRow')
        src += f'''  obtain ⟨r,u,z⟩ := {inp}.back_space hx
  have h := at_coordinates (x := DommaschkJacobianReflection.flip x) ht
    (by simpa only [DommaschkJacobianReflection.flip_zero] using hr)
    (by simpa only [DommaschkJacobianReflection.flip_zero] using r)
    (by simpa only [DommaschkJacobianReflection.flip_zero] using u)
    (by simpa only [DommaschkJacobianReflection.flip_one] using z)
  rw [DommaschkNativeActionReflection.denominator, DommaschkNativeActionReflection.norm hr]
  simpa only [DommaschkJacobianReflection.flip_zero] using h
'''
        thms.append('backward_physical')
    return (name, src + footer(name), thms)


def verify_row(a, data, static):
    packet = json.loads(gzip.decompress(RECORD.read_bytes()))
    trace = next(t for t in packet['traces'] if t['direction'] == a.direction)
    other = next(t for t in packet['traces'] if t['direction'] == -1) if a.paired else None
    ins = row_inputs(a.row, trace, other)
    inp = emit_input(a.row, a.direction, ins, a.paired)
    n = inp[0]
    dep = [digest(DESIGN/(name+'.trace')) for name in (
        'DommaschkNativeActionModel', 'DommaschkPreMirrorSigns', f'DommaschkHarmonicBlock{a.row//8:02}',
        'DommaschkPositionFrames'+('Fwd' if a.direction == 1 else 'Back'))]
    inp_result = compile_modules(a.cache/n, [inp], [], [INPUT_PACKAGE, digest(RECORD), dep], a, INPUT_PACKAGE)
    fields = []
    values = []
    for k, sta in zip(a.fields, static, strict=True):
        item, out = emit_field(a.row, a.direction, k, data[k], ins, n, a.paired)
        field = compile_modules(a.cache/item[0], [item], [union(a.cache, [sta, inp_result])],
                                [FIELD_PACKAGE, sta[1]['key'], inp_result[1]['key']], a, FIELD_PACKAGE)
        print(f'{item[0]}: {field[1]["wall_seconds"]} seconds, {field[1]["peak_rss_kib"]} KiB', flush=True)
        fields.append(field)
        values.append(out)
    proof = []
    if list(a.fields) == list(range(4)):
        item = emit_physical(a.row, a.direction, ins, n, fields, values, a.paired)
        geometry = 'DommaschkNativeActionReflection' if a.paired else 'DommaschkNativeActionGeometry'
        dependencies = [*static, inp_result, *fields]
        physical = compile_modules(a.cache/item[0], [item], [union(a.cache, dependencies)],
                                   [OUTPUT_PACKAGE, digest(DESIGN/(geometry+'.trace')),
                                    *[m['key'] for _, m in dependencies]], a, OUTPUT_PACKAGE)
        proof = [physical]
    return [inp_result, *fields, *proof]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--fields', nargs='+', type=int, choices=range(4), default=range(4))
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/native-action-checks')
    p.add_argument('--row', type=int, choices=range(325), metavar='0..324')
    p.add_argument('--direction', type=int, choices=(-1, 1), default=1)
    p.add_argument('--paired', action='store_true', help='enclose both signed physical tubes with one spatial evaluation')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if a.paired and a.direction != 1:
        p.error('--paired uses the positive spatial orientation')
    def lake(*args):
        return subprocess.check_output(['lake', 'env', *args], cwd=ROOT, text=True).strip()
    a.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv', 'LEAN_PATH')
    data = static_data()
    res = verify_static(a, data)
    signed = verify_row(a, data, res) if a.row is not None else []
    if a.output:
        save(a.output, manifest(a, res, signed))


def manifest(a, static, signed):
    return {'signed_archive': digest(RECORD), 'imports': str(union(a.cache, [*static, *signed]).resolve()),
            'physical_identities': [r for _, r in static], 'signed_model_proofs': [r for _, r in signed]}


if __name__ == '__main__':
    main()
