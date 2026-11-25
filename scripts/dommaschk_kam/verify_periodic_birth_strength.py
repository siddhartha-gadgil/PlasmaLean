"""Verify the Q16 interpolated birth strength over a full toroidal period."""
import argparse
from fractions import Fraction as F
from math import ceil, factorial
from pathlib import Path
from types import SimpleNamespace

from bounce_launch_box import profile_coefficients
from bounce_mirror_pilot import Model, SCALE, angle_models
from emit_trig_slab import CENTRE_SCALE, scalar_centre, verify_rotated
from emit_sparse_taylor_slab import model_literal
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_grouped_mirror_exclusion import GAPS
from verify_harmonic_group_exclusion import FIELDS_PACKAGE, INPUT, field_margins, inputs, result
from verify_native_action_models import DATA_PACKAGE, FIELDS, SP_FIELDS, emit_horner_field, static_data, verify_static
from verify_mirror_endpoint_signs import header
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


SPANS = [(a, min(a + 16, 202)) for a in range(0, 202, 16)]
PHASE = 'PeriodicBirthPhaseCache'


def physical_inputs(a, b, profiles):
    angles = angle_models(F(a + b, 128), F(b - a, 128), F(0))
    anchors = []
    for j in range(1, 4):
        w = F((b - a) * j, 64)
        centre = [scalar_centre(sine, F((a + b) * j, 64)) for sine in (False, True)]
        anchors.append(centre)
        for sine in (False, True):
            model = angles[2*j - sine]
            model.e += ceil(SCALE * (4*abs(w)**10/factorial(10) + F(1, 2**88)))
            verify_rotated(model, sine, F(centre[0][1], CENTRE_SCALE),
                           F(centre[1][1], CENTRE_SCALE), w)
    coordinates, coefficients = [], []
    for key, error in [('R', F(1, 1200)), ('z', F(1, 3800))]:
        inner, outer = [p[key, False][1] for p in profiles]
        central = [(51*c + 49*d)/100 for c, d in zip(inner[:4], outer[:4], strict=True)]
        if key == 'z':
            central[0] = F(0)
        value = Model.rational(central[0]) + Model([0], ceil(SCALE*error) + 64)
        for j in range(1, 4):
            value += Model.rational(central[j])*angles[2*j - (key == 'z')]
        coordinates.append(value)
        coefficients.append(central)
    return [*coordinates, angles[2], angles[1]], angles, anchors, coefficients


def verify_field(name, tube, args):
    source, coordinates = inputs(name + 'Inputs', tube)
    ir = compile_modules(args.cache/source[0], [source], [], args.keys, args, INPUT)
    packages, values, fields = [ir, *args.static], [], []
    for i, channels in enumerate(args.channels):
        static = args.static[i]
        field, value = emit_horner_field(name+FIELDS[i], SP_FIELDS[i], channels, coordinates,
                                         static[1]['module'], source[0], DATA_PACKAGE, INPUT,
                                         integer=True)
        checked = compile_modules(args.cache/field[0], [field], [ir[0], static[0]],
                                  [args.keys, ir[1]['key'], static[1]['key']], args, FIELDS_PACKAGE)
        fields.append(checked)
        values.append(value)
    packages.extend(fields)
    closed, upper = result(name, source[0], tube, fields, values, False, F(0))
    packages.append(compile_modules(args.cache/name, [closed], [union(args.cache, packages)],
                                    [args.keys, [p[1]['key'] for p in packages]], args, GAPS))
    return packages, upper


def phase_source(name, a, b, angles, anchors, coefficients):
    top = name + 'Physical'
    src = header(top, [GAPS+'.'+name, 'PlasmaLean.Design.DommaschkPeriodicBirthCover'])
    src += ('open Certificates.TrajectoryHarmonicPacket DommaschkPeriodicBirthCover\n'
            'open DommaschkPeriodicBirthFourier\n')
    for j, centre in enumerate(anchors, 1):
        (dc, c), (ds, s) = centre
        mid, width = F((a+b)*j,64), F((b-a)*j,64)
        src += f'''private def pair{j} : Pair ({mid}) ({width}) :=
  ⟨⟨{c}, {dc}, by kernel_fact⟩, ⟨{s}, {ds}, by kernel_fact⟩,
   {model_literal(angles[2*j])}, {model_literal(angles[2*j-1])},
   by kernel_fact, by kernel_fact⟩
'''
    src += f'''theorem resolved : Sector ({a}/64) ({b}/64) := by
  intro t ht R z φ hR hz hcos hsin
  let s : ℝ := (128*t-{a+b})/{b-a}
  have hs : |s| ≤ 1 := by dsimp [s]; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
'''
    for j in range(1, 4):
        mid, width = F((a+b)*j,64), F((b-a)*j,64)
        src += f'''  have h{j} (v : Bool) : (pair{j}.model v).Mem s (wave v ({2*j}*t)) := by
    have h := pair{j}.sound v hs
    have clock : (({mid} : ℚ) : ℝ) + (({width} : ℚ) : ℝ)*s = {2*j}*t := by
      dsimp [s]; norm_num; ring
    rw [clock] at h
    cases v <;> exact h
'''
    for coordinate, sine, error, hyp, target in [('r','false',F(1,1200),'hR','radial'),
                                                  ('z','true',F(1,3800),'hz','height')]:
        qs = coefficients[int(sine=='true')]
        for j,q in enumerate(qs):
            src += f'  have {coordinate}{j} : coeff {sine} {j} = ({q} : ℚ) := by kernel_fact\n'
        cs = ','.join(f'{coordinate}{j}' for j in range(4))
        src += f'  rw [low_eq,{cs}] at {hyp}\n'
        src += f'  have {coordinate}mem : {name}Inputs.group.{target}.Mem s {("R" if sine=="false" else "z")} := by\n'
        src += '    apply linear_mem ' + ' '.join(f'(q{j} := ({q}))' for j,q in enumerate(qs))
        src += f' (e := ({error})) hs (h1 {sine}) (h2 {sine}) (h3 {sine})\n'
        src += f'    · simpa only [error,↓reduceIte,Bool.false_eq_true,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using {hyp}\n'
        src += '    · kernel_fact\n'
    src += f'''  have bounded := enclose (c := ⟨[1],1/2⟩) hs rmem (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at bounded
  apply {name}.below hs (by linarith only [bounded.1]) rmem zmem
  · rw [hcos]; exact h1 false
  · rw [hsin]; exact h1 true
end PlasmaLean.Design.{top}
'''
    return top,src,['resolved']


def complete(groups, packages, args):
    name = 'DommaschkPeriodicOriginalBirths'
    imports = [PHASE+'.'+p[1]['module'] for p in packages if p[1]['module'].endswith('Physical')]
    src = header(name, imports)
    src += 'open DommaschkPeriodicBirthCover\n'
    chain = groups[-1]['physical_module']+'.resolved'
    for group in reversed(groups[:-1]):
        chain = f'sector_join {group["physical_module"]}.resolved ({chain})'
    src += f'''theorem full_period : Sector 0 (202/64) := by
  have h : Sector (0/64) (202/64) := {chain}
  simpa only [zero_div] using h
theorem original_births : CommonBirths := from_period full_period
end PlasmaLean.Design.{name}
'''
    root = union(args.cache,packages)
    base, receipt = compile_modules(args.cache/name, [(name,src,['full_period','original_births'])],
        [root], [args.keys,[p[1]['key'] for p in packages]],args,'PeriodicBirthFamilyCache')
    save(args.output, {k:receipt[k] for k in ('module','key','theorems','axioms')} |
         {'kind':'original-periodic-births','groups':groups,'import_paths':[str(base),str(root)]})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/periodic-birth-strength')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--screen', action='store_true')
    parser.add_argument('--fields-only', action='store_true')
    args = parser.parse_args()
    profiles = [profile_coefficients(tag) for tag in 'CA']
    args.channels = static_data()
    groups, all_packages = [], []
    if not args.screen:
        env(args)
        args.keys = [args.version, *[digest(DESIGN/(n+'.trace')) for n in
                     ('DommaschkGroupedHarmonicGap','DommaschkCoreClearance','DommaschkDyadicHorner')]]
        args.static = verify_static(SimpleNamespace(**{**vars(args), 'cache': ROOT/'.lake/native-action-checks',
                                                        'fields': range(4)}), args.channels)
    for a, b in SPANS:
        tube, angles, anchors, coefficients = physical_inputs(a, b, profiles)
        margin = field_margins(tube, args.channels)
        if margin >= 0:
            raise ArithmeticError(f'ticks [{a}, {b}] miss the target with {margin}')
        row = {'ticks': [a,b], 'upper': str(margin)}
        if not args.screen:
            name = f'DommaschkPeriodicBirth{a:03}'
            packages, upper = verify_field(name, tube, args)
            if upper != margin:
                raise ArithmeticError('field enclosure changed during replay')
            top = packages[-1][1]
            row.update(key=top['key'], module=top['module'], axioms=top['axioms'],
                       root=str(packages[-1][0]), overlay=str(union(args.cache, packages)))
            if not args.fields_only:
                src = phase_source(name,a,b,angles,anchors,coefficients)
                phase = compile_modules(args.cache/src[0], [src], [union(args.cache,packages)],
                    [digest(DESIGN/'DommaschkPeriodicBirthCover.trace'),top['key']],args,PHASE)
                row.update(physical_module=src[0],physical_key=phase[1]['key'])
                all_packages.extend([*packages,phase])
        print(a, b, float(margin), flush=True)
        groups.append(row)
        save(args.output, {'groups': groups, 'kind': 'screen' if args.screen else 'fields'})
    if not args.screen and not args.fields_only:
        complete(groups,all_packages,args)


if __name__ == '__main__':
    main()
