"""Emit the three physical field Taylor certificates on the first forward N-60 slab."""
import argparse
from fractions import Fraction
import gzip
import json
from math import ceil
from pathlib import Path

from bounce_mirror_pilot import Model, ONE, ORDER, R0M, SCALE, ZERO, angle_models
from emit_bounce_tubes import DATA, coefficients


ROOT = Path(__file__).resolve().parents[2]
RECORD = Path(__file__).with_name('results') / 'bounce_frame_q0_u470.json.gz'
DEST = ROOT / 'PlasmaLean/Design'
STEM = 'DommaschkBounceTaylorFirst'
BLOCK = 12


def model_literal(model):
    return 'ofDyadic 80 [' + ', '.join(map(str, model.a)) + f'] ({model.e})'


def weighted(model, q):
    """Apply one exact sparse coefficient before the sole final dyadic rounding."""
    exact = [q * value for value in model.a]
    rounded = [value.numerator // value.denominator for value in exact]
    error = abs(q) * model.e + sum(value - digit for value, digit in zip(exact, rounded))
    return Model(rounded, ceil(error))


def inputs():
    with gzip.open(RECORD, 'rt') as fp:
        packet = json.load(fp)
    if (packet['coordinate_denominator'] != SCALE or packet['order'] != ORDER or
            packet['step'] != '1/64' or packet['launch_u'] != '47/100' or
            packet['section_in_half_pi'] != 0):
        raise ValueError('unexpected long-trace witness')
    trace, = (row for row in packet['traces'] if row['direction'] == 1)
    step = trace['steps'][0]
    if step['index'] != 0:
        raise ValueError('missing initial forward step')
    radius, z = [Model(row, step['physical_trial_radius']) for row in step['coefficients']]
    angles = angle_models(Fraction(1, 128), Fraction(1, 128), Fraction(0))
    return radius - R0M, z, angles[2], angles[1]


def models(terms, columns):
    powers = []
    for axis, column in enumerate(columns):
        values = [ONE]
        for _ in range(max(exponents[axis] for _, exponents in terms)):
            values.append(values[-1] * column)
        powers.append(values)
    results = []
    for start in range(0, len(terms), BLOCK):
        total = ZERO
        for q, (i, j, k, n) in terms[start:start + BLOCK]:
            term = powers[0][i] * powers[1][j] * powers[2][k] * powers[3][n]
            total += weighted(term, q)
        results.append(total)
    return results


def field(name, columns, input_name='trial'):
    terms = coefficients(DATA.read_text(), name)
    blocks = models(terms, columns)
    lines = []
    tail = ZERO
    suffix = '(constant 0)'
    for j in reversed(range(len(blocks))):
        start = j * BLOCK
        tag = f'{name}{start}'
        head = blocks[j]
        out = head + tail
        lines.extend([
            f'/-- Taylor enclosure of the sparse suffix starting at term {start}. -/',
            f'def {tag} : Model := {model_literal(out)}',
            f'private theorem {tag}_checked :',
            f'    Blocks ⟨7,80⟩ {input_name} ({name}.drop {start}) {tag} := by',
            f'  apply Blocks.chunk {BLOCK} ({model_literal(head)}) {suffix}',
            '  · constructor <;> apply eq_of_beq <;> kernel_fact',
        ])
        if j == len(blocks) - 1:
            lines.append('  · exact Blocks.nil')
        else:
            lines.append(f'  · exact {suffix}_checked')
        lines.extend(['  · constructor <;> apply eq_of_beq <;> kernel_fact', ''])
        tail, suffix = out, tag
    lines.extend([
        f'/-- Checked Taylor enclosure for every term of the original {name} polynomial. -/',
        f'theorem {name}_checked : Blocks ⟨7,80⟩ {input_name} {name} {name}0 := {name}0_checked',
        '',
    ])
    lo, hi = tail.bound()
    lo = lo.numerator * SCALE // lo.denominator
    hi = hi.numerator * SCALE // hi.denominator
    tail_sum = sum(map(abs, tail.a[1:]))
    lines.extend([
        f'/-- Real range follows from the constant coefficient and all nonconstant terms. -/',
        f'theorem {name}_range {{t y : ℝ}} (ht : |t| ≤ 1) (h : {name}0.Mem t y) :',
        f'    ({lo} : ℝ) / 2^80 ≤ y ∧ y ≤ ({hi} : ℝ) / 2^80 := by',
        f'  have hr := dyadic_range ht (show ({model_literal(tail)}).Mem t y from h)',
        '  have mass : (magnitude',
        '      (' + str(tail.a[1:]) + f'.map fun (z : ℤ) => (z : ℚ))) = {tail_sum} :=',
        '    eq_of_beq (by kernel_fact)',
        '  rw [mass, abs_le] at hr',
        '  norm_num at hr ⊢',
        '  constructor <;> linarith',
        '',
    ])
    return '\n'.join(lines)


def emit():
    columns = inputs()
    header = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceTaylor

/-!
# First forward QA2R field-model certificate

The N-60 endpoint is the phase-zero sector at launch radius 47/100. The first
forward slab uses the exported trial radius. Each directed physical field
enclosure applies whenever the four input models enclose the trajectory.
Generated by `scripts/dommaschk_kam/emit_sparse_taylor_slab.py`.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkBounceTaylorFirst

open PlasmaLean.Certificates.TrajectoryTaylorModel DommaschkKam DommaschkBounceTaylor

set_option linter.style.longLine false
set_option Elab.async false
set_option maxRecDepth 16000

/-- First forward reference trajectory, two trial radii and the angle models
on t ∈ [-1,1] corresponding to geometric angle (1+t)/128. -/
def trial : Inputs := ⟨'''
    tail = '''/-- All three enclosures concern the actual candidate field components
at the same cylindrical point. Input membership is explicit. -/
theorem physical_ranges {t R z φ : ℝ} (ht : |t| ≤ 1) (hR : 0 < R)
    (h : trial.Mem t (R - dkR0) z (Real.cos (2 * φ)) (Real.sin (2 * φ))) :
    1 < R ^ 7 * cylBphi R φ z ∧ |R ^ 8 * cylBR R φ z| ≤ 1/1000 ∧
      -77/1000 ≤ R ^ 8 * cylBz R φ z ∧ R ^ 8 * cylBz R φ z ≤ -76/1000 := by
  obtain ⟨hd,hr,hz⟩ := DommaschkBounceField.field_id hR φ z
  rw [← hd, ← hr, ← hz, abs_le]
  have D := dD_range ht (dD_checked.mem ht h)
  have Nr := dnR_range ht (dnR_checked.mem ht h)
  have Nz := dnZ_range ht (dnZ_checked.mem ht h)
  unfold DommaschkBounceField.atPoint
  norm_num at D Nr Nz
  exact ⟨by linarith [D.1], ⟨by linarith [Nr.1], by linarith [Nr.2]⟩,
    by linarith [Nz.1], by linarith [Nz.2]⟩

/-- For the first actual forward clock the radius and height tube enclosures
suffice. Both harmonic models and positivity of the cylindrical radius follow. -/
theorem physical_clock_ranges {t R z : ℝ} (ht : t ∈ Set.Icc 0 (1 / 64))
    (hu : trial.u.Mem (128 * t - 1) (R - dkR0)) (hz : trial.z.Mem (128 * t - 1) z) :
    1 < R ^ 7 * cylBphi R t z ∧ |R ^ 8 * cylBR R t z| ≤ 1/1000 ∧
      -77/1000 ≤ R ^ 8 * cylBz R t z ∧ R ^ 8 * cylBz R t z ≤ -76/1000 := by
  have hs : |128*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have radial := enclose (c := ⟨[1/10], 1/20⟩) hs hu (by kernel_fact)
  have hr : 0 < R := by
    norm_num [Model.Mem, dkR0, Certificates.QPoly.eval_cons, Certificates.QPoly.eval_nil,
      abs_le] at radial
    linarith
  have hc : t ∈ Set.Icc (0/64:ℝ) (1/64) := by simpa using ht
  apply physical_ranges hs hr
  refine ⟨hu, hz, ?_, ?_⟩
  · change (DommaschkHarmonicSlab0.model false 0 false).Mem _ _
    simpa [Certificates.TrajectoryTrig.wave] using
      DommaschkHarmonicSlab0.physical false 0 false hc
  · change (DommaschkHarmonicSlab0.model false 0 true).Mem _ _
    simpa [Certificates.TrajectoryTrig.wave] using
      DommaschkHarmonicSlab0.physical false 0 true hc

end PlasmaLean.Design.DommaschkBounceTaylorFirst
'''
    finish = 'end PlasmaLean.Design.DommaschkBounceTaylorFirst\n'
    models_header = header.split('/-- First forward reference')[0]
    files = {STEM + 'Inputs': header + ',\n  '.join(model_literal(m) for m in columns) +
             '⟩\n\n' + finish}
    imports = ['public import PlasmaLean.Design.DommaschkHarmonicSlab0']
    for name in ('dD', 'dnR', 'dnZ'):
        module = STEM + {'dD': 'D', 'dnR': 'R', 'dnZ': 'Z'}[name]
        imports.append('public import PlasmaLean.Design.' + module)
        prefix = models_header.replace('public import PlasmaLean.Design.DommaschkBounceTaylor\n',
                                       'public import PlasmaLean.Design.' + STEM + 'Inputs\n')
        files[module] = prefix + field(name, columns) + '\n' + finish
    files[STEM] = models_header.replace('public import PlasmaLean.Design.DommaschkBounceTaylor\n',
                                       '\n'.join(imports) + '\n') + tail
    return files


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, text in emit().items():
        path = DEST / (name + '.lean')
        if args.check:
            if path.read_text() != text:
                raise SystemExit('regenerate ' + path.name)
        else:
            path.write_text(text)
