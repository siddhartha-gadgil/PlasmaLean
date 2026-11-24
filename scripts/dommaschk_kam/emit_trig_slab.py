"""Emit a Lean proof of the twelve directed harmonic models on one entire time slab."""
import argparse
from fractions import Fraction as F
from itertools import zip_longest
from math import factorial
from pathlib import Path

from bounce_mirror_pilot import SCALE, angle_models


ROOT = Path(__file__).resolve().parents[2]


def comparison(sine, degree, a, w):
    """Taylor polynomial of wave(a+w*s), expanded in the normalized variable s."""
    cycle = (0, 1, 0, -1) if sine else (1, 0, -1, 0)
    coeffs = [F(cycle[degree % 4], factorial(degree))]
    for j in reversed(range(degree)):
        coeffs = [F(cycle[j % 4], factorial(j)) + a*coeffs[0],
                  *(a*coeffs[i] + w*coeffs[i-1] for i in range(1, len(coeffs))),
                  w*coeffs[-1]]
    return coeffs, (abs(a) + abs(w))**(degree+1)/factorial(degree+1)


CENTRE_SCALE = 2**96
CENTRE_ERROR = F(2, CENTRE_SCALE)
OFFSET_DEGREE = 9


def scalar_centre(sine, angle):
    cycle = (0, 1, 0, -1) if sine else (1, 0, -1, 0)
    degree = 14
    while abs(angle)**(degree+1) / factorial(degree+1) > CENTRE_ERROR/4:
        degree += 4
    approx = sum(F(cycle[j % 4], factorial(j)) * angle**j for j in range(degree+1))
    integer = round(approx * CENTRE_SCALE)
    value = F(integer, CENTRE_SCALE)
    if abs(value - approx) + abs(angle)**(degree+1)/factorial(degree+1) > CENTRE_ERROR:
        raise ArithmeticError('scalar Taylor comparison failed')
    return degree, integer


def verify_rotated(model, sine, c, z, w):
    """Mirror the two constant-times-polynomial model products in rotated_mem."""
    co, err = comparison(False, OFFSET_DEGREE, F(0), w)
    si, _ = comparison(True, OFFSET_DEGREE, F(0), w)
    a, b = (z, c) if sine else (c, -z)
    coeffs = [a*p + b*q for p, q in zip(co, si, strict=True)]
    radius = CENTRE_ERROR*(sum(map(abs, co))+sum(map(abs, si))+2*err) + (abs(a)+abs(b))*err
    original = [F(v, SCALE) for v in model.a]
    difference = sum(abs(x-y) for x, y in zip_longest(coeffs, original, fillvalue=F(0)))
    if radius + difference > F(model.e, SCALE):
        raise ArithmeticError('rotated Taylor comparison exceeds the exported radius')


def boolean(b):
    return str(bool(b)).lower()


def slab_rows(index):
    centre = 2*index+1
    data = []
    for back in (False, True):
        sign = -1 if back else 1
        angles = angle_models(sign*F(centre, 128), sign*F(1, 128), F(0))
        for j in range(3):
            f = sign*(j+1)
            # The angle centre is enclosed independently of the Python trigonometric boxes.
            anchors = [scalar_centre(sine, F(centre*f, 64)) for sine in (False, True)]
            for sine in (False, True):
                m = angles[2*j + (1 if sine else 2)]
                verify_rotated(m, sine, F(anchors[0][1], CENTRE_SCALE),
                               F(anchors[1][1], CENTRE_SCALE), F(f, 64))
                degree, integer = anchors[int(sine)]
                data.append((back, j, sine, degree, integer, m))
    return data


def emit(index):
    if not 0 <= index < SLABS:
        raise ValueError('the radial trace contains slabs 0 through 390')
    block, offset = divmod(index, BLOCK_SIZE)
    group = f'DommaschkHarmonicBlock{block:02}'
    module = f'DommaschkHarmonicSlab{index}'
    center = 2*index+1
    lines = module_header(module, [f'PlasmaLean.Design.{group}'],
                          f'Harmonic models on outward slab {index}')
    lines += ['open PlasmaLean.Certificates.TrajectoryTrig', '',
              '/-- The original directed Python coefficient and error record. -/',
              'noncomputable def model (back : Bool) (k : Fin 3) (sine : Bool) : Model :=',
              f'  ({group}.packet {offset} back k).model sine', '',
              '/-- All directed harmonics on the normalized time variable. -/',
              'theorem normalized (back : Bool) (k : Fin 3) (sine : Bool) {s : ℝ} (hs : |s| ≤ 1) :',
              f'    (model back k sine).Mem s (wave sine ((({center}*frequency back k/64 : ℚ) : ℝ) +',
              '      ((frequency back k/64 : ℚ) : ℝ)*s)) := by',
              f'  have h := ({group}.packet {offset} back k).sound sine hs',
              f'  have e : 2*(({block*BLOCK_SIZE}+({offset} : Fin {min(BLOCK_SIZE,SLABS-block*BLOCK_SIZE)}).val : ℕ) : ℚ)+1 = {center} := by kernel_fact',
              '  have clock := congrArg (fun v : ℚ => wave sine',
              '    (((v*frequency back k/64 : ℚ) : ℝ) + ((frequency back k/64 : ℚ) : ℝ)*s)) e',
              '  exact clock ▸ h', '',
              '/-- The physical signed clock on the closed time slab. -/',
              'theorem physical (back : Bool) (k : Fin 3) (sine : Bool) {t : ℝ}',
              f'    (ht : t ∈ Set.Icc ({index} / 64 : ℝ) ({index+1} / 64)) :',
              f'    (model back k sine).Mem (128*t-{center})',
              '      (wave sine (2*((k.val : ℝ)+1)*(if back then -t else t))) := by',
              f'  have hs : |128*t-{center}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩',
              '  have h := normalized back k sine hs', '  convert h using 2',
              '  cases back <;> simp [frequency] <;> ring', '', f'end PlasmaLean.Design.{module}', '']
    return module, '\n'.join(lines)


BLOCK_SIZE = 8
SLABS = 391
BLOCKS = (SLABS + BLOCK_SIZE-1) // BLOCK_SIZE


def module_header(name, imports, title):
    return ['/-', 'Copyright (c) 2026 PlasmaLean contributors. All rights reserved.',
            'Released under Apache 2.0 license as described in the file LICENSE.',
            'Authors: PlasmaLean contributors', '-/', 'module', '',
            *(f'public import {m}' for m in imports), '',
            '/-!', f'# {title}', '', 'Generated by `scripts/dommaschk_kam/emit_trig_slab.py`.', '-/',
            '', '@[expose] public section', f'namespace PlasmaLean.Design.{name}', '',
            'open PlasmaLean.Certificates.TrajectoryTaylorModel',
            'open PlasmaLean.Certificates.TrajectoryHarmonicPacket', '']


def write_model(lines, m):
    terms = [str(v) for v in m.a]
    lines.append('      ofDyadic 80')
    for i in range(0, len(terms), 3):
        start = '        [' if i == 0 else '         '
        end = ']' if i+3 >= len(terms) else ','
        lines.append(start+', '.join(terms[i:i+3])+end)
    lines.append(f'        {m.e},')


def emit_block(block):
    if not 0 <= block < BLOCKS:
        raise ValueError('harmonic block index is out of range')
    first = block*BLOCK_SIZE
    size = min(BLOCK_SIZE, SLABS-first)
    name = f'DommaschkHarmonicBlock{block:02}'
    lines = module_header(name, ['PlasmaLean.Certificates.TrajectoryHarmonicPacket'],
                          f'Directed harmonic witnesses for slabs {first} through {first+size-1}')
    lines += ['/-- All original dyadic harmonic models in this block, with their proof terms. -/',
              f'noncomputable def packet : (j : Fin {size}) → Packet ({first}+j)']
    for j in range(size):
        data = slab_rows(first+j)
        for cosine, sine in zip(data[::2], data[1::2], strict=True):
            back, k, _, dc, c, cm = cosine
            _, _, _, ds, z, sm = sine
            lines += [f'  | {j}, {boolean(back)}, {k} =>',
                      f'    ⟨⟨{c}, {dc}, by kernel_fact⟩,',
                      f'      ⟨{z}, {ds}, by kernel_fact⟩,']
            write_model(lines, cm)
            write_model(lines, sm)
            lines.append('      by kernel_fact, by kernel_fact⟩')
    return name, '\n'.join([*lines, '', f'end PlasmaLean.Design.{name}', ''])


def emit_index():
    name = 'DommaschkHarmonicTrace'
    imports = [f'PlasmaLean.Design.DommaschkHarmonicBlock{block:02}' for block in range(BLOCKS)]
    imports.insert(0, 'PlasmaLean.Certificates.TrajectoryHarmonicSections')
    lines = module_header(name, imports, 'Harmonic models on the complete two-sided mirror trace')
    lines += ['open PlasmaLean.Certificates.TrajectoryTrig', '',
              'set_option maxRecDepth 4096 in',
              '/-- Select one of the independently verified finite blocks. -/',
              'noncomputable def block : (b : Fin 49) →',
              '    (j : Fin (min 8 (391 - 8*b.val))) → Packet (8*b.val+j.val)']
    lines.extend(f'  | {block}, j => DommaschkHarmonicBlock{block:02}.packet j' for block in range(BLOCKS))
    lines.append('  | ⟨n + 49, h⟩, _ => False.elim (by omega)')
    lines += ['', '/-- The packet indexed by actual absolute time-slab number. -/',
              'noncomputable def packet (i : Fin 391) : Packet i.val :=',
              '  let b : Fin 49 := ⟨i.val / 8, by omega⟩',
              '  let j : Fin (min 8 (391 - 8*b.val)) := ⟨i.val % 8, by dsimp [b]; omega⟩',
              '  have e : 8*b.val + j.val = i.val := by dsimp [b,j]; omega',
              '  e ▸ block b j', '',
              '/-- Every point on each closed slab satisfies the original degree-seven',
              'model, for each of three harmonics and either signed traversal. -/',
              'theorem physical (i : Fin 391) (back : Bool) (k : Fin 3) (sine : Bool) {t : ℝ}',
              '    (ht : t ∈ Set.Icc ((i.val : ℝ) / 64) (((i.val : ℝ) + 1) / 64)) :',
              '    ((packet i back k).model sine).Mem (128*t-(2*i.val+1 : ℝ))',
              '      (wave sine (2*((k.val : ℝ)+1)*(if back then -t else t))) :=',
              '  PlasmaLean.Certificates.TrajectoryHarmonicPacket.physical (packet i) back k sine ht',
              '', '/-- A common closed-slab index works for both launch sections, either trace',
              'direction and every stored harmonic through the entire long-trace cap. -/',
              'theorem all_times {t : ℝ} (ht : t ∈ Set.Icc 0 (391 / 64 : ℝ)) :',
              '    ∃ i : Fin 391, t ∈ Set.Icc ((i.val : ℝ) / 64) (((i.val : ℝ) + 1) / 64) ∧',
              '      ∀ (opposite back : Bool) (k : Fin 3) (sine : Bool),',
              '        ((packet i back k).model sine).Mem (128*t-(2*i.val+1 : ℝ))',
              '          ((if opposite then (-1 : ℝ)^(k.val+1) else 1) *',
              '            wave sine (2*((k.val : ℝ)+1)*((if opposite then Real.pi/2 else 0)',
              '              + (if back then -t else t)))) := by',
              '  obtain ⟨i, hit⟩ := time_covered ht',
              '  exact ⟨i, hit, fun q back k sine => physical_section (packet i) q back k sine hit⟩',
              '', f'end PlasmaLean.Design.{name}', '']
    return name, '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--index', type=int, default=1, help='emit a named view of a single slab')
    mode.add_argument('--block', type=int, help='one block of up to eight contiguous time slabs')
    mode.add_argument('--all', action='store_true', help='all 391 slabs and their aggregate theorem')
    mode.add_argument('--aggregate', action='store_true', help='only the finite-index selector')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'PlasmaLean'/'Design')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.all:
        from itertools import chain
        modules = chain((emit_block(b) for b in range(BLOCKS)), [emit_index()])
    elif args.aggregate:
        modules = [emit_index()]
    elif args.block is not None:
        modules = [emit_block(args.block)]
    else:
        modules = [emit(args.index)]
    for module, text in modules:
        out = args.output_dir/f'{module}.lean'
        if args.check:
            if text != out.read_text():
                raise SystemExit(f'{out} differs from regenerated models')
        else:
            out.write_text(text)


if __name__ == '__main__':
    main()
