"""Emit the all-angle B_phi lower bound over the entire signed pilot spatial envelope."""

import argparse
from fractions import Fraction
from math import ceil, comb, floor
from pathlib import Path

from verify_native_action_models import R0, ROOT, WAVES, static_data


SCALE = 2**52
LIMIT = Fraction(7, 8)
U = (-SCALE // 32, 3 * SCALE // 32)
Z = (-5 * SCALE // 64, 5 * SCALE // 64)
TARGET = ROOT / 'PlasmaLean/Design/DommaschkToroidalEnvelope.lean'


def coefficients():
    channels = [(wave, [[q for q, _ in row] for row in group])
                for wave, group in static_data()[0]]
    constant = next(rows for wave, rows in channels if wave == 0)[-1]
    for i in range(8):
        constant[-1-i] -= LIMIT * comb(7, i) * R0**(7-i)
    return channels


def mul(x, y):
    products = [a*b for a in x for b in y]
    return min(products) // SCALE, -((-max(products)) // SCALE)


def horner(coeffs, var):
    acc = (0, 0)
    for c in coeffs:
        lo, hi = mul(acc, var)
        acc = lo+c[0], hi+c[1]
    return acc


def lower(channels, u, z):
    total = 0
    for wave, group in channels:
        rows = [horner([(floor(SCALE*q), ceil(SCALE*q)) for q in row], u) for row in group]
        lo, hi = horner(rows, z)
        total += lo if wave == 0 else -max(abs(lo), abs(hi))
    return total


def halves(box):
    mid = sum(box) // 2
    return (box[0], mid), (mid, box[1])


def lean_rat(q):
    return str(q).replace('/', ' / ')


def generate():
    channels = coefficients()
    declarations = []
    names = []
    for wave, group in channels:
        rows = []
        for i, row in enumerate(group):
            name = f'r{wave}_{i}'
            coefficients_src = ',\n  '.join(lean_rat(q) for q in row)
            declarations.append(f'private def {name} : List ℚ := [\n  {coefficients_src}]')
            rows.append(name)
        name = f'c{wave}'
        declarations.append(f'private def {name} : Rows := [{", ".join(rows)}]')
        names.append(f'(.{WAVES[wave]}, {name})')
    declarations.append('private def channels : Channels := [\n  ' + ',\n  '.join(names) + ']')
    declarations.append('''set_option maxHeartbeats 0 in
-- Kernel expansion identifies every rational coefficient in all seven harmonic channels.
private theorem identity (u z θ : ℝ) :
    value u z θ channels = evR u z (Real.cos θ) (Real.sin θ) (shiftedD (7 / 8)) := by
  rw [← expand_sound]
  exact congrArg (evR u z (Real.cos θ) (Real.sin θ))
    (sameTerms_sound (p := expand channels) (q := shiftedD (7 / 8)) (by kernel_fact))''')
    cells = []

    def visit(u, z, indent):
        lo = lower(channels, u, z)
        if lo > 0:
            number = len(cells)
            cells.append((u, z, lo))
            return [indent + f'apply cell{number} <;> linarith']
        opts = [(min(lower(channels, v, z) for v in halves(u)), 'u'),
                (min(lower(channels, u, v) for v in halves(z)), 'z')]
        var = max(opts)[1]
        left, right = halves(u if var == 'u' else z)
        mid = lean_rat(Fraction(left[1], SCALE))
        first = visit(left, z, indent+'  ') if var == 'u' else visit(u, left, indent+'  ')
        last = visit(right, z, indent+'  ') if var == 'u' else visit(u, right, indent+'  ')
        first[0] = indent + '· ' + first[0][len(indent)+2:]
        last[0] = indent + '· ' + last[0][len(indent)+2:]
        return [indent + f'by_cases h{len(cells)} : {var} ≤ {mid}', *first, *last]

    partition = visit(U, Z, '  ')
    for i, (u, z, lo) in enumerate(cells):
        box = lambda p: f'(⟨{p[0]}, {p[1]}⟩ : Box)'
        vals = [lean_rat(Fraction(k, SCALE)) for k in (*u, *z)]
        declarations.append(f'''set_option maxHeartbeats 0 in
-- The exact fixed-point Horner evaluation checks all spatial coefficients on this cell.
private theorem cell{i} {{u z θ : ℝ}} (ul : {vals[0]} ≤ u)
    (ur : u ≤ {vals[1]}) (zl : {vals[2]} ≤ z) (zr : z ≤ {vals[3]}) :
    0 < value u z θ channels := by
  let U := {box(u)}
  let Z := {box(z)}
  have hU : U.Mem u := by constructor <;> norm_num [U, scale] <;> linarith
  have hZ : Z.Mem z := by constructor <;> norm_num [Z, scale] <;> linarith
  have result : (enclosure U Z channels).lo = {lo} := by kernel_fact
  apply pos_of_mem (b := enclosure U Z channels) (by rw [result]; norm_num)
  exact enclosure_mem hU hZ θ channels''')
    declarations += ['''private theorem positive (u z θ : ℝ) (ul : -1 / 32 ≤ u) (ur : u ≤ 3 / 32)
    (zl : -5 / 64 ≤ z) (zr : z ≤ 5 / 64) : 0 < value u z θ channels := by\n''' +
                     '\n'.join(partition),
                     '''/-- The candidate's real azimuthal component exceeds seven eighths everywhere on
the full pilot spatial envelope, at every geometric toroidal angle. -/
theorem cylBphi_lower {R z : ℝ} (φ : ℝ) (rad : R ∈ Set.Icc (7 / 8) 1)
    (vertical : |z| ≤ 5 / 64) : 7 / 8 < cylBphi R φ z := by
  let u := R - dkR0
  have base : dkR0 + u = R := by dsimp [u]; ring
  have shifted := positive u z (2 * φ) (by norm_num [u, dkR0]; linarith [rad.1])
    (by norm_num [u, dkR0]; linarith [rad.2]) (by linarith [(abs_le.mp vertical).1])
    (abs_le.mp vertical).2
  rw [identity, eval_shiftedD, base] at shifted
  change 0 < atPoint dD R φ z - (((7 / 8 : ℚ) : ℝ)) * R ^ 7 at shifted
  rw [(field_id (by linarith [rad.1] : 0 < R) φ z).1] at shifted
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at shifted
  have hr : 0 < R := by linarith [rad.1]
  apply (mul_lt_mul_iff_right₀ (pow_pos hr 7)).mp
  linarith only [shifted]''']
    header = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkHarmonicBoxes
public import PlasmaLean.Design.DommaschkBounceField
public import PlasmaLean.Certificates.KernelFact

/-! # An all-angle lower bound on the toroidal field throughout the pilot envelope

Generated by scripts/dommaschk_kam/emit_toroidal_envelope.py.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkToroidalEnvelope
open DommaschkHarmonicHorner DommaschkHarmonicBoxes DommaschkCompensatedAction
open DommaschkKam Certificates.NativeActionInterval
open DommaschkBounceField (field_id atPoint)
set_option maxRecDepth 32768
set_option Elab.async false

'''
    return header + '\n\n'.join(declarations) + '\n\nend PlasmaLean.Design.DommaschkToroidalEnvelope\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=TARGET)
    args = parser.parse_args()
    args.output.write_text(generate())
