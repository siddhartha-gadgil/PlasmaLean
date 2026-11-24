"""Prove quantitative transverse mirror regularity along one signed physical field line."""

import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def source(i):
    tube = f'DommaschkMirrorSlope{i}Tube'
    name = f'DommaschkSignedSlope{i}'
    upper = str(i == 324).lower()
    rate = '1/400' if i == 324 else '1/128'
    block, offset = divmod(i, 16)
    interval = f'Icc ({i}/64) ({i+1}/64)'
    src = f'''module
public import PlasmaLean.Design.DommaschkSignedMirrorSlope
public import PlasmaLean.Design.DommaschkMirrorBracketSlab
public import MirrorSlopeTubeCache.{tube}

/-! # Transversality on either side of the same enclosed QA2R field line -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkSignedMirrorSlope
open DommaschkMirrorTubeCrossing Set
set_option linter.style.longLine false
set_option maxRecDepth 16000

theorem regular {{n : ℕ}} {{fs bs : State}} {{fr br : List Step}} {{x : Plane}}
    {{y : ℝ → Plane}} (path : Path n fs bs fr br x y) (reached : {i} < n)
    (hf : {i} < fr.length) (hb : {i} < br.length)
    (rf : fr[{i}] = DommaschkPositionFramesFwd.block{block}[{offset}])
    (rb : br[{i}] = DommaschkPositionFramesBack.block{block}[{offset}]) :
    RegularBoth ({i}/64) ({i+1}/64) (DommaschkFirstMirrorLaunchSign.height {upper}) ({rate}) y := by
  have stop : ({i} : ℝ) + 1 = {i+1} := by norm_num
  have size : {i+1} ≤ (n : ℝ) := by exact_mod_cast reached
  have odes := clock_odes path (show (0:ℝ) ≤ {i}/64 by norm_num)
    (show ({i+1}:ℝ)/64 ≤ (n:ℝ)/64 by linarith)
  constructor
'''
    for back, rows, val, eq, limit, tag, rate_sign, side in (
            ('false', 'fr', 'y t', 'rf', 'hf', 'fwd', '1', '1'),
            ('true', 'br', 'y (-t)', 'rb', 'hb', 'back', '(-1)', '2')):
        fn = 'y' if back == 'false' else '(fun u => y (-u))'
        src += f'''  · obtain ⟨cont,prev,inside⟩ := path.at_row reached {back} {limit}
    change ContinuousOn {fn} (Icc ({i}/64) ((({i}:ℝ)+1)/64)) at cont
    change ∀ t ∈ Icc ({i}/64) ((({i}:ℝ)+1)/64),
      {val} ∈ (physicalSlab prev {rows}[{i}] ({i}/64)).tube t at inside
    rw [stop] at cont inside
    rw [{eq}] at inside
    have rpos (t : ℝ) (ht : t ∈ {interval}) : 0 < ({val}) 0 := by
      apply DommaschkMirrorBracketSlab.positive_radius (hx := inside t ht)
      · rwa [show ({i}/64:ℝ) + 1/64 = {i+1}/64 by norm_num]
      · kernel_fact
      · kernel_fact
    apply regular_of_square
    · simpa only [one_mul,neg_one_mul] using continuousOn_strength cont {rate_sign} rpos
    · intro t
      exact norm_nonneg _
    · norm_num [DommaschkFirstMirrorLaunchSign.height]
    · norm_num
    · intro t ht
      have hc := Ioo_subset_Icc_self ht
      have ode := odes.{side} t hc
      have d := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t ode
      apply {tube}.{tag}_transverse (prev := prev) (y := fun t => coordinates ({val})) ht
      · simpa only [ContinuousLinearEquiv.symm_apply_apply] using inside t hc
      · apply d.congr_deriv
        exact coordinates.apply_symm_apply _
'''
    return name, src + f'end PlasmaLean.Design.{name}\n'


def monotone_source(i):
    name, tube = f'DommaschkSignedMonotone{i}', f'DommaschkMirrorSlope{i}Tube'
    interval = f'Icc ({i}/64) ({i+1}/64)'
    src = f'''module
public import PlasmaLean.Design.DommaschkSignedMirrorSlope
public import PlasmaLean.Design.DommaschkMirrorBracketSlab
public import MirrorSlopeTubeCache.{tube}

/-! # Strict outward strength growth on either true signed bracket -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkSignedMirrorSlope
open DommaschkMirrorTubeCrossing Set
set_option linter.style.longLine false
set_option maxRecDepth 16000
'''
    for tag, sign, angle in [('fwd', '1', 'a'), ('back', '(-1)', '(-a)')]:
        row = f'{tube}.row_{tag}'
        src += f'''
theorem {tag}_outward_mono {{prev : State}} {{y : ℝ → Plane}}
    (ode : ∀ t ∈ {interval}, HasDerivWithinAt y
      (DommaschkJacobian.euclideanFlow 0 {sign} t (y t)) ({interval}) t)
    (tube : ∀ t ∈ {interval}, y t ∈ (physicalSlab prev {row} ({i}/64)).tube t) :
    StrictMonoOn (fun a => (strength {angle} (y a)) ^ 2) ({interval}) := by
  have rpos (t : ℝ) (ht : t ∈ {interval}) : 0 < y t 0 := by
    apply DommaschkMirrorBracketSlab.positive_radius (hx := tube t ht)
    · rwa [show ({i}/64:ℝ)+1/64 = {i+1}/64 by norm_num]
    · kernel_fact
    · kernel_fact
  have c := continuousOn_strength (fun a ha => (ode a ha).continuousWithinAt) {sign} rpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by simpa only [Function.comp_def,one_mul,neg_one_mul] using (continuous_pow 2).comp_continuousOn c)
  intro t ht
  rw [interior_Icc] at ht
  have hc := Ioo_subset_Icc_self ht
  have d := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (ode t hc)
  obtain ⟨v,hv,der⟩ := {tube}.{tag}_transverse (prev := prev) (y := fun a => coordinates (y a)) ht
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using tube t hc)
    (d.congr_deriv (coordinates.apply_symm_apply _))
  have slope : HasDerivAt (fun a => (strength {angle} (y a)) ^ 2) v t := der
  rw [slope.deriv]
  exact lt_trans (by norm_num) hv
'''
    src += f'''
theorem both {{n : ℕ}} {{fs bs : State}} {{fr br : List Step}} {{x : Plane}} {{y : ℝ → Plane}}
    (path : Path n fs bs fr br x y) (reached : {i} < n)
    (hf : {i} < fr.length) (hb : {i} < br.length)
    (rf : fr[{i}] = {tube}.row_fwd) (rb : br[{i}] = {tube}.row_back) :
    StrictMonoOn (fun a => (strength a (y a)) ^ 2) ({interval}) ∧
    StrictMonoOn (fun a => (strength (-a) (y (-a))) ^ 2) ({interval}) := by
  have stop : ({i} : ℝ) + 1 = {i+1} := by norm_num
  have size : {i+1} ≤ (n:ℝ) := by exact_mod_cast reached
  have clocks := clock_odes path (show (0:ℝ) ≤ {i}/64 by norm_num)
    (show ({i+1}:ℝ)/64 ≤ (n:ℝ)/64 by linarith)
  constructor
'''
    for tag, back, rows, eq, limit, side, y in [('fwd','false','fr','rf','hf','1','y t'),
                                                 ('back','true','br','rb','hb','2','y (-t)')]:
        src += f'''  · obtain ⟨_,prev,tube⟩ := path.at_row reached {back} {limit}
    change ∀ t ∈ Icc ({i}/64) ((({i}:ℝ)+1)/64), {y} ∈ (physicalSlab prev {rows}[{i}] ({i}/64)).tube t at tube
    rw [stop,{eq}] at tube
    exact {tag}_outward_mono clocks.{side} tube
'''
    return name, src + f'end PlasmaLean.Design.{name}\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--slopes', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--monotone', action='store_true', help='export strict growth on both closed elapsed-time brackets')
    args = parser.parse_args()
    slopes = json.loads(args.slopes.read_text())
    i = slopes['index']
    if i not in (316, 324) or slopes['part'] != 'tube' or slopes['module'] != f'DommaschkMirrorSlope{i}Tube':
        raise ValueError('expected the two-sided tube slope certificate for a mirror bracket')
    paths = list(map(Path, slopes['import_paths']))
    admitted(paths[0], slopes['module'], slopes['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean', '--version')
    args.lean = str(Path(lake('lean', '--print-prefix')) / 'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    name, src = monotone_source(i) if args.monotone else source(i)
    labels = ['fwd_outward_mono', 'back_outward_mono', 'both'] if args.monotone else ['regular']
    deps = [digest(DESIGN / (s+'.trace')) for s in ('DommaschkSignedMirrorSlope', 'DommaschkMirrorBracketSlab')]
    root, rec = compile_modules(ROOT / '.lake/signed-mirrors' / name,
        [(name, src, labels)], paths, [version, slopes['key'], deps], args, 'SignedSlopeCache')
    report = {k: rec[k] for k in ('module', 'key', 'theorems', 'axioms')}
    report.update(index=i, rate_lower=slopes['rate_lower'], import_paths=[str(root), *map(str, paths)])
    if args.output:
        save(args.output, report)
    print(json.dumps(report))


if __name__ == '__main__':
    main()
