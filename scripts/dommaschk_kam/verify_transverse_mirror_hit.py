"""Join a signed physical mirror hit to a quantitative field-strength slope at that hit."""

import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import ROOT, save


def source(index, direction):
    backwards = direction == -1
    field = f'DommaschkPhysical{"Backward" if backwards else "Forward"}{index}'
    hits = f'DommaschkPhysicalMirrorHit{"Backward" if backwards else ""}{index}'
    tube = f'DommaschkMirrorSlope{index}Tube'
    name = f'DommaschkTransverseMirrorHit{"Backward" if backwards else "Forward"}{index}'
    tag, angle_t, angle_a = ('back', '(-t)', '(-a)') if backwards else ('fwd', 't', 'a')
    sign = '(-1)' if backwards else '1'
    rate = '1/400' if index == 324 else '1/128'
    upper = str(index == 324).lower()
    return name, f'''module
public import PhysicalMirrorCache.{hits}
public import MirrorSlopeTubeCache.{tube}
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # A true transverse mirror crossing from every admissible local entry -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing {field} Set
set_option linter.style.longLine false
set_option maxRecDepth 16000

/-- The squared field strength increases strictly, including the bracket endpoints. -/
theorem squared_strictMonoOn {{y : ℝ → Plane}}
    (field : ∀ t ∈ Icc ({index}/64) ({index+1}/64),
      HasDerivWithinAt y (DommaschkJacobian.euclideanFlow 0 {sign} t (y t))
        (Icc ({index}/64) ({index+1}/64)) t ∧ y t ∈ (physicalSlab previous row ({index}/64)).tube t) :
    StrictMonoOn (fun a => (strength {angle_a} (y a)) ^ 2) (Icc ({index}/64) ({index+1}/64)) := by
  have rpos : ∀ t ∈ Icc ({index}/64) ({index+1}/64), 0 < y t 0 := by
    intro t ht
    apply DommaschkMirrorBracketSlab.positive_radius (show t ∈ Icc ({index}/64) (({index}/64)+1/64)
      by convert ht using 2; norm_num) (field t ht).2 <;> kernel_fact
  have c := continuousOn_strength (fun a ha => (field a ha).1.continuousWithinAt) {sign} rpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by simpa only [Function.comp_def,one_mul,neg_one_mul] using (continuous_pow 2).comp_continuousOn c)
  intro t ht
  rw [interior_Icc] at ht
  have in_closed := Ioo_subset_Icc_self ht
  have flow := (field t in_closed).1
  have d := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t flow
  have tube := (field t in_closed).2
  have row_eq : row = {tube}.row_{tag} := by rfl
  rw [row_eq] at tube
  obtain ⟨v,lower,diff⟩ := {tube}.{tag}_transverse (prev := previous) (y := fun a => coordinates (y a)) ht
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using tube)
    (d.congr_deriv (coordinates.apply_symm_apply _))
  have exact_deriv : HasDerivAt (fun a => (strength {angle_a} (y a))^2) v t := diff
  rw [exact_deriv.deriv]
  exact lt_trans (by norm_num) lower

/-- The certified field line crosses the given mirror level with a positive outward slope. -/
theorem transverse_from_entry {{x : Plane}} (hx : x ∈ stateSet previous) :
    ∃ y : ℝ → Plane, y ({index}/64) = x ∧ y ({index+1}/64) ∈ stateSet (next row) ∧
      (∀ t ∈ Icc ({index}/64) ({index+1}/64),
        HasDerivWithinAt y (DommaschkJacobian.euclideanFlow 0 {sign} t (y t))
          (Icc ({index}/64) ({index+1}/64)) t ∧ y t ∈ (physicalSlab previous row ({index}/64)).tube t) ∧
      ∃ t ∈ Ioo ({index}/64) ({index+1}/64),
        strength {angle_t} (y t) = DommaschkFirstMirrorLaunchSign.height {upper} ∧
        (∀ u ∈ Icc ({index}/64) ({index+1}/64),
          strength {'(-u)' if backwards else 'u'} (y u) = DommaschkFirstMirrorLaunchSign.height {upper} → u = t) ∧
        ∃ v > ({rate}:ℝ)/(2*DommaschkFirstMirrorLaunchSign.height {upper}),
          HasDerivAt (fun a => strength {angle_a} (y a)) v t := by
  obtain ⟨y,entry,exit,field,t,ht,hit⟩ := {hits}.hit_from_entry hx
  have at_hit := field t (Ioo_subset_Icc_self ht)
  refine ⟨y,entry,exit,field,t,ht,hit,?_,?_⟩
  · intro u hu he
    apply (squared_strictMonoOn field).injOn hu (Ioo_subset_Icc_self ht)
    exact congrArg (· ^ 2) (he.trans hit.symm)
  · exact {tube}.{tag}_level_transverse ht at_hit.2 at_hit.1
      (by norm_num [DommaschkFirstMirrorLaunchSign.height]) hit

end PlasmaLean.Design.{name}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hit', required=True, type=Path)
    parser.add_argument('--slopes', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    hit = json.loads(args.hit.read_text())
    slopes = json.loads(args.slopes.read_text())
    index, direction = hit['index'], hit['direction']
    if index not in (316, 324) or slopes['index'] != index or direction not in (-1, 1):
        raise ValueError('expected a signed hit and slope on the same certified bracket')
    if slopes['part'] != 'tube' or slopes['module'] != f'DommaschkMirrorSlope{index}Tube':
        raise ValueError('expected the complete signed slope package')
    if hit['module'] != f'DommaschkPhysicalMirrorHit{"Backward" if direction == -1 else ""}{index}':
        raise ValueError('unexpected signed hit module')
    links = []
    for record in (hit, slopes):
        roots = [Path(p) for p in record['import_paths']]
        admitted(roots[0], record['module'], record['key'])
        links.extend(roots)
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean', '--version')
    args.lean = str(Path(lake('lean', '--print-prefix')) / 'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    name, lean = source(index, direction)
    root, record = compile_modules(ROOT / '.lake/mirror-slopes' / name,
        [(name, lean, ['squared_strictMonoOn', 'transverse_from_entry'])], links,
        [version, hit['key'], slopes['key']], args, 'TransverseMirrorCache')
    result = {k: record[k] for k in ('module', 'key', 'theorems', 'axioms')}
    result.update(index=index, direction=direction, import_paths=[str(root), *map(str, links)])
    if args.output:
        save(args.output, result)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
