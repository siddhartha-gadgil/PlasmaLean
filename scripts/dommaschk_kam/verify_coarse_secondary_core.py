"""Prove the exact interior mass needed from the lower-resolution Q0R478 action cover."""
import argparse
from fractions import Fraction
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_secondary_lower import packet_inputs
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save


PACKAGE='CoarseSecondaryCoreCache'
NAME='DommaschkCoarseSecondaryCore325'


def declaration(pack,blocks,count,mass):
    center=pack['counts'][0]
    total=sum(m for _,m in blocks[center-count:center+count])
    previous=sum(m for _,m in blocks[center-count+1:center+count-1])
    table=pack['module']
    src=f'''module
public import {pack['package']}.{table}
public import PlasmaLean.Design.DommaschkSecondaryActionCore

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{NAME}
open Certificates.MirrorActionQuadrature DommaschkSecondaryActionMass Set
open Kinetic.MirrorHeightAction
set_option maxRecDepth 32768
set_option linter.style.longLine false

abbrev inner := ({table}.slabs.drop {center-count}).take {2*count}
abbrev innerMass : ℝ := {mass.numerator}/{mass.denominator}
theorem inner_length : inner.length = {count}+{count} := by with_unfolding_all rfl
theorem inner_total : total inner = {total} := by kernel_fact
theorem previous_total : total (({table}.slabs.drop {center-count+1}).take {2*(count-1)}) = {previous} := by kernel_fact
theorem crosses_target : {previous} / (3072*1099511627776 : ℝ) < target ∧ target < innerMass := by
  norm_num [target,innerMass]

theorem floor_on_enclosing_interval {{f w : ℝ → ℝ}} {{l r : ℝ}}
    (left : l ≤ -{count}/64) (right : {count}/64 ≤ r)
    (cells : Covers false w f height (-{count}/64) inner)
    (hn : ∀ t ∈ Icc l r, 0 ≤ w t) (cf : ContinuousOn f (Icc l r)) (cw : ContinuousOn w (Icc l r)) :
    target < innerMass ∧ innerMass ≤ action f w l r height := by
  have sub : Icc (-{count}/64:ℝ) ({count}/64) ⊆ Icc l r := Icc_subset_Icc left right
  have b := Certificates.NativeActionInterval.exact_lower_mass inner_length cells
    (fun t ht => hn t (sub ht)) (cf.mono sub) (cw.mono sub)
  rw [inner_total] at b
  have lower : innerMass ≤ action f w (-{count}/64) ({count}/64) height := by
    norm_num [innerMass] at b ⊢
    exact b
  exact ⟨crosses_target.2,lower.trans (Kinetic.MirrorActionEnvelope.action_mono_interval
    left (by norm_num) right cf cw hn)⟩
end PlasmaLean.Design.{NAME}
'''
    return NAME,src,['floor_on_enclosing_interval']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-secondary-core')
    a=p.parse_args()
    pack,root,_,blocks,n,mass=packet_inputs(a.packet)
    if n!=325:
        p.error('the supplied packet does not first cross the target at 325 signed pairs')
    env(a)
    decl=declaration(pack,blocks,n,mass)
    deps=[pack['key'],a.version,digest(DESIGN/'DommaschkSecondaryActionCore.trace')]
    base,r=compile_modules(a.cache/NAME,[decl],[root],deps,a,PACKAGE)
    out={k:r[k] for k in ['module','key','theorems','axioms']}
    out.update(pairs=n,blocks=2*n,height=pack['height'],mass=str(mass),target=pack['target'],
               margin=str(mass-Fraction(pack['target'])),coarse_packet=pack['key'],
               import_paths=list(map(str,[base,root])))
    save(a.output,out)
    print(NAME,r['key'],flush=True)


if __name__=='__main__':
    main()
