"""Apply the positive core to the original physical clock and bind its opposite-section seed."""
import argparse
import json
from math import isqrt
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_opposite_action_subwell import CUT, NAME, PACKAGE, load
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',required=True,type=Path)
    p.add_argument('--core',required=True,type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-inner-obstruction')
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    env(a)
    packet=load(a.packet)
    pack=json.loads(a.core.read_text())
    if (pack['packet_sha256'],pack['package'],pack['module'],pack['counts'])!=(
            digest(a.packet),PACKAGE,NAME,[CUT,CUT]):
        raise ValueError('physical clock join requires the exact opposite-section core')
    parents=list(map(Path,pack['import_paths']))
    admitted(parents[0],NAME,pack['key'])
    (x,dr),(z,dz)=packet['seed_center_radius']
    radius=isqrt(dr*dr+dz*dz)+1
    if any(trace['steps'][0]['frame_radius_in']-trace['steps'][0]['jump_norm_upper']!=radius
           for trace in packet['traces']):
        raise ValueError('signed row zero must use the original Euclidean seed before its own jump')
    name='DommaschkOppositeInnerSubwell'
    src=f'''module
public import {PACKAGE}.{NAME}
public import PlasmaLean.Design.DommaschkShiftedActionSubwell
public import PlasmaLean.Design.DommaschkOppositeInnerSeed

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature
open DommaschkShiftedActionSubwell DommaschkRadialFamilyContinuity DommaschkNativeWellAction
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkMirrorLaunch DommaschkOppositeInnerSeed
open {NAME} (slabs coreMass)

theorem recorded_seed : seed.point.x = {x} ∧ seed.point.y = {z} ∧ seed.radius = {radius} := by
  exact ⟨rfl,rfl,rfl⟩

/-- On every physical field line covering the recorded panels a first well about the
actual launch phase strictly exceeds the prescribed action by more than 0.0003. -/
theorem original_clock {{y : ℝ → Plane}} {{l r φ : ℝ}} (hp : |φ-Real.pi/2| ≤ 1/2^19)
    (w : LaunchWell (field y) φ level l r) (e : Enclosed y l r)
    (cells : Covers false (arcAt (Real.pi/2) y) (fieldAt (Real.pi/2) y) level (-5) slabs) :
    l ≤ Real.pi/2-5 ∧ Real.pi/2+5 ≤ r ∧
    target + 3/10000 < action (field y) (density y) l r level := by
  obtain ⟨well,cf,cw,nn,eq⟩ := shifted (s := Real.pi/2) e w
  have birth : φ-Real.pi/2 ∈ Icc (-5) 5 := by
    obtain ⟨lb,ub⟩ := abs_le.mp hp
    constructor <;> linarith
  obtain ⟨left,right,_,mass⟩ := {NAME}.excludes birth well cells cw cf nn
  rw [eq] at mass
  exact ⟨by linarith,by linarith,
    lt_of_lt_of_le (by norm_num [target,coreMass]) mass⟩

end PlasmaLean.Design.{name}
'''
    deps=[a.version,pack['key'],pack['packet_sha256'],digest(DESIGN/'DommaschkShiftedActionSubwell.trace'),
          digest(DESIGN/'DommaschkOppositeInnerSeed.trace')]
    claims=[f'PlasmaLean.Design.{name}.original_clock',
            'PlasmaLean.Design.DommaschkOppositeInnerSeed.from_nested_tori']
    root,rec=compile_modules(a.cache/name,[(name,src,[])],parents,deps,a,
                             'OppositeInnerPhysicalClockCache',qualified_claims=claims)
    out={k:rec[k] for k in ('module','key','axioms','theorems','wall_seconds','peak_rss_kib')}
    out.update(packet_sha256=pack['packet_sha256'],core=pack['key'],import_paths=[str(root),*pack['import_paths']])
    save(a.output,out)
    print(name,rec['key'],flush=True)


if __name__=='__main__':
    main()
