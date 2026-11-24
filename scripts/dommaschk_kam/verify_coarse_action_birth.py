"""Attach the two chronological coarse action blocks adjacent to each actual launch section."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_physical_action import PACKAGE
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def source(label,n,prefix,pack,rows):
    mod=pack['module']
    upper=str(pack['upper']).lower()
    m=pack['splits']
    name=f'DommaschkCoarseBirth{label.upper()}N{m}Of{n:03}'
    deps=['PlasmaLean.Design.DommaschkLowerActionPath',f'{SIGNED_PACKAGE}.{prefix}',
          *[f'{PACKAGE}.{rows[s]}' for s in [-1,1]]]
    src='module\n'+''.join(f'public import {v}\n' for v in deps)+f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature DommaschkMirrorLaunch
open DommaschkLowerActionPath DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set {prefix}
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option linter.style.longLine false
abbrev zeroAngle : ℝ := azimuth endpoint.opposite
abbrev height := {rows[1]}.height
abbrev blocks := ({mod}.slabs.drop {pack['counts'][0]-1}).take 2
def Evidence (y : ℝ → Plane) : Prop :=
  (∀ t ∈ Icc (-({n}/64:ℝ)) ({n}/64),
    HasDerivWithinAt y (DommaschkJacobian.euclideanFlow zeroAngle 1 t (y t)) (Icc (-({n}/64)) ({n}/64)) t) ∧
  Covers {upper} (fun t => arcDensity (y t 0) (zeroAngle+t) (y t 1))
    (fun t => strength (zeroAngle+t) (y t)) height (-1/64) blocks

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ Evidence := by
  obtain ⟨s,a,hs,hφ,src,approach,y,hy,_,_,ode,forward,backward⟩ := {prefix}.from_entry e
  refine ⟨s,a,y,hs,hφ,src,approach,hy,ode,?_⟩
  have slice : blocks = [{rows[-1]}.block,{rows[1]}.block] := by with_unfolding_all rfl
  rw [slice]
  refine ⟨?_,?_,trivial⟩
'''
    for sign,branch in [(-1,'backward'),(1,'forward')]:
        r=rows[sign]
        src+=f'''  · have hi : 0 < {branch}Rows.length := by change 0 < {n}; norm_num
    obtain ⟨prev,mem⟩ := DommaschkSignedObservable.slab_at endpoint.start 0 (i := 0) hi
    have link : {branch}Rows[0] = {r}.row := by with_unfolding_all rfl
    rw [link,Nat.cast_zero,zero_div,add_zero] at mem
    have bound := {r}.cells (prev := prev) (y := y) (by
      intro t ht
      rw [zero_div]
      apply {branch} _ mem t
      change t ∈ Icc 0 (0+1/64)
      simpa only [zero_div,zero_add] using ht)
    convert bound using 1 <;> norm_num [zeroAngle,azimuth,endpoint,MirrorEndpoint.opposite,
      {r}.phase,{r}.height,height,{rows[1]}.height]
'''
    src+=f'''
theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ-zeroAngle| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ Evidence := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry (entry endpoint φ h)⟩
end PlasmaLean.Design.{name}
'''
    return name,src,['from_entry','from_nested_tori']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for x in ['packet','cells','signed','output']:
        p.add_argument('--'+x,type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-action-birth')
    a=p.parse_args()
    pack,cells,signed=(json.loads(f.read_text()) for f in [a.packet,a.cells,a.signed])
    env(a)
    label=pack['endpoint']
    n=signed['length_each_direction']
    pm=f'DommaschkSignedPrefix{label.upper()}{n:03}'
    if signed['module']!=pm or n==0 or pack['packet_sha256']!=signed['packet_sha256']:
        p.error('expected the original signed trajectory of the same physical launch')
    if sorted((r['index'],r['direction']) for r in cells)!=[(0,-1),(0,1)]:
        p.error('need both signed launch blocks')
    paths=[Path(signed['proof_root']),Path(signed['import_path'])]
    admitted(paths[0],pm,signed['key'])
    keys=[a.version,signed['key'],pack['key'],digest(DESIGN/'DommaschkLowerActionPath.trace')]
    slots={}
    for row in cells:
        if row['coarse_packet']!=pack['key'] or row['packet_sha256']!=signed['packet_sha256']:
            p.error('physical row refers to another coarse packet or trajectory')
        roots=list(map(Path,row['import_paths']))
        admitted(roots[0],row['module'],row['key'])
        paths.extend(roots)
        keys.append(row['key'])
        slots[row['direction']]=row['module']
    item=source(label,n,pm,pack,slots)
    overlay=merge_import_roots(a.cache,paths,keys)
    base,r=compile_modules(a.cache/item[0],[item],[overlay],keys,a,'CoarseActionBirthCache')
    out={k:r[k] for k in ['module','key','axioms','theorems']}
    out.update(endpoint=label,coarse_packet=pack['key'],signed= signed['key'],signed_length=n,
               splits=pack['splits'],upper=pack['upper'],height=pack['height'],blocks=2,
               independently_checked_panels=2*pack['splits'],chronological_cells=96,
               import_paths=[str(base),str(overlay)])
    save(a.output,out)
    print(out['module'],out['key'],flush=True)


if __name__=='__main__':
    main()
