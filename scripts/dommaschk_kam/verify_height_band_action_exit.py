"""Ground the varying-height first radial exit from the two complete original endpoint paths."""
import argparse
import json
from pathlib import Path
import re

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


THEORY='DommaschkHeightBandActionExit'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--outer',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/height-band-action-exit')
    args=parser.parse_args()
    outer=json.loads(args.outer.read_text())
    old=outer['module']
    match=re.fullmatch(r'DommaschkOuterFaceFlightOn(\d+(?:_\d+){7})',old)
    if not match or outer['time_upper']!=452 or outer['near_upper_width']!='1/100000':
        parser.error('expected the original 452-bounded variable-height outer physical face')
    roots=list(map(Path,outer['import_paths']))
    parent=admitted(roots[0],old,outer['key'])
    claims=['from_entries','from_nested_tori']
    if not all(f'PlasmaLean.Design.{old}.{t}' in parent['theorems'] for t in claims):
        parser.error('outer proof does not carry the original nested birth entries')
    original=(roots[0]/'OuterFaceFlightCache'/(old+'.lean')).read_text()
    marker='  exact DommaschkOuterFaceFlight.of_outer_witness small bornO pz pf pb outerWell outerFloor'
    if original.count(marker)!=1 or original.count('  obtain ⟨pb⟩ := back_branch b.prefix room')!=1:
        parser.error('could not identify the two independent signed endpoint reconstructions')
    name=THEORY+'On'+match[1]
    src=original.split(marker)[0].replace(old,name)
    src=src.replace('public import PlasmaLean.Design.DommaschkOuterFaceFlight',
                    f'public import OuterFaceFlightCache.{old}\npublic import PlasmaLean.Design.{THEORY}')
    src=src.replace('open DommaschkOuterFaceFlight','open DommaschkHeightBandActionExit')
    target='DommaschkOuterFaceFlight.Result uC zC uA zA φ := by'
    if src.count(target)!=1:
        parser.error('unexpected upper-height face result signature')
    src=src.replace(target,'∀ h ∈ heights, Bounds uC zC uA zA φ h := by')
    src+=f'''  intro h hh
  exact of_endpoints small bornI bornO py pz obs.2.2.1 pf pb ({old}.from_entries small entryI entryO) hh

theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    (∀ φ, |φ| ≤ 1/2^19 → ∀ h ∈ heights, Bounds uC zC uA zA φ h) ∧ Guard uC zC uA zA := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,entries,_⟩ := DommaschkRadialRibbonEntry.from_nested_tori
  have faces : ∀ φ, |φ| ≤ 1/2^19 → ∀ h ∈ heights, Bounds uC zC uA zA φ h := by
    intro φ small
    exact from_entries small (entries .q0r470 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small))
      (entries .q0r478 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small))
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,faces,guard faces⟩

end PlasmaLean.Design.{name}
'''
    env(args)
    deps=[args.version,outer['key'],outer['faces'],digest(DESIGN/(THEORY+'.trace'))]
    item=name,src,claims
    audit=[f'PlasmaLean.Design.{name}.{t}' for t in claims]+[f'PlasmaLean.Design.{THEORY}.stays_inside_of_correction']
    root,r=compile_modules(args.cache/name,[item],roots,deps,args,'HeightBandActionExitCache',qualified_claims=audit)
    out={k:v for k,v in r.items() if k!='artifacts'}
    out.update(outer=outer['key'],height_drop='1/500000',budget='249/250000',
               import_paths=list(map(str,[root,*roots])))
    save(args.output,out)
    print(name,r['key'],flush=True)


if __name__=='__main__':
    main()
