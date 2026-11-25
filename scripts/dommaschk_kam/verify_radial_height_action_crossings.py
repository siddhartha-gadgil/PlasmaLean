"""Compose the exact N-186 path and N-188 face certificates on one pair of physical tori."""
import argparse
import json
from pathlib import Path
import re
import time

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def theorem_source(band, faces, path=None):
    name = 'DommaschkRadialHeightActionRectangle'
    physical_import, physical_proof, argument = '', '', ''
    conclusion = f'({band}.Through → Realizes uC zC uA zA)'
    claims = ['from_entries', 'from_nested_tori']
    if path is not None:
        name = 'DommaschkProvedRadialHeightActionRectangle'
        physical_import = f"public import {path['package']}.{path['module']}\n"
        physical_proof = f"""theorem through : {band}.Through := by
  intro k x hx
  obtain ⟨y, start, ode, rows⟩ := {path['module']}.from_seed k x hx
  exact ⟨y, start, ode, by fin_cases k <;> exact rows⟩

"""
        conclusion = 'Realizes uC zC uA zA'
        argument = ' through'
        claims.append('through')
    src = f'''module
public import PlasmaLean.Design.DommaschkSectorHeightCrossings
public import RadialRibbonHeightBandFamilyCache.{band}
public import RadialSectorFacesCache.{faces}
{physical_import}
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set
open Certificates.PositionFrameSlabs (Plane coordinates)
open DommaschkKamC KamNewton Theory.KAM WEll1Z2 Contract Forms Fields.VacuumBoozer
open DommaschkSectorHeightAction DommaschkSectorHeightCrossings
open DommaschkSectorAction DommaschkRadialSectionAction DommaschkNativeWellAction
open DommaschkMirrorLaunch DommaschkRadialMirrorHeightBand DommaschkRadialFamilyContinuity
open DommaschkSectorActionBand (BandFaces)
set_option linter.all false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A single three-parameter physical family exists over the full original launch sector.
Every pair of continuous height and action prescriptions in the smaller rectangle has a crossing. -/
def Realizes (uC zC uA zA : FA) : Prop :=
  Nonempty (Family uC zC uA zA) ∧
    ∀ H J : Phase → ℝ, Continuous H → Continuous J → (∀ φ, |H φ-level| ≤ delta) →
      (∀ φ, J φ ∈ Icc lowTarget highTarget) → Crossing uC zC uA zA H J

theorem from_entries {{uC zC uA zA : FA}}
    (ec : EmbeddedTorus (RofC uC) (Zof zC)) (ea : EmbeddedTorus (RofC uA) (Zof zA))
    (entries : ∀ φ : Phase, Entries uC zC uA zA φ)
    (faces : ∀ φ : Phase, BandFaces uC zC uA zA φ)
    (through : {band}.Through) : Realizes uC zC uA zA := by
  have solutions (p : Parameter) : ∃ y : ℝ → Plane,
      y p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧
      Enclosed y (-cap) cap ∧ Verified y := by
    obtain ⟨k,_,entry⟩ := entries p.1 p.2
    exact {band}.from_entry (abs_le.mpr p.1.2) entry through
  choose Y born enc obs using solutions
  obtain ⟨family⟩ := family_of_paths ec ea Y born enc obs
  exact ⟨⟨family⟩,crossing family faces⟩

{physical_proof}theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      {conclusion} := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,inputs⟩ := {faces}.from_nested_tori
  have items (φ : Phase) := inputs φ (abs_le.mpr φ.2)
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,
    from_entries ec ea (fun φ => (items φ).1) (fun φ => (items φ).2.2){argument}⟩
end PlasmaLean.Design.{name}
'''
    return name, src, claims


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--band',required=True,type=Path)
    p.add_argument('--faces',required=True,type=Path)
    p.add_argument('--through', type=Path, help='complete four-tile physical ODE receipt')
    p.add_argument('--wait', action='store_true', help='wait for the complete ODE receipt')
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-height-action-rectangle')
    a=p.parse_args()
    band,faces=[json.loads(x.read_text()) for x in (a.band,a.faces)]
    if (band['module']!='DommaschkRadialRibbonMirrorBand' or
            not re.fullmatch(r'DommaschkSectorActionBandOn\d+(?:_\d+){7}',faces['module'])):
        p.error('expected the authenticated N186 height-band family and N188 physical action faces')
    records=[band,faces]
    if a.wait and a.through is None:
        p.error('--wait requires --through')
    path = None
    if a.through:
        while a.wait and not a.through.is_file():
            time.sleep(15)
        path = json.loads(a.through.read_text())
        if (path['module'] != 'DommaschkRadialRibbonThrough' or path['outer_rows'] != 332
                or path['package'] != 'RadialRibbonThroughFamilyCache'
                or path['packet_sha256'] != band['ribbon']):
            p.error('requires all 332 original rows in both directions on all four tiles')
        records.append(path)
    parents=[s['key'] for s in records]
    for s in records:
        admitted(Path(s['import_paths'][0]),s['module'],s['key'])
    roots=[Path(r) for s in records for r in s['import_paths']]
    links=merge_import_roots(a.cache,roots,parents)
    env(a)
    item=theorem_source(band['module'],faces['module'],path)
    root,rec=compile_modules(a.cache/item[0],[item],[links],
                           [a.version,parents,digest(DESIGN/'DommaschkSectorHeightCrossings.trace')],a,
                           'RadialHeightActionRectangleCache')
    result={k:rec[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')}
    result.update(parents=parents,height_half_width='1/10000000',action_offsets=['-11/10000','9/10000'],
                  import_paths=[str(root),str(links)])
    if path is not None:
        result['through_key'] = path['key']
    save(a.output,result)
    print(item[0],rec['key'],flush=True)


if __name__=='__main__':
    main()
