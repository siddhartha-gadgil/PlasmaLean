"""Use the polynomial interior to bound the action between the true second upper first mirrors."""
import argparse
import json
from pathlib import Path
import time

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_secondary_cover import subst_once
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_second_action_polynomial_floor import PACKAGE as FLOOR
from verify_secondary_action_cover import BAND_MODULE,THEORY,header
from verify_signed_mirror_passage import merge_import_roots


NAME='DommaschkQ0R478PolynomialFirstWell'
PACKAGE='PolynomialFirstWellCache'
TEMPLATE=Path(__file__).parent/'templates/secondary_lower_well.lean.tpl'


def bridge(floor):
    src=TEMPLATE.read_text().replace('DommaschkQ0R478LowerFirstWell',NAME)
    src=subst_once(src,'module\n','module\npublic import '+FLOOR+'.'+floor+'\n')
    src=subst_once(src,'open DommaschkSecondaryActionCore DommaschkSecondaryActionMass',
                   'open '+floor+' DommaschkSecondaryActionMass')
    src=subst_once(src,'Covers false (density y) (field y) height (-322/64) inner',
                   'Tracks fwdRows backRows 325 y')
    src=subst_once(src,'floor_on_enclosing_interval (f := field y) (w := density y)',
                   'floor_on_enclosing_interval (y := y)')
    src=subst_once(src,'    (rectangles : ∀ y, Tracks fwdRows backRows 322 y → Core y) :', '    :')
    src=subst_once(src,'(rectangles y (tracks_of_take fc bc))','(tracks_of_take fc bc)')
    src=src.replace('322','325').replace('the 644 packed blocks on its strictly interior','the certified polynomial lower bound on its strictly interior')
    return NAME,src,['on_path','from_passage']


def birth(n,pm):
    name=f'{NAME}Birth{n:03}'
    src=header(name,[PACKAGE+'.'+NAME,SIGNED_PACKAGE+'.'+pm])
    src+=f'''
open {pm} {NAME} Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton
theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ
      (fun y => Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧ Conclusion y) := by
  apply from_passage (by norm_num) (extraF := forwardRows.drop 327) (extraB := backwardRows.drop 327)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) ({pm}.from_entry e)

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ-azimuth endpoint.opposite| ≤ endpoint.width →
        AtBirth endpoint uC zC uA zA φ
          (fun y => Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧ Conclusion y) := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ small => from_entry (entry endpoint φ small)⟩
end PlasmaLean.Design.{name}
'''
    return name,src,['from_entry','from_nested_tori']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for k in ['floor','band','output']:
        p.add_argument('--'+k,type=Path,required=True)
    p.add_argument('--signed',type=Path)
    p.add_argument('--wait',action='store_true')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/second-polynomial-first-well')
    a=p.parse_args()
    while a.wait and not a.floor.exists():
        time.sleep(30)
    env(a)
    floor,band=[json.loads(path.read_text()) for path in [a.floor,a.band]]
    timing=band['timing']
    if (floor['module'],band['module'],timing['module'],floor['packet_sha256'])!=(
            'DommaschkQ0R478PolynomialFloor325',BAND_MODULE,'DommaschkQ0R478MirrorTimeSeparation',band['packet_sha256']):
        p.error('expected the complete polynomial core and the true signed mirror timing on the same witness')
    keys=[a.version,digest(DESIGN/(THEORY+'.trace'))]
    paths=[]
    for rec in [floor,band,timing]:
        roots=list(map(Path,rec['import_paths']))
        admitted(roots[0],rec['module'],rec['key'])
        keys.append(rec['key'])
        paths.extend(roots)
    joined=merge_import_roots(a.cache,paths,keys)
    base,r=compile_modules(a.cache/NAME,[bridge(floor['module'])],[joined],keys,a,PACKAGE)
    out={k:r[k] for k in ['module','key','theorems','axioms','peak_rss_kib','wall_seconds']}
    out.update(complete=False,floor=floor['key'],timing=timing['key'],packet_sha256=band['packet_sha256'],
               mass=floor['mass'],import_paths=list(map(str,[base,joined])))
    save(a.output,out)
    if a.signed:
        while a.wait and not a.signed.exists():
            time.sleep(30)
        pf=json.loads(a.signed.read_text())
        n=pf['length_each_direction']
        pm=f'DommaschkSignedPrefixQ0R478{n:03}'
        if n<=327 or pf['module']!=pm or pf['packet_sha256']!=band['packet_sha256']:
            p.error('need a signed trajectory extending past the original upper first-mirror brackets')
        pfpaths=list(map(Path,[pf['proof_root'],pf['import_path']]))
        admitted(pfpaths[0],pm,pf['key'])
        deps=[*keys,r['key'],pf['key']]
        overlay=merge_import_roots(a.cache/'birth',[base,joined,*pfpaths],deps)
        item=birth(n,pm)
        leaf,br=compile_modules(a.cache/item[0],[item],[overlay],deps,a,'PolynomialFirstBirthCache')
        out['birth']={k:br[k] for k in ['module','key','theorems','axioms','wall_seconds','peak_rss_kib']}
        out['birth']['import_paths']=list(map(str,[leaf,overlay]))
        out.update(complete=True,signed=pf['key'],length_each_direction=n)
        save(a.output,out)
    print(out['module'],out['key'],out['complete'],flush=True)


if __name__=='__main__':
    main()
