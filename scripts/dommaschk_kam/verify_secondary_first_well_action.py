"""Bind the second launch's lower core to its physical upper-height first mirrors."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_action_cover import BAND_MODULE, THEORY, header, package
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


NAME='DommaschkQ0R478LowerFirstWell'
PACKAGE='SecondaryFirstWellLowerCache'


def birth(n,prefix,cover):
    name=f'{NAME}Birth{n:03}'
    src=header(name,[f'{PACKAGE}.{NAME}',f'{SIGNED_PACKAGE}.{prefix}',f'{package(5,649)}.{cover}'])
    src+=f'''
open {prefix} {NAME} Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ
      (fun y => Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧ Conclusion y) := by
  have fmatch : forwardRows = {BAND_MODULE}.fwdRows ++ forwardRows.drop 327 := by with_unfolding_all rfl
  have bmatch : backwardRows = {BAND_MODULE}.backRows ++ backwardRows.drop 327 := by with_unfolding_all rfl
  apply from_passage (by norm_num) fmatch bmatch ({prefix}.from_entry e)
  intro y track
  have lower := {cover}.cover track
  rw [{cover}.Covered,show {cover}.start = (-322/64:ℝ) by norm_num [{cover}.start]] at lower
  exact lower

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ
        (fun y => Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧ Conclusion y) := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry (entry endpoint φ h)⟩
'''
    return name,src+f'\nend PlasmaLean.Design.{name}\n',['from_entry','from_nested_tori']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--band',type=Path,required=True)
    p.add_argument('--cover',type=Path)
    p.add_argument('--signed',type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-first-well-action')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if bool(a.cover)!=bool(a.signed):
        p.error('supply both the signed physical prefix and the complete lower core to attach the birth')
    band=json.loads(a.band.read_text())
    packet=digest(load(478)[1])
    if band['module']!=BAND_MODULE or band['packet_sha256']!=packet:
        p.error('expected the second launch’s complete upper mirror branch')
    timing=band['timing']
    if timing['module']!='DommaschkQ0R478MirrorTimeSeparation':
        p.error('expected the certified upper-height timing caps')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    base=[lake('lean','--version'),digest(DESIGN/(THEORY+'.trace')),packet]
    paths=list(map(Path,timing['import_paths']))
    admitted(paths[0],timing['module'],timing['key'])
    src=(Path(__file__).parent/'templates/secondary_lower_well.lean.tpl').read_text()
    keys=[*base,band['key'],timing['key']]
    item=(NAME,src,['forward_regular','backward_regular','on_path','from_passage'])
    root,mark=compile_modules(a.cache/NAME,[item],paths,keys,a,PACKAGE)
    out={k:mark[k] for k in ['module','key','theorems','axioms']}
    out.update(complete=False,packet_sha256=packet,import_paths=list(map(str,[root,*paths])))
    if a.cover:
        cover,prefix=[json.loads(d.read_text()) for d in [a.cover,a.signed]]
        n=prefix['length_each_direction']
        pm=f'DommaschkSignedPrefixQ0R478{n:03}'
        if (cover['block_range']!=[5,649] or cover['module']!='DommaschkLowerCoverQ0R478L005R649'
                or cover['packet_sha256']!=packet or cover['package']!=package(5,649)
                or prefix['module']!=pm or n<=327 or prefix['packet_sha256']!=packet):
            p.error('the attachment requires exactly 644 original blocks and a true trajectory past slab 326')
        cp=list(map(Path,cover['import_paths']))
        sp=list(map(Path,[prefix['proof_root'],prefix['import_path']]))
        admitted(cp[0],cover['module'],cover['key'])
        admitted(sp[0],pm,prefix['key'])
        kp=[*keys,mark['key'],prefix['key'],cover['key']]
        overlay=merge_import_roots(a.cache/'birth',[root,*paths,*cp,*sp],kp)
        item=birth(n,pm,cover['module'])
        rb,done=compile_modules(a.cache/item[0],[item],[overlay],kp,a,'SecondaryCompleteLowerWellCache')
        out['birth']={k:done[k] for k in ['module','key','theorems','axioms']}
        out['birth'].update(signed_length=n,import_paths=list(map(str,[rb,overlay])))
        out['complete']=True
    save(a.output,out)
    print(json.dumps({k:v for k,v in out.items() if k not in ('import_paths','birth')}))


if __name__=='__main__':
    main()
