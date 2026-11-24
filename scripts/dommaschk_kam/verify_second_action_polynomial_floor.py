"""Join the actual second birth's native interior to the signed polynomial action integrals."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from screen_secondary_action_archive import archive
from verify_action_polynomial_shells import PACKAGE as SHELLS
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_secondary_action_cover import BAND_MODULE,THEORY,header
from verify_signed_mirror_passage import merge_import_roots


PACKAGE='SecondPolynomialActionCache'
CENTER=110


def source(original,pieces,stop):
    name=f'DommaschkQ0R478PolynomialFloor{stop:03}'
    cover=original['module']
    imports=['PlasmaLean.Design.DommaschkLowerActionPath','PlasmaLean.Certificates.ActionFloorShells',
             original['package']+'.'+cover,*[SHELLS+'.'+r['module'] for r in pieces]]
    s=header(name,imports)
    total=sum(m for _,m in archive()[327-CENTER:327+CENTER])
    mass=F(total,3072*2**40)
    s+=f'''
open MeasureTheory Certificates.PolynomialActionFloor
open DommaschkSecondaryActionMass Kinetic.MirrorHeightAction
def integrand (y : ℝ → Plane) (t : ℝ) := density y t * Real.sqrt (2*(height-field y t))
theorem center {{y : ℝ → Plane}} (track : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows {CENTER} y)
    (hn : ∀ t ∈ Icc (-{CENTER}/64:ℝ) ({CENTER}/64), 0 ≤ density y t)
    (cf : ContinuousOn (field y) (Icc (-{CENTER}/64:ℝ) ({CENTER}/64)))
    (cw : ContinuousOn (density y) (Icc (-{CENTER}/64:ℝ) ({CENTER}/64))) :
    ({mass}:ℝ) ≤ ∫ t in (-{CENTER}/64:ℝ)..({CENTER}/64), integrand y t := by
  have c := {cover}.cover track
  rw [{cover}.Covered,show {cover}.start = (-{CENTER}/64:ℝ) by norm_num [{cover}.start]] at c
  have b := Certificates.NativeActionInterval.exact_lower_mass
    (show {cover}.blocks.length = {CENTER}+{CENTER} by with_unfolding_all rfl) c hn cf cw
  rw [show total {cover}.blocks = {total} by kernel_fact] at b
  change _ ≤ action (field y) (density y) _ _ height
  norm_num at b ⊢
  exact b
'''
    full=mass+sum(F(r['signed_mass']) for r in pieces)
    s+=f'''
abbrev innerMass : ℝ := {full}
theorem estimate {{y : ℝ → Plane}} (track : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows {stop} y)
    (hn : ∀ t ∈ Icc (-{stop}/64:ℝ) ({stop}/64), 0 ≤ density y t)
    (cf : ContinuousOn (field y) (Icc (-{stop}/64:ℝ) ({stop}/64)))
    (cw : ContinuousOn (density y) (Icc (-{stop}/64:ℝ) ({stop}/64))) :
    innerMass ≤ action (field y) (density y) (-{stop}/64) ({stop}/64) height := by
  have continuous : ContinuousOn (integrand y) (Icc (-{stop}/64:ℝ) ({stop}/64)) :=
    cw.mul ((continuousOn_const.mul (continuousOn_const.sub cf)).sqrt)
  have incl {{n : ℝ}} (h : n ≤ {stop}/64) : Icc (-n) n ⊆ Icc (-{stop}/64:ℝ) ({stop}/64) :=
    Icc_subset_Icc (by linarith) h
  have cs : Icc (-{CENTER}/64:ℝ) ({CENTER}/64) ⊆ Icc (-{stop}/64:ℝ) ({stop}/64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have c{CENTER} := center (track.mono (by norm_num)) (fun t ht => hn t (cs ht)) (cf.mono cs) (cw.mono cs)
'''
    for r in pieces:
        a,b=r['start'],r['stop']
        mod=r['module']
        mass+=F(r['signed_mass'])
        s+=f'''  have h{b} : Shell (integrand y) ({a}/64) ({b}/64) {mod}.mass := by
    apply {mod}.shell (track.mono (by norm_num))
    change ContinuousOn (integrand y) _
    simpa only [neg_div] using continuous.mono (incl (n := {b}/64) (by norm_num))
  have step{b} := Shell.adjoin (F := integrand y) (by norm_num : (0:ℝ) ≤ {a}/64)
    (by norm_num : ({a}:ℝ)/64 ≤ {b}/64) (continuous.mono (incl (by norm_num))) h{b}
    (by simpa only [neg_div] using c{a})
  have c{b} : ({mass}:ℝ) ≤ ∫ t in (-{b}/64:ℝ)..({b}/64), integrand y t := by
    convert step{b} using 1 <;> norm_num [{mod}.mass]
'''
    s+=f'''  exact c{stop}
'''
    if stop==325:
        s+=f'''
theorem floor_on_enclosing_interval {{y : ℝ → Plane}} {{l r : ℝ}}
    (left : l ≤ -325/64) (right : 325/64 ≤ r)
    (track : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows 325 y)
    (hn : ∀ t ∈ Icc l r, 0 ≤ density y t) (cf : ContinuousOn (field y) (Icc l r))
    (cw : ContinuousOn (density y) (Icc l r)) : target < innerMass ∧
      innerMass ≤ action (field y) (density y) l r height := by
  have sub : Icc (-325/64:ℝ) (325/64) ⊆ Icc l r := Icc_subset_Icc left right
  have lower := estimate track (fun t ht => hn t (sub ht)) (cf.mono sub) (cw.mono sub)
  exact ⟨by norm_num [innerMass,target],lower.trans (Kinetic.MirrorActionEnvelope.action_mono_interval
    left (by norm_num) right cf cw hn)⟩
'''
    thms=['center','estimate']+(['floor_on_enclosing_interval'] if stop==325 else [])
    return (name,s+f'end PlasmaLean.Design.{name}\n',thms),full


def birth(pf,ground,stop):
    n=pf['length_each_direction']
    name=f'DommaschkQ0R478BirthPolynomial{stop:03}Of{n:03}'
    pm=pf['module']
    mod=ground['module']
    s=header(name,[SIGNED_PACKAGE+'.'+pm,PACKAGE+'.'+mod])
    s+=f'''
open {pm} {mod} DommaschkSecondaryActionMass Kinetic.MirrorHeightAction
open Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton
def Claims (y : ℝ → Plane) : Prop :=
  Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧
    innerMass ≤ action (field y) (DommaschkNativeWellAction.density y) (-{stop}/64) ({stop}/64) height

theorem on_path {{y : ℝ → Plane}} (path : Signed endpoint.start forwardRows backwardRows ({n}/64) y) : Claims y := by
  have f := path.forward
  have b := path.backward
  rw [show forwardRows = {BAND_MODULE}.fwdRows.take {stop} ++ forwardRows.drop {stop} by with_unfolding_all rfl] at f
  rw [show backwardRows = {BAND_MODULE}.backRows.take {stop} ++ backwardRows.drop {stop} by with_unfolding_all rfl] at b
  have reg := regions f.prefix b.prefix (n := {stop}) (by norm_num) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  have reg' : ∀ t ∈ Icc (-{stop}/64:ℝ) ({stop}/64), DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [Nat.cast_ofNat] using reg
  have room : Icc (-{stop}/64:ℝ) ({stop}/64) ⊆ Ioo (-({n}/64)) ({n}/64) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨cf,cw,eq⟩ := path.inputs room reg'
  have est := estimate (tracks_of_take f.prefix b.prefix)
    (fun t ht => by rw [← eq t ht]; exact norm_nonneg _) cf cw
  refine ⟨path,est.trans_eq ?_⟩
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num)] at ht
  exact congrArg (fun u => u * _) (eq t ht).symm

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ Claims := observe (by rfl) ({pm}.from_entry e) (fun _ => on_path)

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ-azimuth endpoint.opposite| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ Claims := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ small => from_entry (entry endpoint φ small)⟩
end PlasmaLean.Design.{name}
'''
    return name,s,['on_path','from_entry','from_nested_tori']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--center',required=True,type=Path)
    p.add_argument('--stop',type=int,required=True)
    p.add_argument('--shells',required=True,nargs='+',type=Path)
    p.add_argument('--signed',type=Path)
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/second-polynomial-action')
    a=p.parse_args()
    env(a)
    center=json.loads(a.center.read_text())
    if center['pairs']!=CENTER or center['module']!=f'DommaschkLowerCoverQ0R478L{327-CENTER:03}R{327+CENTER:03}':
        p.error('a verified native 110-pair lower-action center is required')
    inputs=list(map(Path,center['import_paths']))
    admitted(inputs[0],center['module'],center['key'])
    keys=[a.version,center['key'],digest(DESIGN/(THEORY+'.trace'))]
    pieces={}
    for path in a.shells:
        for _,r in json.loads(path.read_text()).items():
            i=r['start']
            if i<a.stop:
                if i in pieces or r['packet_sha256']!=center['packet_sha256']:
                    p.error(f'incompatible signed shell at {i}')
                pieces[i]=r
    seq=[]
    current=CENTER
    while current<a.stop and current in pieces:
        r=pieces[current]
        if r['stop']<=current:
            p.error('empty shell')
        roots=list(map(Path,r['import_paths']))
        admitted(roots[0],r['module'],r['key'])
        inputs.extend(roots)
        keys.append(r['key'])
        seq.append(r)
        current=r['stop']
    if not seq or current!=a.stop or len(seq)!=len(pieces):
        p.error(f'shells cover the outward interval only up to {current}')
    decl,mass=source(center,seq,a.stop)
    merged=merge_import_roots(a.cache,inputs,keys)
    base,r=compile_modules(a.cache/decl[0],[decl],[merged],keys,a,PACKAGE)
    out={k:r[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
    out.update(stop=a.stop,mass=str(mass),center=center['key'],shells=[q['key'] for q in seq],
               packet_sha256=center['packet_sha256'],import_paths=list(map(str,[base,merged])))
    save(a.output,out)
    if a.signed:
        pf=json.loads(a.signed.read_text())
        n=pf['length_each_direction']
        if n<=a.stop or pf['module']!=f'DommaschkSignedPrefixQ0R478{n:03}' or pf['packet_sha256']!=out['packet_sha256']:
            p.error('signed passage must extend beyond this complete action interval')
        paths=list(map(Path,[pf['proof_root'],pf['import_path']]))
        admitted(paths[0],pf['module'],pf['key'])
        chain=[*keys,r['key'],pf['key']]
        overlay=merge_import_roots(a.cache/'birth',[*paths,base,merged],chain)
        item=birth(pf,r,a.stop)
        rt,br=compile_modules(a.cache/item[0],[item],[overlay],chain,a,'SecondPolynomialBirthCache')
        out['birth']={k:br[k] for k in ['module','key','axioms','theorems','peak_rss_kib','wall_seconds']}
        out['birth']['import_paths']=list(map(str,[rt,overlay]))
        save(a.output,out)
    print(out['module'],out['key'],flush=True)


if __name__=='__main__':
    main()
