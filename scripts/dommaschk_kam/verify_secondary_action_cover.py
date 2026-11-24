"""Check a tree of consecutive original lower quadrature blocks and bind it to a signed birth."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from screen_secondary_action_archive import ARCHIVE, COUNT, archive
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_action_cells import PHYSICAL
from verify_secondary_mirror_band import BAND
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


BAND_MODULE = 'DommaschkQ0R478MirrorBranch327'
THEORY = 'DommaschkLowerActionPath'
BIRTH = 'SecondaryLowerCoverBirthCache'


def header(name, imports):
    return ('module\n' + ''.join(f'public import {s}\n' for s in imports) + f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature
open {THEORY} DommaschkEndpointMirrorBranch DommaschkMirrorLaunch Set
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false
''')


def ref(j):
    return (COUNT-1-j,'backward','back','2') if j<COUNT else (j-COUNT,'forward','fwd','1')


def split(l,r):
    # Separate the signs at the birth and keep outward groups aligned to powers of two.
    if l<COUNT<r:
        return COUNT
    if r-l<=4:
        return None
    width=1 << ((r-l-1).bit_length()-1)
    return r-width if r<=COUNT else l+width


def package(l,r):
    return f'SecondaryLowerCover{r-l:03}Cache'


def node(l,r,children):
    name=f'DommaschkLowerCoverQ0R478L{l:03}R{r:03}'
    k=max(ref(l)[0],ref(r-1)[0])+1
    cell=lambda i: f'DommaschkLowerCellsQ0R478{i:03}'
    imports=([f'{p}.{m}' for p,m,_ in children] if children else
             sorted({f'{PHYSICAL}.{cell(ref(j)[0])}' for j in range(l,r)}))
    src=header(name,['PlasmaLean.Design.'+THEORY,BAND+'.'+BAND_MODULE,*imports])
    src+=f'''
abbrev blocks := (DommaschkActionQ0R478.slabs.drop {l}).take {r-l}
abbrev start : ℝ := ({l}:ℝ)/64 - 327/64
def Covered (y : ℝ → Plane) : Prop :=
  Covers false (density y) (field y) DommaschkSecondaryActionMass.height start blocks

theorem cover {{y : ℝ → Plane}}
    (track : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows {k} y) : Covered y := by
  unfold Covered
'''
    if children:
        (_,first,width),(_,second,_)=children
        src+=f'''  have adjacent : blocks = {first}.blocks ++ {second}.blocks := by with_unfolding_all rfl
  rw [adjacent,covers_append_iff]
  refine ⟨{first}.cover (track.mono (by norm_num)), ?_⟩
  have clock : start + {first}.blocks.length/64 = {second}.start := by
    change start + ({width}:ℝ)/64 = _
    norm_num [start,{second}.start]
  rw [clock]
  exact {second}.cover (track.mono (by norm_num))
'''
    else:
        rows=[ref(j) for j in range(l,r)]
        original=', '.join(f'{cell(i)}.{side}Block' for i,side,_,_ in rows)
        src+=f'''  have original : blocks = [{original}] := by with_unfolding_all rfl
  rw [original]
  refine ⟨{', '.join(['?_']*len(rows)+['trivial'])}⟩
'''
        for i,side,branch,part in rows:
            mod=cell(i)
            src+=f'''  · have hi : {i} < {BAND_MODULE}.{branch}Rows.length := by change {i}<327; norm_num
    obtain ⟨prev,tube⟩ := track.{part} {i} (by norm_num) hi
    have link : {BAND_MODULE}.{branch}Rows[{i}] = {mod}.{side}Row := by with_unfolding_all rfl
    rw [link] at tube
    have h := {mod}.{side}_cells (prev := prev) (y := y) (by
      simpa only [Bool.false_eq_true,↓reduceIte,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,
        show ({i}:ℝ)+1={i+1} by norm_num] using tube)
    change Cells false (fun t => DommaschkPhysicalActionPanel.arcDensity (y t 0) t (y t 1))
      (fun t => DommaschkMirrorTubeCrossing.strength t (y t)) _ _ 48 {mod}.{side}Block.packed
    convert h using 1 <;> norm_num [start,DommaschkSecondaryActionMass.height,
      {mod}.height,DommaschkLowerTicksQ0R478{i:03}.height]
'''
    return name,src+f'\nend PlasmaLean.Design.{name}\n',['cover']


def bind(n,k,pm,cover,cpack):
    name=f'DommaschkQ0R478BirthCover{k:03}Of{n:03}'
    m=sum(s for _,s in archive()[COUNT-k:COUNT+k])
    mass=Fraction(m,3072*2**40)
    text=header(name,[f'{cpack}.{cover}',f'{SIGNED_PACKAGE}.{pm}'])
    text+=f'''
open Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton {pm}
abbrev mass : ℝ := {mass.numerator}/{mass.denominator}
abbrev level := DommaschkSecondaryActionMass.height
def Claims (y : ℝ → Plane) : Prop :=
  Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧ {cover}.Covered y ∧
    mass ≤ Kinetic.MirrorHeightAction.action (field y) (DommaschkNativeWellAction.density y)
      (-{k}/64) ({k}/64) level

theorem on_path {{y : ℝ → Plane}} (p : Signed endpoint.start forwardRows backwardRows ({n}/64) y) :
    Claims y := by
  have fsplit : forwardRows = {BAND_MODULE}.fwdRows.take {k} ++ forwardRows.drop {k} := by with_unfolding_all rfl
  have bsplit : backwardRows = {BAND_MODULE}.backRows.take {k} ++ backwardRows.drop {k} := by with_unfolding_all rfl
  have f := p.forward
  have b := p.backward
  rw [fsplit] at f
  rw [bsplit] at b
  have c := {cover}.cover (tracks_of_take f.prefix b.prefix)
  have box := regions f.prefix b.prefix (n := {k}) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  have inside : Icc (-{k}/64:ℝ) ({k}/64) ⊆ Ioo (-({n}/64)) ({n}/64) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have regular : ∀ t ∈ Icc (-{k}/64:ℝ) ({k}/64), DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [Nat.cast_ofNat,Nat.cast_one] using box
  obtain ⟨cf,cw,eq⟩ := p.inputs inside regular
  have land : {cover}.start = (-{k}/64:ℝ) := by norm_num [{cover}.start]
  have cells := c
  rw [{cover}.Covered,land] at cells
  have len : {cover}.blocks.length = {k}+{k} := by with_unfolding_all rfl
  have estimate := Certificates.NativeActionInterval.exact_lower_mass len cells
    (fun t ht => by rw [← eq t ht]; exact norm_nonneg _) cf cw
  have totalMass : total {cover}.blocks = {m} := by kernel_fact
  rw [totalMass] at estimate
  refine ⟨p,c,?_⟩
  have same : Kinetic.MirrorHeightAction.action (field y) (density y) (-{k}/64) ({k}/64) level =
      Kinetic.MirrorHeightAction.action (field y) (DommaschkNativeWellAction.density y) (-{k}/64) ({k}/64) level := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact congrArg (fun v => v * _) (eq t ht).symm
  rw [← same]
  norm_num [mass,level] at estimate ⊢
  exact estimate

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ Claims :=
  observe (by rfl) ({pm}.from_entry e) (fun _ => on_path)

theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ Claims := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry (entry endpoint φ h)⟩
'''
    return name,text+f'\nend PlasmaLean.Design.{name}\n',['on_path','from_entry','from_nested_tori']


def certify(a):
    checksum=digest(load(478)[1])
    band=json.loads(a.band.read_text())
    if band['module']!=BAND_MODULE or band['packet_sha256']!=checksum:
        raise ValueError('expected the original paired 327-row Q0R478 mirror bracket archive')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    core=[lake('lean','--version'),checksum,digest(ARCHIVE),digest(DESIGN/(THEORY+'.trace'))]
    bandroots=list(map(Path,band['import_paths']))
    admitted(bandroots[0],BAND_MODULE,band['key'])
    kern=[*core,band['key']]
    anchor=merge_import_roots(a.cache/'archive',bandroots,kern)
    def tree(l,r):
        mid=split(l,r)
        children=None
        if mid is not None:
            parents=[tree(l,mid),tree(mid,r)]
            children=[(v['package'],v['module'],width) for (v,_),width in zip(parents,[mid-l,r-mid],strict=True)]
        else:
            parents=[]
            for i in sorted({ref(j)[0] for j in range(l,r)}):
                rec=json.loads((a.row_cache/'rows'/f'{i:03}.json').read_text())
                if (rec['module'],rec['packet_sha256'],rec['archive_sha256'])!=(
                        f'DommaschkLowerCellsQ0R478{i:03}',checksum,core[2]):
                    raise ValueError(f'incompatible physical lower block {i}')
                paths=list(map(Path,rec['import_paths']))
                admitted(paths[0],rec['module'],rec['key'])
                parents.append((rec,paths))
        keys=[*kern,*[v['key'] for v,_ in parents]]
        overlay=merge_import_roots(a.cache/'tree',[p for _,ps in parents for p in ps],keys)
        pkg=package(l,r)
        item=node(l,r,children)
        root,record=compile_modules(a.cache/item[0],[item],[overlay,anchor],[pkg,*keys],a,pkg)
        return {**record,'package':pkg},[root,overlay]
    k=a.pairs
    rec,paths=tree(COUNT-k,COUNT+k)
    result={v:rec[v] for v in ['module','package','key','axioms','theorems']}
    result.update(pairs=k,physical_cells=96*k,block_range=[COUNT-k,COUNT+k],
                  packet_sha256=checksum,import_paths=list(map(str,[*paths,anchor])))
    if a.signed:
        prefix=json.loads(a.signed.read_text())
        n=prefix['length_each_direction']
        pm=f'DommaschkSignedPrefixQ0R478{n:03}'
        if prefix['packet_sha256']!=checksum or prefix['module']!=pm or n<=k:
            raise ValueError('the signed Q0R478 prefix must extend beyond the complete core')
        signed=[Path(prefix['proof_root']),Path(prefix['import_path'])]
        admitted(signed[0],pm,prefix['key'])
        keys=[*kern,rec['key'],prefix['key']]
        merged=merge_import_roots(a.cache/'birth',[*paths,anchor,*signed],keys)
        item=bind(n,k,pm,rec['module'],rec['package'])
        root,birth=compile_modules(a.cache/item[0],[item],[merged],keys,a,BIRTH)
        result['birth']={v:birth[v] for v in ['module','key','axioms','theorems']}
        result['birth'].update(import_paths=list(map(str,[root,merged])),signed_length=n,signed_key=prefix['key'])
    save(a.output,result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('import_paths','birth')},indent=2),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--band',type=Path,required=True)
    p.add_argument('--signed',type=Path)
    p.add_argument('--pairs',type=int,required=True)
    p.add_argument('--row-cache',type=Path,default=ROOT/'.lake/secondary-lower-action')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-lower-cover')
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    if not 1<=args.pairs<=COUNT:
        p.error('choose between 1 and 327 chronological pairs')
    certify(args)
