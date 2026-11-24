"""Attach the checked pre-mirror history, outward slopes and upper cap to one signed QA2R line."""
import argparse
import json
from pathlib import Path
import subprocess

from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules
from verify_grouped_mirror_exclusion import FINAL
from verify_mirror_height_band import row_source
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import HITS, SIGNS, load, tag
from verify_secondary_mirror_slopes import TUBE
from verify_signed_mirror_passage import merge_import_roots


CELLS = 'SecondaryMirrorRateCache'
BAND = 'SecondaryMirrorBandCache'


def localization(label,brackets,band):
    (a,c),(d,b) = brackets
    n = f'Dommaschk{label}MirrorTimeSeparation'
    low,high = tag(label,c-1,True,0),tag(label,d,False,1)
    text = f'''module
public import {BAND}.{band}
public import {SIGNS}.{low}
public import {SIGNS}.{high}
public import PlasmaLean.Theory.Kinetic.MirrorBranchCaps

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{n}
open Certificates.PositionFrameSlabs DommaschkEndpointMirrorBranch DommaschkMirrorEndpointSign
open DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign Kinetic.MirrorHeightBand Set {band}
set_option maxRecDepth 32768
set_option linter.style.longLine false

def lowHeight : Icc (height false : ℝ) (height true) :=
  ⟨height false,le_rfl,by norm_num [height]⟩
def highHeight : Icc (height false : ℝ) (height true) :=
  ⟨height true,by norm_num [height],le_rfl⟩
'''
    proofs = []
    for dr,sign,prefix in [('fwd','1',''),('back','(-1)','-')]:
        name = dr+'_root_separation'
        proofs.append(name)
        text += f'''
theorem {name} {{entry : State}} {{T : ℝ}} {{y : ℝ → Plane}}
    (path : Outward entry {dr}Rows {sign} T y) (br : {dr}Branch y) :
    br.time lowHeight ∈ Ioo ({a}/64) ({c}/64) ∧
    br.time highHeight ∈ Ioo ({d}/64) ({b}/64) ∧
    ({d-c}/64:ℝ) < br.time highHeight - br.time lowHeight ∧
    br.time highHeight - br.time lowHeight < ({b-a}/64:ℝ) := by
  obtain ⟨pl, first⟩ := path.at_row (i := {c-1}) (by change {c-1} < {b}; norm_num)
  obtain ⟨pu, second⟩ := path.at_row (i := {d}) (by change {d} < {b}; norm_num)
  have lc := first ({c}/64) (by norm_num)
  have uc := second ({d}/64) (by norm_num)
  have l : (height false : ℝ) < strength ({prefix}({c}/64)) (y ({c}/64)) := by
    simpa only [oriented,↓reduceIte] using {low}.{dr}_tube_sign (prev := pl)
      (by with_unfolding_all exact lc)
  have u : strength ({prefix}({d}/64)) (y ({d}/64)) < (height true : ℝ) := by
    simpa only [oriented,Bool.false_eq_true,↓reduceIte] using {high}.{dr}_tube_sign (prev := pu)
      (by with_unfolding_all exact uc)
  have lc' := br.time_lt_of_above lowHeight (by norm_num : (0:ℝ) ≤ {c}/64) l
  have uc' := br.lt_time_of_below highHeight (by norm_num : ({d}/64:ℝ) ≤ {b}/64) u
  have la := (br.interior_time lowHeight).1
  have ub := (br.interior_time highHeight).2
  exact ⟨⟨la,lc'⟩,⟨uc',ub⟩,by linarith,by linarith⟩
'''
        proofs.append(dr+'_time_derivative')
        text += f'''
theorem {dr}_time_derivative {{y : ℝ → Plane}} (br : {dr}Branch y) {{h : ℝ}}
    (inside : h ∈ Ioo (height false : ℝ) (height true)) :
    let order := inside.1.le.trans inside.2.le
    ∃ v > (1/400) / (2*h),
      HasDerivAt (fun t => strength {('t' if dr=='fwd' else '(-t)')} (y t)) v (br.timeAt order h) ∧
      HasDerivAt (br.timeAt order) v⁻¹ h ∧ 0 < v⁻¹ ∧ v⁻¹ < 800*h := by
  simpa only [show 2*h/(1/400:ℝ) = 800*h by ring] using
    br.timeAt_derivative (by norm_num [height]) (by norm_num) inside
'''
    return n,text+f'\nend PlasmaLean.Design.{n}\n',proofs


def rate_leaf(label,index,tube):
    old,src,proofs = row_source(index)
    name = f'Dommaschk{label}MirrorRate{index:03}'
    src = src.replace('MirrorSlopeClosedTubeCache.',TUBE+'.')
    src = src.replace(f'DommaschkMirrorSlope{index}ClosedTube',tube).replace(old,name)
    return name,src,proofs


def assembly(label,first,last,upper,prefix,caps,leaves):
    name = f'Dommaschk{label}MirrorBranch{last+1:03}'
    final_cap = tag(label,last,True,int(upper))
    imports = ['PlasmaLean.Design.DommaschkEndpointMirrorBranch',FINAL+'.'+prefix,
               HITS+'.'+caps,SIGNS+'.'+final_cap,*[CELLS+'.'+leaf for leaf,_ in leaves]]
    text = 'module\n'+''.join('public import '+m+'\n' for m in imports)
    text += f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkEndpointMirrorBranch DommaschkSignedMirrorBand
open DommaschkMirrorEndpointSign DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign
open DommaschkEndpointSignedTrace Kinetic.MirrorHeightBand Set
set_option linter.style.longLine false
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
'''
    high = f'height {str(upper).lower()}'
    ground = []
    for d,sign,clock,simp in [('fwd','1','t','one_mul'),('back','(-1)','(-t)','neg_one_mul')]:
        suff = ', '.join(tube+'.row_'+d for _,tube in leaves)
        text += f'''
def {d}Tail : List Step := [{suff}]
def {d}Rows := {prefix}.{d}Rows ++ {d}Tail
def {d}Branch (y : ℝ → Plane) := Branch (fun t => strength {clock} (y t))
  ({first}/64) ({last+1}/64) (height false) ({high}) (1/400)

theorem {d}_branch {{entry : State}} {{T : ℝ}} {{y : ℝ → Plane}}
    (path : Outward entry {d}Rows {sign} T y) (room : ({last+1}/64:ℝ) < T) :
    Nonempty ({d}Branch y) := by
  have early0 := ({prefix}.{d}_below entry).on_nonempty_prefix (post := {d}Tail)
    (by intro h; have v := congrArg List.length h; change {first} = 0 at v; omega)
    path.contained
  have early : ∀ t ∈ Icc 0 ({first}/64:ℝ), strength {clock} (y t) < height false := by
    simpa only [show {prefix}.{d}Rows.length = {first} by rfl, Nat.cast_ofNat, zero_add] using early0
  obtain ⟨prev, endRow⟩ := path.at_row (i := {last}) (by change {last} < {last+1}; norm_num)
  have inside := endRow ({last+1}/64) (by norm_num)
  have high : ({high}:ℝ) < strength ({('' if d=='fwd' else '-')}({last+1}/64)) (y ({last+1}/64)) := by
    simpa only [oriented,↓reduceIte] using {final_cap}.{d}_tube_sign
      (prev := prev) (by with_unfolding_all exact inside)
'''
        for i,(leaf,_) in enumerate(leaves,first):
            text += f'''  have slope{i} : Growth (fun t => strength {clock} (y t)) ({i}/64) ({i+1}/64) (1/400) := by
    have each := path.growth (i := {i}) (by change {i} < {last+1}; norm_num) (by norm_num)
      (by norm_num; linarith : (({i}:ℕ)+1 : ℝ)/64 < T) (k := 1/400) (by
        change SlabSlope {d}Rows[{i}] {sign} ({i}/64) ((({i}:ℝ)+1)/64) (1/400)
        rw [show ((({i}:ℝ)+1)/64) = {i+1}/64 by norm_num]
        with_unfolding_all exact {leaf}.{d})
    simpa only [{simp}, Nat.cast_ofNat, show ((({i}:ℝ)+1)/64) = {i+1}/64 by norm_num] using each
'''
        text += f'''  apply branch (by norm_num) (by norm_num) (by norm_num [height])
    (by norm_num [height]) (by norm_num) (fun _ => norm_nonneg _) early high
  exact slope{first}'''+''.join(f'\n    |>.append slope{i}' for i in range(first+1,last+1))+'\n'
        ground.append(d+'_branch')
    text += f'''
/-- Whenever the signed physical chain reaches the outer cap, both first-mirror height
branches refer to one and the same section trajectory with its original starting point. -/
theorem of_signed_chain {{entry : State}} {{fr br : List Step}} {{x : Plane}} {{fe be : Set Plane}} {{T : ℝ}}
    (path : Joined 0 T x fe be (physicalSlabs entry 0 (fwdRows ++ fr))
      (physicalSlabs entry 0 (backRows ++ br))) (room : ({last+1}/64:ℝ) < T) :
    ∃ y : ℝ → Plane, y 0 = x ∧ Outward entry fwdRows 1 T y ∧
      Outward entry backRows (-1) T (fun t => y (-t)) ∧
      Nonempty (fwdBranch y) ∧ Nonempty (backBranch (fun t => y (-t))) := by
  obtain ⟨y,hy,f,b⟩ := of_joined path
  exact ⟨y,hy,f.prefix,b.prefix,fwd_branch f.prefix room,back_branch b.prefix room⟩

end PlasmaLean.Design.{name}
'''
    return name,text,[*ground,'of_signed_chain']


def checked(manifest,label,checksum,name=None):
    if manifest['endpoint'] != label or manifest.get('packet_sha256',manifest.get('record_sha256')) != checksum:
        raise ValueError('proof belongs to a different physical endpoint')
    if name is not None and manifest['module'] != name:
        raise ValueError('wrong parent module')
    paths = list(map(Path,manifest['import_paths']))
    marker = admitted(paths[0],manifest['module'],manifest['key'])
    return paths,marker['key']


def birth_source(label,stop,n,band,prefix):
    from verify_endpoint_signed_prefix import SIGNED_PACKAGE
    name = f'Dommaschk{label}MirrorBandBirth{n:03}'
    text = f'''module
public import {SIGNED_PACKAGE}.{prefix}
public import {BAND}.{band}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkEndpointMirrorBranch DommaschkEndpointSignedTrace
open DommaschkMirrorLaunch DommaschkBounceField DommaschkKamC KamNewton
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set {prefix}
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
set_option linter.style.longLine false

/-- The actual physical approach and one common field line for the whole certified height band. -/
def Passage (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  let duration := |φ - azimuth endpoint.opposite|
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * duration = azimuth endpoint.opposite ∧
    a 0 = birth uC zC uA zA endpoint.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    y 0 = coordinates.symm (a duration) ∧
    Outward endpoint.start {band}.fwdRows 1 ({n}/64) y ∧
    Outward endpoint.start {band}.backRows (-1) ({n}/64) (fun t => y (-t)) ∧
    Nonempty ({band}.fwdBranch y) ∧ Nonempty ({band}.backBranch (fun t => y (-t)))

theorem from_entry_passage {{uC zC uA zA : FA}} {{φ : ℝ}} (entry : SectionEntry endpoint uC zC uA zA φ) :
    Passage uC zC uA zA φ := by
  obtain ⟨s,a,hs,hφ,src,ode,joined⟩ := {prefix}.from_entry entry
  have f : forwardRows = {band}.fwdRows ++ forwardRows.drop {stop} := by with_unfolding_all rfl
  have b : backwardRows = {band}.backRows ++ backwardRows.drop {stop} := by with_unfolding_all rfl
  have whole : Joined 0 ({n}/64) _ _ _ (physicalSlabs endpoint.start 0 forwardRows)
      (physicalSlabs endpoint.start 0 backwardRows) := joined
  rw [f,b] at whole
  obtain ⟨y,hy,fwd,back,first,second⟩ := {band}.of_signed_chain whole (by norm_num)
  exact ⟨s,a,y,hs,hφ,src,ode,hy,fwd,back,first,second⟩

theorem from_birth :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → Passage uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry_passage (entry endpoint φ h)⟩

end PlasmaLean.Design.{name}
'''
    return name,text,['from_entry_passage','from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--launch',type=int,default=478)
    p.add_argument('--caps',type=Path,required=True)
    p.add_argument('--exclusion',type=Path,required=True)
    p.add_argument('--slopes',type=Path,required=True)
    p.add_argument('--lower-only',action='store_true')
    p.add_argument('--signed',type=Path,help='also discharge the physical chain using a longer signed prefix')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-mirror-band')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    label,archive,_,brackets = load(args.launch)
    checksum = digest(archive)
    a = brackets[0][0]
    b = brackets[int(not args.lower_only)][1]
    caps,ex,slopes = [json.loads(f.read_text()) for f in (args.caps,args.exclusion,args.slopes)]
    roots,caps_key = checked(caps,label,checksum,f'Dommaschk{label}MirrorCrossings')
    more,prefix_key = checked(ex,label,checksum,f'Dommaschk{label}SubmirrorPrefix{a:03}')
    roots.extend(more)
    if slopes['endpoint'] != label or slopes['packet_sha256'] != checksum:
        p.error('the slope archive belongs to another endpoint')
    rows = {r['index']:r for r in slopes['rows']}
    if not all(i in rows for i in range(a,b)):
        p.error('require an audited closed-row slope on every intervening slab')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    version = lake('lean','--version')
    parents = [caps_key,prefix_key]
    leaves = []
    for i in range(a,b):
        r = rows[i]
        tube = f'Dommaschk{label}MirrorJet{i:03}Physical'
        ps,k = checked({**slopes,**r},label,checksum,tube)
        leaf = rate_leaf(label,i,tube)
        root,marker = compile_modules(args.cache/leaf[0],[leaf],ps,[checksum,version,k,
            digest(DESIGN/'DommaschkSignedMirrorBand.trace')],args,CELLS)
        parents.append(marker['key'])
        roots.extend([root,*ps])
        leaves.append((leaf[0],tube))
    table = assembly(label,a,b-1,not args.lower_only,ex['module'],caps['module'],leaves)
    overlay = merge_import_roots(args.cache,roots,parents)
    root,mark = compile_modules(args.cache/table[0],[table],[overlay],
        [checksum,version,parents,digest(DESIGN/'DommaschkEndpointMirrorBranch.trace')],args,BAND)
    data = {k:mark[k] for k in ('key','module','axioms','theorems')}
    data.update(endpoint=label,packet_sha256=checksum,parents=parents,import_paths=[str(root),str(overlay)])
    if not args.lower_only:
        loc = localization(label,brackets,table[0])
        lr,lm = compile_modules(args.cache/loc[0],[loc],[root,overlay],
            [checksum,version,mark['key'],caps_key,digest(DESIGN.parent/'Theory/Kinetic/MirrorBranchCaps.trace')],
            args,'SecondaryMirrorTimeCache')
        data['timing'] = {k:lm[k] for k in ('key','module','axioms','theorems')}
        data['timing'].update(import_paths=[str(lr),str(root),str(overlay)])
    if args.signed:
        signed = json.loads(args.signed.read_text())
        n = signed['length_each_direction']
        prefix = f'DommaschkSignedPrefix{label}{n:03}'
        if n<=b or signed['endpoint'].upper()!=label or signed['packet_sha256']!=checksum or signed['module']!=prefix:
            p.error(f'require this endpoint’s actual signed chain beyond row {b-1}')
        sr,so = Path(signed['proof_root']),Path(signed['import_path'])
        admitted(sr,prefix,signed['key'])
        parents = [mark['key'],signed['key']]
        all_imports = merge_import_roots(args.cache,[root,overlay,sr,so],parents)
        joined = birth_source(label,b,n,table[0],prefix)
        br,bm = compile_modules(args.cache/joined[0],[joined],[all_imports],[checksum,version,parents],
                                args,'SecondaryMirrorBandBirthCache')
        data['physical_birth'] = {k:bm[k] for k in ('key','module','axioms','theorems')}
        data['physical_birth'].update(parents=parents,import_paths=[str(br),str(all_imports)],signed_length=n)
    save(args.output,data)
    print(table[0],mark['key'],flush=True)


if __name__ == '__main__':
    main()
