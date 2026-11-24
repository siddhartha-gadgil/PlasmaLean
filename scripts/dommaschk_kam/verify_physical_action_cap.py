"""Prove the first chronological Q0R470 action cell, past its high mirror on the negative branch."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import subprocess

from bounce_mirror_pilot import HEIGHTS, Model, ORDER, R0M, SCALE, ZERO
from emit_sparse_taylor_slab import RECORD, ROOT, model_literal, models
from screen_physical_action_panels import packed_rows
from screen_sparse_reference_defects import bounds, sparse_fields
from verify_backward_physical_prefix import union
from verify_mirror_endpoint_signs import header
from verify_mirror_physical_hit import admitted
from verify_physical_action_launch import numeric
from verify_pre_mirror_signs import DESIGN, compile_modules, digest, inputs, jacobian, own_fields, save
from verify_signed_mirror_passage import merge_import_roots


ROW=324
Q=F(23,24)
TIME=F(15599,3072)


def nearest_box(lo,hi):
    lo=lo.__floor__()
    hi=hi.__ceil__()
    return Model([(lo+hi)//2],(hi-lo+1)//2)


def snap(m):
    value=sum(a*Q**i for i,a in enumerate(m.a))
    return nearest_box(value-m.e,value+m.e)


def panel_box(m):
    lo,hi=list(bounds(m,48))[-1]
    return nearest_box(F(lo,48**ORDER),F(hi,48**ORDER))


def matches(tag,rad,cols):
    return f'''private def {tag}Radius : Model := {model_literal(rad)}
private def {tag}Inputs : Inputs := ⟨{', '.join(map(model_literal,cols))}⟩
private theorem {tag}Matches : DommaschkPreMirrorSigns.Matches true row {tag}Radius {tag}Inputs := by
  constructor
  · exact eq_of_beq (by kernel_fact)
  · exact eq_of_beq (by kernel_fact)
  · exact eq_of_beq (by kernel_fact)
  all_goals kernel_fact
'''


def waves(tag):
    result=''
    witness='by norm_num [t]' if tag=='point' else 'by norm_num at ht ⊢; exact ht'
    for key,flag in [('cos','false'),('sin','true')]:
        result+=f'''  have {key}Mem : {tag}Inputs.{key}.Mem (128*t-649) (Real.{key} (2*t)) := by
    let p := DommaschkHarmonicBlock40.packet (4:Fin 8)
    have h := TrajectoryHarmonicPacket.physical p false 0 {flag} (t := t)
      ({witness})
    change ((p false 0).model {flag}).Mem _ _
    convert h using 1 <;> norm_num [TrajectoryTrig.wave]
'''
    return result


def source(name,arith,provider,raw,radial,cols,jac,quantity):
    jac_rad,jac_cols,jac_name,jac_imports,_=jac
    imports=['ActionPhysicalCache.'+arith,*jac_imports,'PlasmaLean.Design.DommaschkPhysicalActionCap',
             'PlasmaLean.Design.DommaschkHarmonicBlock40','PlasmaLean.Design.DommaschkActionQ0R470',
             'SignedSlopeCache.DommaschkSignedMonotone324']
    src=header(name,imports)
    src+='open Certificates Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel DommaschkPreMirrorSigns DommaschkMirrorEndpointSign DommaschkBounceField MirrorActionQuadrature Set\n'
    src+='abbrev row := DommaschkPositionFramesBack.block20[4]\n'
    src+=matches('point',*raw)+matches('range',jac_rad,jac_cols)
    src+=f'''private theorem point_speed {{previous : PositionFrameSlabs.State}} {{x : Plane}}
    (inside : x ∈ (physicalSlab previous row (324/64)).tube ({TIME}:ℝ)) :
    ({HEIGHTS[1]}:ℝ) ≤ strength (-({TIME}:ℝ)) x := by
  let t : ℝ := {TIME}
  have ht : t ∈ Icc (324/64:ℝ) (325/64) := by norm_num [t]
  obtain ⟨r,_,z⟩ := pointMatches.mem inside
  have clock : coord (324/64) ({TIME}:ℝ) = 128*t-649 := by norm_num [t,coord]
  rw [clock] at r z
  have time : 128*t-649 ∈ Icc ((({Q}):ℚ):ℝ) ((({Q}):ℚ):ℝ) := by norm_num [t]
'''
    src+=waves('point')
    rc,e=radial.a
    src+=f'''  have Rbox := constant_coord (box_on (c := {rc}) (e := {e}) (by kernel_fact) (by kernel_fact) time r 0)
  have bounds := abs_le.mp Rbox
  have pos : 0 < x 0 := by linarith only [bounds.1]
  obtain ⟨w,hw,rm⟩ := radial_parameter (by norm_num : (0:ℤ)<{e}) Rbox
  have inp : {provider}.trial.Mem w (x 0-dkR0) (-(x 1)) (Real.cos (2*t)) (Real.sin (2*t)) := by
    refine ⟨shifted_mem (u := {provider}.trial.u) rm (eq_of_beq (by kernel_fact)) (by kernel_fact), ?_,?_,?_⟩
'''
    for m,orig in zip(cols[1:],('z','cosMem','sinMem'),strict=True):
        src+=f'    · exact box_on (c := {m.a[0]}) (e := {m.e}) (by kernel_fact) (by kernel_fact) time {orig} w\n'
    src+=f'''  have speed := ({arith}.columns hw pos (by linarith only [bounds.2]) rm inp).2
  have le := (le_max_left _ (0:ℝ)).trans speed
  have reflected :=  strength_reflected pos t (-(x 1))
  rw [neg_neg] at reflected
  change _ ≤ ‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint (x 0) (-t) (x 1))‖
  rw [reflected]
  linarith only [le]

private theorem density_bound {{previous : PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}}
    (period : t ∈ Icc ({TIME}:ℝ) (325/64)) (inside : x ∈ (physicalSlab previous row (324/64)).tube t) :
    arcDensity (x 0) (-t) (x 1) ≤ ({quantity}:ℝ) := by
  have ht : t ∈ Icc (324/64:ℝ) (325/64) := ⟨by linarith only [period.1],period.2⟩
  obtain ⟨r,u,z⟩ := rangeMatches.mem inside
  have clock : coord (324/64) t = 128*t-649 := by unfold coord; ring
  rw [clock] at r u z
  have time : 128*t-649 ∈ Icc ((({Q}):ℚ):ℝ) ((1:ℚ):ℝ) :=
    ⟨by norm_num; linarith only [period.1],by norm_num; linarith only [period.2]⟩
  have hw : |128*t-649| ≤ 1 := abs_le.mpr ⟨by linarith only [ht.1],by linarith only [ht.2]⟩
'''
    src+=waves('range')
    src+=f'''  have inp : {jac_name}.trial.Mem (128*t-649) (x 0-dkR0) (-(x 1)) (Real.cos (2*t)) (Real.sin (2*t)) :=
    ⟨u,z,cosMem,sinMem⟩
  let field := fun p => atPoint p (x 0) t (-(x 1))
'''
    fields=[sum(models(term,jac_cols),ZERO) for term in sparse_fields()]
    lohi=[]
    for m,k,h in zip([jac_rad,*fields],['R','D','Nr','Nz'],
                     ['r',*[f'({jac_name}.{p}_checked.mem hw inp)' for p in ('dD','dnR','dnZ')]],strict=True):
        b=panel_box(m)
        lohi.append(b.bound())
        src+=f'''  have {k}B := abs_le.mp (constant_coord (box_on (c := {b.a[0]}) (e := {b.e}) (by kernel_fact) (by kernel_fact) time {h} 0))
'''
    U,D,N,Z=lohi[0][1],lohi[1][0],max(map(abs,lohi[2])),max(map(abs,lohi[3]))
    src+=f'''  have pos : 0 < x 0 := by linarith only [RB.1]
  have eq := arcDensity_reflected pos t (-(x 1))
  rw [neg_neg] at eq
  rw [eq]
  apply arcDensity_le_of_ranges (r := ({U}:ℝ)) (d := ({D}:ℝ)) (b := ({N}:ℝ)) (c := ({Z}:ℝ)) pos (by norm_num)
  · linarith only [RB.2]
  · norm_num
  · change _ ≤ field dD
    change _ ≤ field dD - _ ∧ _ at DB
    linarith only [DB.1]
  · change |field dnR| ≤ _
    change _ ≤ field dnR - _ ∧ field dnR - _ ≤ _ at NrB
    exact abs_le.mpr ⟨by linarith only [NrB.1],by linarith only [NrB.2]⟩
  · change |field dnZ| ≤ _
    change _ ≤ field dnZ - _ ∧ field dnZ - _ ≤ _ at NzB
    exact abs_le.mpr ⟨by linarith only [NzB.1],by linarith only [NzB.2]⟩
  all_goals norm_num

/-- The first chronological panel of the original packet has its true arclength
bound and exactly zero clipped speed on the physical downward-angle trajectory. -/
theorem physical_cell {{previous : PositionFrameSlabs.State}} {{y : ℝ → Plane}}
    (ode : ∀ t ∈ Icc (324/64) (325/64), HasDerivWithinAt y
      (DommaschkJacobian.euclideanFlow 0 (-1) t (y t)) (Icc (324/64) (325/64)) t)
    (tube : ∀ t ∈ Icc (324/64) (325/64), y t ∈ (physicalSlab previous row (324/64)).tube t) :
    Cell true (fun t => arcDensity (y (-t) 0) t (y (-t) 1)) (fun t => strength t (y (-t)))
      ({HEIGHTS[1]}:ℝ) (-325/64) (DommaschkActionQ0R470.slabs[0]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed := by
  change Cell true _ _ _ _ DommaschkActionQ0R470.slabGroup0[0].packed
  have d : density DommaschkActionQ0R470.slabGroup0[0].packed = {int(quantity*2**20)} := by kernel_fact
  have g : speedSq DommaschkActionQ0R470.slabGroup0[0].packed = 0 := by kernel_fact
  have mono := DommaschkSignedMonotone324.back_outward_mono (prev := previous) (y := y) ode tube
  have sample : ({TIME}:ℝ) ∈ Icc (324/64) (325/64) := by norm_num
  have above := point_speed (tube _ sample)
  intro t ht
  have cap : -t ∈ Icc ({TIME}:ℝ) (325/64) := ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
  have slab : -t ∈ Icc (324/64:ℝ) (325/64) := ⟨by linarith only [cap.1],cap.2⟩
  have den := density_bound cap (tube _ slab)
  have zero := zero_speed_of_monotone (f := fun t => strength (-t) (y t)) mono.monotoneOn
    sample slab cap.1 (norm_nonneg _) (norm_nonneg _) above
  simp only [neg_neg] at den zero
  change arcDensity _ _ _ ≤ _ ∧ max _ _ ≤ _
  rw [d,g]
  constructor
  · exact den
  · simpa only [Nat.cast_zero, zero_div] using zero.le

end PlasmaLean.Design.{name}
'''
    return src


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--monotone',required=True,type=Path)
    p.add_argument('--physical-hit',type=Path,
                   help='also prove existence of the actual panel trajectory from every local entry')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/physical-action-panels')
    p.add_argument('--jacobian-cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    a.cached_only=False
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    a.keys=[digest(RECORD),lake('lean','--version'),digest(DESIGN/'DommaschkBounceTaylor.trace')]
    mr=json.loads(a.monotone.read_text())
    mpaths=list(map(Path,mr['import_paths']))
    admitted(mpaths[0],'DommaschkSignedMonotone324',mr['key'])
    b,f=[t['steps'][ROW] for t in json.loads(gzip.decompress(RECORD.read_bytes()))['traces']]
    e=max(b['physical_radius_out'],f['physical_radius_out'])
    if b['coefficients']!=[f['coefficients'][0],[-v for v in f['coefficients'][1]]]:
        raise ValueError('unmatched physical reference')
    raw=inputs(f,ROW,e,e)
    a0=snap(raw[0])
    radial=Model([a0.a[0],a0.e])
    cols=(radial-R0M,*map(snap,raw[1][1:]))
    digit=packed_rows()[0]%(1<<72)
    den,g=F(digit%(1<<24),2**20),F((digit>>24)%(1<<24),2**26)
    if g!=0:
        raise ValueError('the first chronological panel must have a zero clipped-speed column')
    jac=jacobian(a,ROW,f,e)
    if not jac:
        raise ValueError('the row 324 whole-tube input provider is required')
    prov,imports,base=own_fields(a,ROW,'ActionCapSample',cols)
    arith='DommaschkActionCapSample324'
    src=numeric(arith,prov,imports,radial,cols,den,g)
    pkg='ActionPhysicalCache'
    proof=compile_modules(a.cache/arith,[(arith,src,['columns'])],[union(a.cache,base)],
                          [a.keys,*[r['key'] for _,r in base],digest(DESIGN/'DommaschkPhysicalActionPanel.trace')],a,pkg)
    dep=[*base,proof,*jac[4]]
    assembly='DommaschkFirstPhysicalActionCell'
    src=source(assembly,arith,prov,raw,radial,cols,jac,den)
    overlay=merge_import_roots(a.cache,[union(a.cache,dep),*mpaths],[*[r['key'] for _,r in dep],mr['key']])
    root,record=compile_modules(a.cache/assembly,[(assembly,src,['physical_cell'])],[overlay],
                                ['ActionPhysicalCellCache',a.keys,proof[1]['key'],mr['key'],digest(DESIGN/'DommaschkPhysicalActionCap.trace')],a,'ActionPhysicalCellCache')
    if a.physical_hit:
        physical=json.loads(a.physical_hit.read_text())
        paths=list(map(Path,physical['import_paths']))
        admitted(paths[0],'DommaschkPhysicalMirrorHitBackward324',physical['key'])
        keys=[a.keys,record['key'],physical['key']]
        overlay=merge_import_roots(a.cache,[root,overlay,*paths],keys)
        top='DommaschkFirstActionFromEntry'
        src=header(top,['ActionPhysicalCellCache.'+assembly,'PhysicalMirrorCache.DommaschkPhysicalMirrorHitBackward324'])
        src+=f'''open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature DommaschkPhysicalBackward324
open DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel

/-- From every local entry one and the same true ODE solution meets the high mirror
and realizes the first chronological panel of the archived quadrature. -/
theorem from_entry {{x : Plane}} (hx : x ∈ stateSet previous) :
    ∃ y : ℝ → Plane, y (324/64) = x ∧ y (325/64) ∈ stateSet (next row) ∧
      (∀ t ∈ Set.Icc (324/64:ℝ) (325/64),
        HasDerivWithinAt y (DommaschkJacobian.euclideanFlow 0 (-1) t (y t))
          (Set.Icc (324/64) (325/64)) t ∧ y t ∈ (physicalSlab previous row (324/64)).tube t) ∧
      (∃ t ∈ Set.Ioo (324/64:ℝ) (325/64), strength (-t) (y t) = DommaschkFirstMirrorLaunchSign.height true) ∧
      Cell true (fun t => arcDensity (y (-t) 0) t (y (-t) 1)) (fun t => strength t (y (-t)))
        ({HEIGHTS[1]}:ℝ) (-325/64) (DommaschkActionQ0R470.slabs[0]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed := by
  obtain ⟨y,hs,he,h,mirror⟩ := DommaschkPhysicalMirrorHitBackward324.hit_from_entry hx
  exact ⟨y,hs,he,h,mirror,{assembly}.physical_cell (fun t ht => (h t ht).1) (fun t ht => (h t ht).2)⟩

end PlasmaLean.Design.{top}
'''
        root,record=compile_modules(a.cache/top,[(top,src,['from_entry'])],[overlay],keys,a,'ActionPhysicalEntryCache')
    save(a.output,record | {'import_paths':[str(root),str(overlay)],'packet_sha256':a.keys[0]})


if __name__=='__main__':
    main()
