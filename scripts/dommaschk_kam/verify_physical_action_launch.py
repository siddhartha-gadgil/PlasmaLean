"""Check the original Q0R470 action density and squared speed on the two launch panels."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import subprocess

from bounce_mirror_pilot import HEIGHTS, SCALE, ZERO
from emit_sparse_taylor_slab import RECORD, ROOT, model_literal, models
from screen_physical_action_panels import packed_rows, radial_parameter_panel
from screen_sparse_reference_defects import sparse_fields
from verify_backward_physical_prefix import union
from verify_mirror_endpoint_signs import gap_proof, header
from verify_pre_mirror_signs import DESIGN, compile_modules, digest, inputs, own_fields, save


def numeric(name,provider,imports,rad,cols,density,g):
    h=HEIGHTS[1]-g/2
    src=header(name,['PlasmaLean.Design.DommaschkPhysicalActionPanel',*imports])
    src+='open DommaschkPhysicalActionPanel DommaschkMirrorEndpointSign DommaschkBounceField '+provider+'\n'
    gap=gap_proof(True,True,h,rad,cols)
    gap=gap.replace('DommaschkFirstMirrorLaunchSign.height true','('+str(h)+' : ℚ)')
    src+=gap
    den,nr,nz=[sum(models(terms,cols),ZERO) for terms in sparse_fields()]
    d=den.bound()[0]
    b,c=[max(map(abs,v.bound())) for v in (nr,nz)]
    r=rad.bound()[1]
    if not (d>0 and b*b+c*c<=(density*density-r*r)*d*d):
        raise ValueError('the independent bounds do not establish the arclength inequality')
    src+=f'''
theorem columns {{w R t z : ℝ}} (hw : |w| ≤ 1) (pos : 0 < R) (upper : R ≤ ({r}:ℝ))
    (rad : ({model_literal(rad)}).Mem w R)
    (inp : trial.Mem w (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t))) :
    arcDensity R t z ≤ ({density}:ℝ) ∧
    max (2 * (({HEIGHTS[1]}:ℝ) - ‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint R t z)‖)) 0 ≤ ({g}:ℝ) := by
  let f := fun q => atPoint q R t z
  have D := dD_range hw (dD_checked.mem hw inp)
  have Nr := dnR_range hw (dnR_checked.mem hw inp)
  have Nz := dnZ_range hw (dnZ_checked.mem hw inp)
  change _ ≤ f dD ∧ f dD ≤ _ at D
  change _ ≤ f dnR ∧ f dnR ≤ _ at Nr
  change _ ≤ f dnZ ∧ f dnZ ≤ _ at Nz
  apply upper_columns pos (by norm_num) (by norm_num) (by norm_num)
  · change 0 < f dD
    linarith only [D.1]
  · apply density_margin_of_ranges (r := ({r}:ℝ)) (d := ({d}:ℝ)) (b := ({b}:ℝ)) (c := ({c}:ℝ)) pos.le upper (by norm_num)
    · change _ ≤ f dD
      linarith only [D.1]
    · change |f dnR| ≤ _
      exact abs_le.mpr ⟨by linarith only [Nr.1], by linarith only [Nr.2]⟩
    · change |f dnZ| ≤ _
      exact abs_le.mpr ⟨by linarith only [Nz.1], by linarith only [Nz.2]⟩
    all_goals norm_num
  · have G := sign_on_models hw rad inp
    change 0 < gap R ((({h}:ℚ):ℝ)) (f dD) (f dnR) (f dnZ) at G
    convert G.le using 1
    norm_num [f]

end PlasmaLean.Design.{name}
'''
    return src


def physical(name,arithmetic,provider,rad,time_r,time_cols,cols,density,g):
    src=header(name,['ActionPhysicalCache.'+arithmetic,'PlasmaLean.Design.DommaschkActionQ0R470',
                     'PlasmaLean.Design.DommaschkHarmonicSlab0','PlasmaLean.Design.DommaschkSignedObservable'])
    src+='open Certificates Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel DommaschkPreMirrorSigns DommaschkMirrorEndpointSign MirrorActionQuadrature\n'
    src+=f'private def radius : Model := {model_literal(time_r)}\n'
    src+='private def timed : Inputs := ⟨'+', '.join(map(model_literal,time_cols))+'⟩\n'
    rc,e=rad.a
    src+=f'''private theorem panel {{t R z : ℝ}} (ht : t ∈ Set.Icc 0 (1/3072))
    (radial : radius.Mem (128*t-1) R) (vertical : timed.z.Mem (128*t-1) z) :
    arcDensity R t z ≤ ({density}:ℝ) ∧
    max (2 * (({HEIGHTS[1]}:ℝ) - ‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint R t z)‖)) 0 ≤ ({g}:ℝ) := by
  have htime : 128*t-1 ∈ Set.Icc (((-1):ℚ):ℝ) (((-23/24):ℚ):ℝ) :=
    ⟨by norm_num; linarith [ht.1], by norm_num; linarith [ht.2]⟩
  have clock : t ∈ Set.Icc (0/64:ℝ) (1/64) := ⟨by simpa using ht.1, by linarith [ht.2]⟩
  have Rbox := constant_coord (box_on (c := {rc}) (e := {e}) (by kernel_fact) (by kernel_fact) htime radial 0)
  have rs := abs_le.mp Rbox
  have pos : 0 < R := by linarith only [rs.1]
  obtain ⟨w,hw,rad⟩ := radial_parameter (by norm_num : (0:ℤ)<{e}) Rbox
  apply {arithmetic}.columns hw pos (by linarith only [rs.2]) rad
  refine ⟨shifted_mem (u := {provider}.trial.u) rad (eq_of_beq (by kernel_fact)) (by kernel_fact), ?_, ?_, ?_⟩
'''
    for j,(key,harmonic) in enumerate([('z',None),('cos','false'),('sin','true')],1):
        c,e=cols[j].a[0],cols[j].e
        if harmonic is None:
            source='vertical'
        else:
            source='wave'
            src+=f'''  · have wave : timed.{key}.Mem (128*t-1) (Real.{key} (2*t)) := by
      change (DommaschkHarmonicSlab0.model false 0 {harmonic}).Mem _ _
      simpa [TrajectoryTrig.wave] using DommaschkHarmonicSlab0.physical false 0 {harmonic} clock
'''
        bullet='  · ' if harmonic is None else '    '
        src+=f'{bullet}exact box_on (c := {c}) (e := {e}) (by kernel_fact) (by kernel_fact) htime {source} w\n'
    for tag in ('fwd','back'):
        rev=tag=='back'
        row='DommaschkPositionFrames'+tag.title()+'.block0[0]'
        lookup='(DommaschkActionQ0R470.slabGroup20[4].packed >>> (72*47))' if rev else 'DommaschkActionQ0R470.slabGroup20[5].packed'
        flag=str(rev).lower()
        start='(-1/3072:ℝ)' if rev else '(0:ℝ)'
        phase='(-t)' if rev else 't'
        src+=f'''
private theorem {tag}Matches : Matches {flag} {row} radius timed := by
  constructor
  · exact eq_of_beq (by kernel_fact)
  · exact eq_of_beq (by kernel_fact)
  · exact eq_of_beq (by kernel_fact)
  all_goals kernel_fact

/-- An original action cell on every path enclosed in its physical slab. -/
theorem {tag}_cell {{y : ℝ → Plane}} {{previous : State}}
    (inside : ∀ t ∈ Set.Icc (0:ℝ) (1/3072), y {phase} ∈ (physicalSlab previous {row} 0).tube t) :
    Cell true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
      ({HEIGHTS[1]}:ℝ) {start} {lookup} := by
  have den : density {lookup} = {int(density*2**20)} := by kernel_fact
  have speedSqEq : speedSq {lookup} = {int(g*2**26)} := by kernel_fact
  intro t ht
  change arcDensity _ _ _ ≤ _ ∧ max _ _ ≤ _
  rw [den, speedSqEq]
'''
        sign='(-t)' if rev else 't'
        src+=f'''  have member : {sign} ∈ Set.Icc (0:ℝ) (1/3072) := ⟨by linarith [ht.1,ht.2], by linarith [ht.1,ht.2]⟩
  have tube := inside {sign} member
'''
        if rev:
            src+='  rw [neg_neg] at tube\n'
        src+=f'''  obtain ⟨r,u,z⟩ := {tag}Matches.mem tube
  rw [show coord 0 {sign} = 128*{sign}-1 by simp [coord]] at r z
'''
        zval='(-(y t 1))' if rev else '(y t 1)'
        src+=f'''  change timed.z.Mem (128*{sign}-1) {zval} at z
  have cols := panel member r z
'''
        if rev:
            src+=f'''  have positive : 0 < y t 0 := DommaschkMirrorBracketSlab.positive_radius
    (a := 0) (r := {row}) ⟨by linarith [member.1],by linarith [member.2]⟩ tube (by kernel_fact) (by kernel_fact)
  have ar := arcDensity_reflected positive (-t) (-(y t 1))
  have st := strength_reflected positive (-t) (-(y t 1))
  simp only [neg_neg] at ar st
  rw [← ar, ← st] at cols
'''
        src+='  simpa [strength] using cols\n'
    src+='''open DommaschkBackwardPairedPrefix DommaschkSignedObservable DommaschkMirrorLaunch

abbrev fw := DommaschkPhysicalFirstStep.row
abbrev bw := DommaschkJacobianBackward000.row

private theorem packed_fw :
    (DommaschkActionQ0R470.slabs[325]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed =
      DommaschkActionQ0R470.slabGroup20[5].packed := rfl

private theorem packed_bw :
    (DommaschkActionQ0R470.slabs[324]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed =
      DommaschkActionQ0R470.slabGroup20[4].packed := rfl
'''
    for row,sign,source,bd in [('fw','1','DommaschkPhysicalFirstStep','ball_field_bounds'),
                               ('bw','(-1)','DommaschkPhysicalBackwardFirstStep','field_bounds')]:
        src+=f'''private theorem {row}Dir : Direction {sign} 1 (next {row}) [{row}] := by
  refine ⟨?_,{source}.{bd},trivial⟩
  apply Chain.cons (m := next {row}) (n := 0)
  · simp only [run, Bool.and_true]
    exact congrArg (fun k => (k,next {row})) {source}.checked
  · exact .nil _
'''
    src+=f'''
/-- One actual trajectory through each admitted Q-16 birth realizes both original action cells. -/
theorem exists_nested_launch_cells :
    BirthWith (fun x => ∃ y : ℝ → Plane, DommaschkSignedObservable.Path 1 (next fw) (next bw) [fw] [bw] x y ∧
      (Cell true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
        ({HEIGHTS[1]}:ℝ) 0 (DommaschkActionQ0R470.slabs[325]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed ∧
       Cell true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
        ({HEIGHTS[1]}:ℝ) (-1/3072) ((DommaschkActionQ0R470.slabs[324]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)).packed >>> (72*47)))) := by
  rw [packed_fw, packed_bw]
  apply birth_with (birthPassage fwDir bwDir)
  intro x y path
  constructor
  · apply fwd_cell (previous := MirrorEndpoint.start .q0r470)
    intro t ht
    apply path.forward (physicalSlab _ fw 0) (by simp [physicalSlabs]) t
    exact ⟨ht.1,by change t ≤ 0+1/64; linarith only [ht.2]⟩
  · apply back_cell (previous := MirrorEndpoint.start .q0r470)
    intro t ht
    apply path.backward (physicalSlab _ bw 0) (by simp [physicalSlabs]) t
    exact ⟨ht.1,by change t ≤ 0+1/64; linarith only [ht.2]⟩
'''
    return src+'\nend PlasmaLean.Design.'+name+'\n'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/physical-action-panels')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    a.cached_only=False
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    a.keys=[digest(RECORD),lake('lean','--version'),digest(DESIGN/'DommaschkBounceTaylor.trace')]
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    b,f=[t['steps'][0] for t in packet['traces']]
    if (b['coefficients']!=[f['coefficients'][0],[-z for z in f['coefficients'][1]]]
            or packet['section_in_half_pi']!=0 or packet['launch_u']!='47/100'):
        raise ValueError('expected reflected section-zero launch rows')
    er=max(b['physical_radius_out'],f['physical_radius_out'])
    timed,columns=inputs(f,0,er,er)
    radial,cols=radial_parameter_panel(timed,columns,0)
    packed=packed_rows()
    digit=packed[325]%(1<<72)
    if digit!=packed[324]>>(47*72):
        raise ValueError('launch panels have different signed columns')
    density,g=F(digit%(1<<24),2**20),F((digit>>24)%(1<<24),2**26)
    provider,imports,base=own_fields(a,0,'LaunchAction',cols)
    arithmetic='DommaschkLaunchActionColumns'
    source=numeric(arithmetic,provider,imports,radial,cols,density,g)
    overlay=union(a.cache,base)
    pkg='ActionPhysicalCache'
    data=compile_modules(a.cache/arithmetic,[(arithmetic,source,['columns'])],[overlay],
                         [a.keys,*[r['key'] for _,r in base],digest(DESIGN/'DommaschkPhysicalActionPanel.trace')],a,pkg)
    top='DommaschkPhysicalLaunchAction'
    source=physical(top,arithmetic,provider,radial,timed,columns,cols,density,g)
    overlay=union(a.cache,[*base,data])
    root,record=compile_modules(a.cache/top,[(top,source,['fwd_cell','back_cell','exists_nested_launch_cells'])],[overlay],
                                ['ActionPhysicalCellCache',a.keys,data[1]['key'],digest(DESIGN/'DommaschkActionQ0R470.trace')],a,'ActionPhysicalCellCache')
    save(a.output,record | {'import_paths':[str(root),str(overlay)],'packet_sha256':a.keys[0]})


if __name__=='__main__':
    main()
