"""Check field-strength signs on archived physical mirror-bracket endpoint boxes."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import subprocess

from bounce_mirror_pilot import Model, ONE, R0M, SCALE, ZERO, angle_models
from emit_sparse_taylor_slab import RECORD, ROOT, field, model_literal, models
from screen_sparse_reference_defects import sparse_fields
from verify_backward_physical_prefix import compile_modules, union
from verify_physical_trace_slabs import DESIGN, digest, save


PACKAGE = 'MirrorSignCache'
INPUTS = 'MirrorInputsCache'
FIELDS = 'MirrorFieldsCache'
ARCHIVE = RECORD.with_name('bounce_local_graphs_20261123.json')


def header(stem, imports):
    return ('module\n' + ''.join('public import '+s+'\n' for s in imports)
            + '\n@[expose] public section\nnoncomputable section\nnamespace PlasmaLean.Design.'+stem
            + '\nopen Certificates.TrajectoryTaylorModel DommaschkKam DommaschkKam.DkPoly'
            + ' DommaschkBounceTaylor\nset_option maxRecDepth 16000\n'
            + 'set_option linter.style.longLine false\nset_option Elab.async false\n')


def endpoint_data(index, right, traces):
    back, forward = (trace['steps'][index] for trace in traces)
    side = 1 if right else -1
    def endpoint(coefficients):
        return sum(c*side**j for j,c in enumerate(coefficients))
    r,z = map(endpoint,forward['coefficients'])
    if tuple(map(endpoint,back['coefficients'])) != (r,-z):
        raise ValueError('reflected endpoint coordinates differ')
    error = max(d['physical_radius_out'] for d in (back,forward))
    radial = Model([r,error])
    angles = angle_models(F(2*index+1,128),F(1,128),F(0))
    columns = (radial-R0M,Model([z],error),
               *(Model([endpoint(v.a)],v.e) for v in (angles[2],angles[1])))
    return radial,columns


def gap_proof(upper,right,height,radial,cols,*,field_values=None):
    upper_s,right_s = (str(k).lower() for k in (bool(upper),right))
    height_expr = f'((DommaschkFirstMirrorLaunchSign.height {upper_s} : ℚ) : ℝ)'
    decl = []
    lines = [f'''theorem sign_on_models {{w R z c s : ℝ}} (hw : |w| ≤ 1)
    (rad : ({model_literal(radial)}).Mem w R) (inp : trial.Mem w (R-dkR0) z c s) :
    oriented {right_s} (gap R {height_expr} (evR (R-dkR0) z c s dD)
      (evR (R-dkR0) z c s dnR) (evR (R-dkR0) z c s dnZ)) 0 := by''']
    table = {'R': (radial,'R','rad')}
    physical_angles=field_values is not None
    if physical_angles:
        lines[0]=lines[0].replace('(hw : |w| ≤ 1)','(hw : |w| ≤ 1) (hc : |c| ≤ 1) (hs : |s| ≤ 1)')
    else:
        field_values=[sum(models(terms,cols),ZERO) for terms in sparse_fields()]
    for key,poly,value in zip(('D','nr','nz'),('dD','dnR','dnZ'),field_values,strict=True):
        lines.append(f'  let {key} := evR (R-dkR0) z c s {poly}')
        checked=f'{poly}_checked.mem hw inp'+(' hc hs' if physical_angles else '')
        lines.append(f'  have in_{key} : {poly}0.Mem w {key} := {checked}')
        table[key] = (value,key,'in_'+key)
    for key,value,expr in [('h',height,height_expr),('neg',F(-1),'(-1:ℝ)')]:
        model = Model.rational(value)
        decl.append(f'private def model_{key} : Model := {model_literal(model)}')
        lines.append(f'  have in_{key} : model_{key}.Mem w {expr} := by')
        if key == 'h':
            lines.append(f'    exact enclose hw (constant_mem (DommaschkFirstMirrorLaunchSign.height'
                         +f' {upper_s}) w) (by kernel_fact)')
        else:
            lines.append(f'    simpa only [Rat.cast_neg, Rat.cast_one] using (enclose (c := model_{key}) hw'
                         +f' (constant_mem ({value}) w) (by kernel_fact))')
        table[key]=(model,expr,'in_'+key)
    def binary(key,left,right,op):
        a,x,ha = table[left]
        b,y,hb = table[right]
        model = a*b if op == '*' else a+b
        action = f'mem_product_fit hw {ha} {hb}' if op == '*' else f'enclose hw (mem_add {ha} {hb})'
        decl.append(f'private def model_{key} : Model := {model_literal(model)}')
        lines.append(f'  let value_{key} := {x} {op} {y}')
        lines.append(f'  have in_{key} : model_{key}.Mem w value_{key} := {action} (by kernel_fact)')
        table[key]=model,'value_'+key,'in_'+key
    for k,l,r,o in [('rr','R','R','*'),('r4','rr','rr','*'),('r8','r4','r4','*'),
                    ('h8','h','r8','*'),('minus','neg','h8','*'),('rd','R','D','*'),
                    ('diff','rd','minus','+'),('sum','rd','h8','+'),('prod','diff','sum','*'),
                    ('nr2','nr','nr','*'),('nz2','nz','nz','*'),('a','prod','nr2','+'),
                    ('final','a','nz2','+')]:
        binary(k,l,r,o)
    m,_,_ = table['final']
    lo,hi = m.bound()
    if not (lo > 0 if right else hi < 0):
        raise ValueError(f'endpoint score straddles zero: {lo}..{hi}')
    mid,width=(lo+hi)/2,(hi-lo)/2
    lines.extend([f'  have g : value_final = gap R {height_expr} D nr nz := by',
                  '    dsimp only ['+', '.join(v for _,v,_ in table.values() if v.startswith('value_'))+', gap]',
                  '    ring',
                  f'  have bound := enclose (c := ⟨[({mid})],({width})⟩) hw in_final (by kernel_fact)',
                  '  rw [g] at bound',
                  '  change oriented '+right_s+' (gap R '+height_expr+' D nr nz) 0',
                  '  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le, oriented] at bound ⊢',
                  '  linarith only [bound.1,bound.2]'])
    return '\n'.join(decl+['']+lines)+'\n'


def point_proof(stem,index,upper,right,radial,cols):
    upper_s,right_s = (str(k).lower() for k in (bool(upper),right))
    t = f'({index+int(right)}/64:ℝ)'
    s = '1' if right else '(-1)'
    rc,e = radial.a
    zc = cols[1].a[0]
    block,offset=divmod(index,8)
    hmodel = f'DommaschkHarmonicBlock{block:02}.packet ({offset}:Fin 8)'
    angle = []
    for key, col, flag, fun in [('c','cos','false','Real.cos'),('s','sin','true','Real.sin')]:
        angle.append(f'''  have in_{key} : trial.{col}.Mem w ({fun} (2*{t})) := by
    let m := (({hmodel}) false 0).model {flag}
    have hh := Certificates.TrajectoryHarmonicPacket.physical ({hmodel}) false 0 {flag}
      (t := {t}) (by norm_num)
    have held : m.Mem (({s}:ℚ):ℝ) ({fun} (2*{t})) := by
      convert hh using 1 <;> norm_num [Certificates.TrajectoryTrig.wave]
    have snap : (⟨[Certificates.QPoly.evalQ m.poly {s}], m.radius⟩ : Model) = trial.{col} := by
      apply Matches.eq
      constructor <;> apply eq_of_beq <;> kernel_fact
    rw [← snap]
    exact at_fixed_time held w''')
    src=f'''
/-- True field-strength sign for every point in the endpoint coordinate enclosure. -/
theorem sign_on_box {{R z : ℝ}} (rh : |R - ({rc}:ℝ)/2^80| ≤ ({e}:ℝ)/2^80)
    (zh : |z - ({zc}:ℝ)/2^80| ≤ ({e}:ℝ)/2^80) :
    oriented {right_s} ‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint R {t} z)‖
      (DommaschkFirstMirrorLaunchSign.height {upper_s}) := by
  obtain ⟨w,hw,rad⟩ := radial_parameter (c := {rc}) (e := {e}) (by norm_num) rh
  have rs : 0 < R := by rw [abs_le] at rh; linarith only [rh.1]
  have in_u : trial.u.Mem w (R - dkR0) := by
    rw [mem_ofDyadic_iff] at rad
    change ({model_literal(cols[0])}).Mem _ _ 
    rw [mem_ofDyadic_iff]
    norm_num [Certificates.QPoly.eval, dkR0] at rad ⊢
    linarith only [rad]
  have in_z : trial.z.Mem w z := by
    change ({model_literal(cols[1])}).Mem _ _
    norm_num [Model.Mem, ofDyadic, Certificates.QPoly.eval, Certificates.QPoly.scale] at zh ⊢
    simpa using zh
'''+'\n'.join(angle)+f'''
  apply physical_sign {right_s} rs (by norm_num [DommaschkFirstMirrorLaunchSign.height])
  exact sign_on_models hw rad ⟨in_u,in_z,in_c,in_s⟩
'''
    for back,sector in ((False,'Fwd'),(True,'Back')):
        row=f'DommaschkPositionFrames{sector}.block{index//16}[{index%16}]'
        z0=-zc if back else zc
        sign='-' if back else ''
        tag=sector.lower()
        src+=f'''
private def row_{tag} : Step := {row}
private theorem point_{tag} : DommaschkMirrorBracketSlab.endPoint {right_s} row_{tag} =
    (⟨{rc},{z0}⟩ : Point) := by rfl
private theorem cap_{tag} : row_{tag}.physicalOut ≤ {e} := by kernel_fact

/-- The sign applies to every true point in the {sector} physical slab at this endpoint. -/
theorem {tag}_tube_sign {{prev : Certificates.PositionFrameSlabs.State}} {{x : Plane}}
    (hx : x ∈ (physicalSlab prev {row} ({index}/64)).tube {t}) :
    oriented {right_s} (DommaschkMirrorTubeCrossing.strength ({sign}{t}) x)
      (DommaschkFirstMirrorLaunchSign.height {upper_s}) := by
  have clock : DommaschkMirrorBracketSlab.endTime {right_s} ({index}/64) = {t} := by
    norm_num [DommaschkMirrorBracketSlab.endTime]
  have inside : x ∈ (physicalSlab prev row_{tag} ({index}/64)).tube
      (DommaschkMirrorBracketSlab.endTime {right_s} ({index}/64)) := clock.symm ▸ hx
  obtain ⟨cr,cz⟩ := DommaschkMirrorBracketSlab.end_coordinates point_{tag} cap_{tag} inside
  simp only [{('Int.cast_neg, ' if min(rc,z0)<0 else '')}Int.cast_ofNat, Nat.cast_ofNat] at cr cz
'''
        if not back:
            src+='  exact sign_on_box cr cz\n'
        else:
            src+=f'''  have radial := cr
  have rs : 0 < x 0 := by rw [abs_le] at radial; linarith only [radial.1]
  have vertical : |-(x 1) - ({zc}:ℝ)/2^80| ≤ ({e}:ℝ)/2^80 := by
    rw [show -(x 1) - ({zc}:ℝ)/2^80 = -(x 1 - ({z0}:ℝ)/2^80) by ring, abs_neg]
    exact cz
  have eq := DommaschkMirrorTubeCrossing.strength_reflected rs {t} (-(x 1))
  rw [neg_neg] at eq
  unfold DommaschkMirrorTubeCrossing.strength
  rw [eq]
  exact sign_on_box radial vertical
'''
    return src


def check_sign(cache,args,keys,stem,index,upper,right,height,radial,cols,packages):
    imports=['PlasmaLean.Design.DommaschkMirrorBracketSlab',
             f'PlasmaLean.Design.DommaschkHarmonicBlock{index//8:02}',
             *[FIELDS+'.'+stem+l for l in ('D','R','Z')]]
    source=header(stem,imports)+'open DommaschkMirrorEndpointSign Certificates.PositionFrameSlabs\n'
    source+='set_option maxHeartbeats 1600000\n'
    source+=gap_proof(upper,right,height,radial,cols)
    source+=point_proof(stem,index,upper,right,radial,cols)+'\nend PlasmaLean.Design.'+stem+'\n'
    overlay=union(cache,packages)
    base,record=compile_modules(cache/stem,[(stem,source,['sign_on_box','fwd_tube_sign','back_tube_sign'])],
                                [overlay],[keys,*[r['key'] for _,r in packages],
                                digest(DESIGN/'DommaschkMirrorBracketSlab.trace'),
                                digest(DESIGN/f'DommaschkHarmonicBlock{index//8:02}.trace')],args,PACKAGE)
    print(f'verified signed physical endpoint {stem}: {record["key"]}',flush=True)
    public={k:v for k,v in record.items() if k!='artifacts'} | {'import_paths':[str(base),str(overlay)]}
    return public,[*packages,(base,record)]


def bracket(cache,args,keys,index,upper,packages):
    stem=f'DommaschkMirrorBracket{index:03}'
    left,right=(f'DommaschkMirrorSign{index:03}'+side for side in ('Left','Right'))
    src=header(stem,[PACKAGE+'.'+left,PACKAGE+'.'+right])
    src+='open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing\n'
    upper_s=str(bool(upper)).lower()
    for tag,sgn in [('fwd',1),('back',-1)]:
        row=f'DommaschkPositionFrames{tag.title()}.block{index//16}[{index%16}]'
        src+=f'''
/-- A continuous trajectory in the actual {tag} slab encounters the specified mirror height. -/
theorem {tag}_hit {{prev : State}} {{y : ℝ → Plane}}
    (hy : ContinuousOn y (Set.Icc ({index}/64) ({index+1}/64)))
    (inside : ∀ t : ℝ, t ∈ Set.Icc ({index}/64) ({index+1}/64) →
      y t ∈ (physicalSlab prev {row} ({index}/64)).tube t) :
    ∃ t : ℝ, t ∈ Set.Ioo ({index}/64) ({index+1}/64) ∧
      strength (({sgn}:ℝ)*t) (y t) = DommaschkFirstMirrorLaunchSign.height {upper_s} := by
  have stop : ({index}/64:ℝ) + 1/64 = {index+1}/64 := by norm_num
  rw [← stop] at hy inside ⊢
  apply DommaschkMirrorBracketSlab.hit hy inside (by kernel_fact) (by kernel_fact)
  · intro x hx
    simpa [DommaschkMirrorEndpointSign.oriented] using {left}.{tag}_tube_sign hx
  · rw [stop]
    intro x hx
    simpa [DommaschkMirrorEndpointSign.oriented] using {right}.{tag}_tube_sign hx
'''
    src+='\nend PlasmaLean.Design.'+stem+'\n'
    overlay=union(cache,packages)
    root,r=compile_modules(cache/stem,[(stem,src,['fwd_hit','back_hit'])],[overlay],
                           [keys,*[r['key'] for _,r in packages]],args,'MirrorBracketCache')
    print(f'verified physical mirror bracket {index} in both directions: {r["key"]}',flush=True)
    return {k:v for k,v in r.items() if k!='artifacts'} | {'import_paths':[str(root),str(overlay)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/mirror-signs')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--fields-only',action='store_true')
    a = parser.parse_args()
    packet = json.loads(gzip.decompress(RECORD.read_bytes()))
    if (packet['section_in_half_pi'] != 0 or packet['launch_u'] != '47/100'
            or packet['coordinate_denominator'] != SCALE
            or [p['direction'] for p in packet['traces']] != [-1,1]):
        raise ValueError('expected the two signed q0/u=.470 records')
    sector, = (s for s in json.loads(ARCHIVE.read_text())['sections'] if s['section_in_half_pi'] == 0)
    record, = (e for e in sector['endpoints'] if e['launch_radius'] == '47/100')
    b,f = record['crossings']
    if b['brackets'] != f['brackets'] or not (b['success'] and f['success']):
        raise ValueError('expected two matching, accepted outward brackets')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    cache = a.cache.resolve()
    version = lake('lean','--version')
    packet_keys = [digest(RECORD),digest(ARCHIVE),version]
    results = {'boundaries':[],'brackets':[]}
    for upper,(ends,h) in enumerate(zip(f['brackets'],record['heights'],strict=True)):
        start,end = (64*F(e) for e in ends)
        if start.denominator != 1 or end-start != 1:
            raise ValueError('expected one slab bracket')
        index = int(start)
        bracket_packages = []
        for right in (False,True):
            radial,cols = endpoint_data(index,right,packet['traces'])
            stem = f'DommaschkMirrorSign{index:03}'+('Right' if right else 'Left')
            tail = '\nend PlasmaLean.Design.'+stem+'\n'
            inp = stem+'Inputs'
            insrc = (header(stem,['PlasmaLean.Design.DommaschkBounceTaylor'])
                     +'def trial : Inputs := ⟨'+', '.join(map(model_literal,cols))+'⟩\n'+tail)
            base = compile_modules(cache/inp,[(inp,insrc,[])],[],packet_keys+[
                                   digest(DESIGN/'DommaschkBounceTaylor.trace'),INPUTS],a,INPUTS)
            pieces = []
            for label,p in zip(('D','R','Z'),('dD','dnR','dnZ'),strict=True):
                name = stem+label
                src = header(stem,[INPUTS+'.'+inp])+field(p,cols)+tail
                pieces.append(compile_modules(cache/name,[(name,src,[])],[base[0]],
                                               [base[1]['key'],FIELDS],a,FIELDS))
            print(f'checked {stem}: all three full sparse polynomials',flush=True)
            if not a.fields_only:
                result,dependencies = check_sign(cache,a,packet_keys,stem,index,upper,right,F(h),
                                                 radial,cols,[base,*pieces])
                results['boundaries'].append(result)
                bracket_packages.extend(dependencies)
        if not a.fields_only:
            results['brackets'].append(bracket(cache,a,packet_keys,index,upper,bracket_packages))
    if a.output and not a.fields_only:
        save(a.output,results)


if __name__ == '__main__':
    main()
