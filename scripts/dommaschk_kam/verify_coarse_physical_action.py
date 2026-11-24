"""Verify independent signed action cells directly against a complete coarse endpoint packet."""
import argparse
from fractions import Fraction as F
import json
from math import ceil, floor, isqrt
from pathlib import Path

from bounce_action_pilot import PanelPolynomial, sqrt_nonnegative
from bounce_common_section import section_polynomial_data
from bounce_launch_box import Box, S
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import panel_row, slab_witness
from emit_sparse_taylor_slab import model_literal
from replay_physical_action_archive import segment
from screen_action_panel_resolution import endpoint_inputs
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env, section_data, verify
from verify_mirror_physical_hit import admitted
import verify_native_action_columns as ticks
import verify_native_action_models as native
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


PACKAGE='CoarsePhysicalActionCache'
TICKS='CoarsePhysicalTickCache'


def tick_modules(atom,models,h,upper,m,word,back):
    tag=str(upper).lower()
    polys=[PanelPolynomial(model) for model in models]
    hname=atom+'Data'
    src=ticks.header(atom,['PlasmaLean.Design.DommaschkNativeActionColumns','PlasmaLean.Certificates.CoarseActionCells'])
    src+='def models : Five Model := ⟨'+',\n  '.join(map(model_literal,models))+'⟩\n'
    src+=f'abbrev height : ℚ := {h}\ndef packed : ℕ := {word}\n'
    pos=f'({m-1}-k)' if back else 'k'
    src+=f'def record (k : ℕ) := packed >>> (72*{pos})\n'
    for key,poly in zip(ticks.FIELDS,polys,strict=True):
        coeff=', '.join(map(ticks.box_literal,poly.coefficients))
        src+=f'''theorem coef_{key} : models.{key}.poly.map rational = [{coeff}] := by with_unfolding_all rfl
theorem err_{key} : (rational models.{key}.radius).hi = {poly.remainder.hi} := by with_unfolding_all rfl
'''
    end='\nend PlasmaLean.Design.'+atom+'\n'
    parts=[(hname,src+end,[])]
    leafs=[]
    for first in range(0,m,6):
        name=atom+f'Part{first//6}'
        leafs.append(name)
        src=ticks.header(atom,[TICKS+'.'+hname])
        for k in range(first,min(first+6,m)):
            t=Box(floor((F(2*k,m)-1)*S),ceil((F(2*(k+1),m)-1)*S))
            boxes=[p.on(t) for p in polys]
            d,r8,r16,u,num=boxes
            root=sqrt_nonnegative(u)
            density=root/d
            sq=Box(2*S,2*S)*(Box(max(0,num.lo),max(0,num.hi))/(r16*(Box.rational(h)+root/r8)))
            rounded=(lambda b,n:ceil(F(b.hi*n,S))) if upper else (lambda b,n:floor(F(b.lo*n,S)))
            dt,gt=rounded(density,2**20),rounded(sq,2**26)
            st=isqrt(gt*2**14)
            st+=int(upper and st*st<gt*2**14)
            stored=word>>(72*(m-1-k if back else k))
            if [(stored>>(24*j))%(2**24) for j in range(3)]!=[dt,gt,st]:
                raise ValueError(f'independent exact Horner models differ from the signed coarse word at {atom}/{k}')
            src+=f'''theorem panel{k} : ∃ root, Checked {tag} (models.map (fun p => onPanel p (coarseTime {m} {k})))
    root height (record {k}) := by
  let boxes : Five Box := ⟨{', '.join(map(ticks.box_literal,boxes))}⟩
  have clock : coarseTime {m} {k} = {ticks.box_literal(t)} := by with_unfolding_all rfl
'''
            for field,poly in zip(ticks.FIELDS,polys,strict=True):
                term=ticks.panel_equality(field,poly,t,k).replace(f'(timeBox {k})',f'(coarseTime {m} {k})')
                src+=term
            src+=f'''  have run : models.map (fun p => onPanel p (coarseTime {m} {k})) = boxes := by
    simp only [Five.map,boxes,{', '.join('bound_'+f for f in ticks.FIELDS)}]
  rw [run]
  refine ⟨{ticks.box_literal(root)},?_⟩
  constructor
  · constructor <;> first
    | (intro _; rw [← Int.blt'_eq_true]; with_unfolding_all rfl)
    | (rw [← Int.blt'_eq_true]; with_unfolding_all rfl)
    | (rw [← Int.ble'_eq_true]; with_unfolding_all rfl)
  all_goals first | (rw [← Int.blt'_eq_true]; with_unfolding_all rfl) | with_unfolding_all rfl
'''
        parts.append((name,src+end,[]))
    src=ticks.header(atom,[TICKS+'.'+name for name in leafs])
    src+=f'''theorem checked (k : Fin {m}) : ∃ root,
    Checked {tag} (models.map (fun p => onPanel p (coarseTime {m} k))) root height (record k) := by
  fin_cases k
'''+''.join(f'  · exact panel{k}\n' for k in range(m))
    return [*parts,(atom,src+end,['checked'])]


def cell(label,i,sign,pack,model,atom,word,mass):
    back=sign<0
    m=pack['splits']
    copies=48//m
    j=pack['counts'][0]-1-i if back else pack['counts'][0]+i
    upper=str(pack['upper']).lower()
    negative=str(back).lower()
    phase='(Real.pi/2)' if label[1]=='1' else '0'
    hname=f'DommaschkCoarsePhysical{label.upper()}{"Back" if back else "Fwd"}{i:03}N{m}'
    src=ticks.header(hname,[TICKS+'.'+atom,native.OUTPUT_PACKAGE+'.'+model,pack['package']+'.'+pack['module']])
    src+='open Certificates.PositionFrameSlabs DommaschkPhysicalActionPanel DommaschkMirrorTubeCrossing\n'
    group,off=divmod(j,16)
    clk='(-t)' if back else 't'
    idx='(47-(j:ℕ))' if back else '(j:ℕ)'
    time=f'(-({i+1}:ℝ)/64)' if back else f'({i}/64:ℝ)'
    src+=f'''abbrev row := {model}.row
abbrev phase : ℝ := {phase}
abbrev height := {atom}.height
abbrev block := {pack['module']}.slabs[{j}]'(by rw [{pack['module']}.checked.len]; norm_num)
def archive : ℕ := {word}
theorem original : block.packed = archive := by with_unfolding_all rfl
theorem encoded_mass : block.mass = {mass} := by with_unfolding_all rfl
theorem copies_match (j : Fin 48) :
    SameDigits ({atom}.record ((j:ℕ)/{copies})) (archive >>> (72*{idx})) := by
  fin_cases j <;> constructor <;> with_unfolding_all rfl

theorem point {{prev : State}} {{t : ℝ}} {{x : Plane}} (j : Fin 48)
    (ht : t ∈ Icc ({i}/64:ℝ) ({i+1}/64)) (hx : x ∈ (physicalSlab prev row ({i}/64)).tube t)
    (hs : 128*t-{2*i+1} ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1)) :
    Directed {upper} (arcDensity (x 0) (phase+{clk}) (x 1)) (density (archive >>> (72*{idx}))/1048576) ∧
    Directed {upper} (max (2*((height:ℝ)-strength (phase+{clk}) x)) 0) (speedSq (archive >>> (72*{idx}))/67108864) := by
  obtain ⟨r,d,p8,p16,u,num⟩ := {model}.physical ht hx
  have d8 := DommaschkNativeActionGeometry.squared_numerator r (phase+{clk})
  have mem : Five.Rel (fun m z => m.Mem (128*t-{2*i+1}) z) {atom}.models
      (quantities (x 0) (phase+{clk}) (x 1) height) := by
    rw [← d8] at u
    with_unfolding_all exact ⟨d,p8,p16,u,num⟩
  let k : Fin {m} := ⟨(j:ℕ)/{copies},by omega⟩
  obtain ⟨_,cert⟩ := {atom}.checked k
  have inside := coarse_time_mem (m := {m}) (copies := {copies}) (k := (j:ℕ)/{copies}) (j := j)
    (by norm_num) (by omega) (by omega) hs
  exact physical r (by norm_num [height,{atom}.height]) (cert.of_sameDigits (copies_match j)) (five_mem inside mem)

theorem cells {{prev : State}} {{y : ℝ → Plane}}
    (tube : ∀ t ∈ Icc ({i}/64:ℝ) ({i+1}/64), y {clk} ∈ (physicalSlab prev row ({i}/64)).tube t) :
    Cells {upper} (fun t => arcDensity (y t 0) (phase+t) (y t 1)) (fun t => strength (phase+t) (y t))
      height {time} 48 block.packed := by
  rw [original]
  have out := @directed_cells (fun t => arcDensity (y t 0) (phase+t) (y t 1))
    (fun t => strength (phase+t) (y t)) (height:ℝ) {upper} {negative} {i} archive (by
      intro j t ht hs
      have h : t ∈ Icc ({i}/64:ℝ) ({i+1}/64) := by convert ht using 1; norm_num
      have s : 128*t-{2*i+1} ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1) := by
        convert hs using 1; norm_num
      exact point j h (tube t h) s)
  convert out using 1; norm_num
'''
    if label[1]=='0':
        src=src.replace('    rw [← d8] at u','    simp only [phase,zero_add] at d8 ⊢\n    rw [← d8] at u')
    return hname,src+f'\nend PlasmaLean.Design.{hname}\n',['point','cells']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',type=Path,required=True)
    p.add_argument('--row',type=int,default=0)
    p.add_argument('--directions',type=int,nargs='+',choices=(-1,1),default=[1,-1])
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-action-models')
    p.add_argument('--native-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--cell-cache',type=Path,default=ROOT/'.lake/coarse-physical-action')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    env(a)
    pack=json.loads(a.packet.read_text())
    label=pack['endpoint']
    upper,h,counts,_,trs,packet,arc=endpoint_inputs(label)
    m=pack['splits']
    if (pack['package']!='CoarseActionPacketCache' or pack['module']!=f'DommaschkCoarseAction{label.upper()}N{m}'
            or pack['packet_sha256']!=packet or pack['action_sha256']!=arc or pack['height']!=str(h)
            or pack['upper']!=upper or pack['counts']!=counts or m not in (12,16)):
        p.error('expected the coarse packet for the same complete endpoint and height')
    base=Path(pack['import_paths'][0])
    admitted(base,pack['module'],pack['key'])
    section=int(label[1])
    data,static=section_data(a,section)
    exact=section_polynomial_data(section)
    gap=ShiftedStrength(exact)
    reports=[]
    for sign in a.directions:
        model,nums=verify(a,label,a.row,sign,data,static)
        word,mass=panel_row(segment(trs[int(sign==1)],a.row),exact,gap,h,upper,m)
        original=slab_witness(word,mass,upper,m)
        flat=int(original.split('0x',1)[1].split(',',1)[0],16)
        atom=model['module'].replace('CoarseModel','CoarseTicks')+f'N{m}'
        inputs=[a.version,packet,pack['key'],digest(DESIGN.parent/'Certificates/CoarseActionCells.trace')]
        tb,tr=compile_modules(a.cell_cache/atom,tick_modules(atom,nums,h,upper,m,word,sign<0),[],inputs,a,TICKS)
        roots=[base,tb,*map(Path,model['import_paths'])]
        keys=[*inputs,model['key'],tr['key']]
        overlay=merge_import_roots(a.cell_cache,roots,keys)
        decl=cell(label,a.row,sign,pack,model['module'],atom,flat,mass)
        leaf,accepted=compile_modules(a.cell_cache/decl[0],[decl],[overlay],keys,a,PACKAGE)
        out={k:accepted[k] for k in ['module','key','theorems','axioms']}
        out.update(endpoint=label,direction=sign,index=a.row,height=str(h),upper=upper,splits=m,
                   packet_sha256=packet,coarse_packet=pack['key'],model=model['key'],ticks=tr['key'],
                   expanded_hex=hex(flat),mass=mass,chronological_block=counts[0]-1-a.row if sign<0 else counts[0]+a.row,
                   import_paths=[str(leaf),str(overlay)])
        reports.append(out)
        save(a.output,reports)
        print(out['module'],out['key'],flush=True)


if __name__=='__main__':
    main()
