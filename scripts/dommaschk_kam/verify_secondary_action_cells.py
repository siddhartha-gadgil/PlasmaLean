"""Prove lower action cells on both original Q0R478 physical tubes with one worker."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, floor, isqrt
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_action_pilot import PanelPolynomial, sqrt_nonnegative
from bounce_launch_box import Box, S
from bounce_mirror_pilot import HEIGHTS
from emit_sparse_taylor_slab import model_literal
from screen_secondary_action_archive import ARCHIVE, COUNT, archive
from verify_backward_physical_prefix import compile_modules, union
import verify_native_action_columns as native_ticks
import verify_native_action_models as native
from verify_paired_action_profiles import native_provider
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import load


TICKS = 'SecondaryLowerTickCache'
PHYSICAL = 'SecondaryLowerCellCache'


@lru_cache(maxsize=1)
def inputs():
    return load(478)


def ticks_source(i):
    traces=inputs()[2]
    outgoing=max(t['steps'][i]['physical_radius_out'] for t in traces)
    values=native_ticks.physical_models(traces[1],i,outgoing)
    polys=list(map(PanelPolynomial,values))
    index=COUNT+i
    block,_=archive()[index]
    group,offset=divmod(index,16)
    name=f'DommaschkLowerTicksQ0R478{i:03}'
    parts=[]
    inputs_name=name+'Data'
    src=native_ticks.header(name,['PlasmaLean.Design.DommaschkNativeActionColumns',
                                 'PlasmaLean.Design.DommaschkActionQ0R478'])
    src+='def models : Five Model := ⟨'+',\n  '.join(map(model_literal,values))+'⟩\n'
    src+=f'''abbrev height : ℚ := {HEIGHTS[1]}
def archive := DommaschkActionQ0R478.slabGroup{group}[{offset}].packed
def record (n : ℕ) := archive >>> (72*n)
'''
    for field,poly in zip(native_ticks.FIELDS,polys,strict=True):
        coeffs=', '.join(map(native_ticks.box_literal,poly.coefficients))
        src+=f'''theorem coef_{field} : models.{field}.poly.map rational = [{coeffs}] := by with_unfolding_all rfl
theorem err_{field} : (rational models.{field}.radius).hi = {poly.remainder.hi} := by with_unfolding_all rfl
'''
    end='\nend PlasmaLean.Design.'+name+'\n'
    parts.append((inputs_name,src+end,[]))
    leaves=[]
    for start in range(0,48,8):
        child=name+f'Part{start//8}'
        leaves.append(child)
        src=native_ticks.header(name,[TICKS+'.'+inputs_name])
        for j in range(start,start+8):
            t=Box(floor((F(j,24)-1)*S),ceil((F(j+1,24)-1)*S))
            b=[m.on(t) for m in polys]
            d,r8,r16,u,num=b
            root=sqrt_nonnegative(u)
            density=root/d
            sq=Box(2*S,2*S)*(Box(max(0,num.lo),max(0,num.hi))/(r16*(Box.rational(HEIGHTS[1])+root/r8)))
            density_tick=floor(F(density.lo*2**20,S))
            sq_tick=floor(F(sq.lo*2**26,S))
            word=block>>(72*j)
            actual=[(word>>(24*k))%(2**24) for k in range(3)]
            if actual!=[density_tick,sq_tick,isqrt(sq_tick*16384)]:
                raise ValueError(f'lower square root or directed tick differs at {i}/{j}')
            src+=f'''
theorem panel{j} : ∃ root, Checked false (models.map (fun m => onPanel m (timeBox {j})))
    root height (record {j}) := by
  let boxes : Five Box := ⟨{', '.join(map(native_ticks.box_literal,b))}⟩
  have clock : timeBox {j} = {native_ticks.box_literal(t)} := by with_unfolding_all rfl
'''
            src+=''.join(native_ticks.panel_equality(f,poly,t,j) for f,poly in zip(native_ticks.FIELDS,polys,strict=True))
            src+=f'''  have horner : models.map (fun m => onPanel m (timeBox {j})) = boxes := by
    simp only [Five.map, boxes, {', '.join('bound_'+f for f in native_ticks.FIELDS)}]
  rw [horner]
  refine ⟨{native_ticks.box_literal(root)}, ?_⟩
  constructor
  · constructor <;> first
    | (intro _; rw [← Int.blt'_eq_true]; with_unfolding_all rfl)
    | (rw [← Int.blt'_eq_true]; with_unfolding_all rfl)
    | (rw [← Int.ble'_eq_true]; with_unfolding_all rfl)
  all_goals first | (rw [← Int.blt'_eq_true]; with_unfolding_all rfl) | with_unfolding_all rfl
'''
        parts.append((child,src+end,[]))
    src=native_ticks.header(name,[TICKS+'.'+x for x in leaves])
    src+='''theorem checked (j : Fin 48) : ∃ root,
    Checked false (models.map (fun m => onPanel m (timeBox j))) root height (record j) := by
  fin_cases j
'''+''.join(f'  · exact panel{j}\n' for j in range(48))
    parts.append((name,src+end,['checked']))
    return parts


def physical_source(i,model,tick):
    name=f'DommaschkLowerCellsQ0R478{i:03}'
    src=native_ticks.header(name,[TICKS+'.'+tick,native.OUTPUT_PACKAGE+'.'+model,
                                'PlasmaLean.Design.DommaschkSecondaryActionMass'])
    src+='open Certificates.PositionFrameSlabs DommaschkPhysicalActionPanel DommaschkMirrorTubeCrossing\n'
    bg,bo=divmod(COUNT-1-i,16)
    src+=f'''abbrev height := {tick}.height
abbrev forwardArchive := {tick}.archive
def backwardArchive := DommaschkActionQ0R478.slabGroup{bg}[{bo}].packed
def backwardRecord (j : ℕ) := backwardArchive >>> (72*(47-j))
theorem mirrored (j : Fin 48) : SameDigits ({tick}.record j) (backwardRecord j) := by
  fin_cases j <;> constructor <;> with_unfolding_all rfl
'''
    thms=['mirrored']
    for back in [False,True]:
        tag='backward' if back else 'forward'
        phase='(-q)' if back else 'q'
        row='backRow' if back else 'row'
        point='backward_physical' if back else 'physical'
        record='backwardRecord' if back else tick+'.record'
        index=COUNT-1-i if back else COUNT+i
        time=f'(-({i+1}:ℝ)/64)' if back else f'({i}/64:ℝ)'
        orient='true' if back else 'false'
        cert='(cert.of_sameDigits (mirrored j))' if back else 'cert'
        thms.extend([tag+'_point',tag+'_cells'])
        src+=f'''abbrev {tag}Row := {model}.{row}
abbrev {tag}Block := DommaschkActionQ0R478.slabs[{index}]'(by rw [DommaschkActionQ0R478.checked.len]; norm_num)
theorem {tag}_archive : {tag}Block.packed = {tag}Archive := by with_unfolding_all rfl
theorem {tag}_point {{prev : State}} {{q : ℝ}} {{x : Plane}} (j : Fin 48)
    (hq : q ∈ Icc ({i}/64:ℝ) ({i+1}/64)) (hx : x ∈ (physicalSlab prev {tag}Row ({i}/64)).tube q)
    (hs : 128*q-{2*i+1} ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1)) :
    (density ({record} j):ℝ)/1048576 ≤ arcDensity (x 0) {phase} (x 1) ∧
    (speedSq ({record} j):ℝ)/67108864 ≤ max (2*((height:ℝ)-strength {phase} x)) 0 := by
  obtain ⟨hr,hd,h8,h16,hu,hn⟩ := {model}.{point} hq hx
  rw [← DommaschkNativeActionGeometry.squared_numerator hr {phase}] at hu
  have mem : Five.Rel (fun m z => m.Mem (128*q-{2*i+1}) z) {tick}.models
      (quantities (x 0) {phase} (x 1) height) := by
    with_unfolding_all exact ⟨hd,h8,h16,hu,hn⟩
  obtain ⟨_,cert⟩ := {tick}.checked j
  exact physical hr (by norm_num [height,{tick}.height]) {cert} (five_mem (time_mem hs) mem)

theorem {tag}_cells {{prev : State}} {{y : ℝ → Plane}}
    (tube : ∀ q ∈ Icc ({i}/64:ℝ) ({i+1}/64), y {phase} ∈ (physicalSlab prev {tag}Row ({i}/64)).tube q) :
    Cells false (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
      height {time} 48 {tag}Block.packed := by
  rw [{tag}_archive]
  have out := @NativeActionInterval.lower_cells (fun t => arcDensity (y t 0) t (y t 1))
    (fun t => strength t (y t)) (height:ℝ) {orient} {i} {tag}Archive (by
      intro j q hq hs
      have hd : q ∈ Icc ({i}/64:ℝ) ({i+1}/64) := by convert hq using 1; norm_num
      have ss : 128*q-{2*i+1} ∈ Icc (2*(j:ℝ)/48-1) (2*((j:ℝ)+1)/48-1) := by
        convert hs using 1; norm_num
      exact {tag}_point j hd (tube q hd) ss)
  convert out using 1; norm_num
'''
    return name,src+'\nend PlasmaLean.Design.'+name+'\n',thms


def verify(i,args,static,data):
    name=f'DommaschkLowerTicksQ0R478{i:03}'
    fields,_,_,checksum=native_provider(args,i,478,data,static)
    ticks=compile_modules(args.lower_cache/name,ticks_source(i),[],
        [args.version,checksum,digest(ARCHIVE),digest(DESIGN/'DommaschkNativeActionColumns.trace')],args,TICKS)
    print(name,ticks[1]['key'],flush=True)
    deps=[*static,*fields,ticks]
    item=physical_source(i,fields[-1][1]['module'],name)
    overlay=union(args.lower_cache,deps)
    key=[args.version,checksum,digest(DESIGN/'DommaschkSecondaryActionMass.trace'),[m['key'] for _,m in deps]]
    base,marker=compile_modules(args.lower_cache/item[0],[item],[overlay],key,args,PHYSICAL)
    report={k:v for k,v in marker.items() if k!='artifacts'}
    report.update(index=i,archive_indices=[COUNT-1-i,COUNT+i],panels=96,endpoint='q0r478',
                  packet_sha256=checksum,archive_sha256=digest(ARCHIVE),quadrature='lower',
                  parent_model=fields[-1][1]['key'],ticks=ticks[1]['key'],import_paths=[str(base),str(overlay)])
    save(args.lower_cache/'rows'/f'{i:03}.json',report)
    print(item[0],marker['key'],flush=True)
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--rows',nargs='+',type=int)
    group.add_argument('--range',nargs=2,type=int,metavar=('FIRST','LAST'))
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-action-profiles')
    parser.add_argument('--model-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    parser.add_argument('--lower-cache',type=Path,default=ROOT/'.lake/secondary-lower-action')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    rows=args.rows if args.rows is not None else list(range(args.range[0],args.range[1]+1))
    if not rows or len(set(rows))!=len(rows) or any(not 0<=i<COUNT for i in rows):
        parser.error('choose distinct outward row indices from 0 to 326')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path=lake('printenv','LEAN_PATH')
    args.version=lake('lean','--version')
    data=native.static_data()
    (args.lower_cache/'rows').mkdir(parents=True,exist_ok=True)
    static=native.verify_static(SimpleNamespace(**{**vars(args),'cache':args.model_cache,'fields':range(4)}),data)
    reports=[]
    for i in rows:
        reports.append(verify(i,args,static,data))
        save(args.output,dict(requested=rows,completed=[r['index'] for r in reports],
                             cells=96*len(reports),endpoint='q0r478',rows=reports))


if __name__=='__main__':
    main()
