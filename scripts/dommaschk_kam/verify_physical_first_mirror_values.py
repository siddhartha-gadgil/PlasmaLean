"""Attach the QA2R first-mirror area formula directly to signed physical position tubes."""
import argparse
import json
from pathlib import Path

from emit_position_slabs import step
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_common_endpoint_traces import ENDPOINTS
from verify_grouped_mirror_exclusion import FINAL as ORDERED
from verify_mirror_physical_hit import admitted
from verify_opposite_mirror_caps import HITS as OPPOSITE, LABELS, bracket_nodes, cap_module
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import HITS as ZERO, load
from verify_signed_mirror_passage import merge_import_roots


THEORY = 'DommaschkPhysicalFirstMirrorValues'
BOXES = 'PhysicalFirstMirrorClockCache'
CAPS = 'PhysicalFirstMirrorRowsCache'
SIGNS = 'PhysicalFirstMirrorSignCache'


def source_start(name, imports):
    return ('module\n' + ''.join(f'public import {x}\n' for x in imports) +
            f'\n@[expose] public section\nnoncomputable section\nnamespace PlasmaLean.Design.{name}\n'
            'open Set Certificates.PositionFrameSlabs DommaschkPhysicalFirstMirrorValues DommaschkMirrorLaunch\n'
            'open DommaschkEndpointTraceFamily DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign\n'
            'set_option maxRecDepth 65536\nset_option maxHeartbeats 4500000\nset_option linter.style.longLine false\n')


def row_source(label, back, rows, k, n, crossings):
    side = 'Back' if back else 'Fwd'
    tag = side.lower()
    stem = 'DommaschkArea'+label.upper()+side
    opposite = label in LABELS
    cap = cap_module(label, -1 if back else 1, 1, n, True) if opposite else (
        f'Dommaschk{label.upper()}MirrorUpper{n-1:03}Right')
    section = 'Real.pi / 2' if opposite else '0'
    src = source_start(stem, ['PlasmaLean.Design.'+THEORY,(OPPOSITE if opposite else ZERO)+'.'+crossings])
    src += 'def rows : List Step := [\n' + ',\n'.join(step(r) for r in rows[:n]) + ']\n'
    caprow = cap + ('.row' if opposite else '.'+tag+'Row')
    cap_theorem = cap + ('.on_tube' if opposite else '.'+tag+'_tube_sign')
    high_proof = (f'exact {cap_theorem} atCap' if opposite else
                  'simpa only [clock,Bool.false_eq_true,↓reduceIte,zero_add,DommaschkMirrorEndpointSign.oriented]\n'
                  f'    using {cap_theorem} atCap')
    src += f'''
theorem packed : rows.all DommaschkSignedTraceDomain.packed = true := by with_unfolding_all rfl
theorem last_high (prev : State) {{x : Plane}}
    (hx : x ∈ (physicalSlab prev rows[{n-1}] ({n-1}/64)).tube ({n}/64)) :
    (height true : ℝ) < strength (({section}) + clock {str(back).lower()} ({n}/64)) x := by
  have atCap : x ∈ (physicalSlab prev {caprow} ({n-1}/64)).tube ({n}/64) := by
    with_unfolding_all exact hx
  {high_proof}

theorem side (tail : List Step)
    (low : OnTubes (fun t x => strength (({section}) + clock {str(back).lower()} t) x < height false)
      (MirrorEndpoint.start .{label}) 0 (rows.take {k})) :
    Side (azimuth (MirrorEndpoint.opposite .{label})) (MirrorEndpoint.start .{label})
      {str(back).lower()} {k} {n-1} (rows ++ tail) := by
  refine ⟨by norm_num,by norm_num,?_,by norm_num,?_,?_,?_⟩
  · rw [List.length_append]
    change {n-1} < {n} + tail.length
    omega
  · with_unfolding_all exact packed
  · with_unfolding_all exact low
  · intro prev x hx
    have clockEnd : ((({n-1} : ℕ):ℝ)+1)/64 = {n}/64 := by norm_num
    rw [clockEnd] at hx ⊢
    exact last_high prev (by with_unfolding_all exact hx)
end PlasmaLean.Design.{stem}
'''
    return stem,src,['packed','last_high','side']


def sign_source(label, side_names, early, counts):
    stem = 'DommaschkArea'+label.upper()+'Sides'
    src = source_start(stem, [BOXES+'.'+m for m in side_names]+[ORDERED+'.'+early])
    for back,(mod,(k,n)) in enumerate(zip(side_names,counts,strict=True)):
        simplify = 'simp only [zero_add,clock,↓reduceIte]' if back else 'simp only [zero_add,clock,Bool.false_eq_true,↓reduceIte]'
        side = 'back' if back else 'fwd'
        src += f'''
theorem {side} (tail : List Step) : Side (azimuth (MirrorEndpoint.opposite .{label}))
    (MirrorEndpoint.start .{label}) {str(bool(back)).lower()} {k} {n-1} ({mod}.rows ++ tail) := by
  apply {mod}.side
  {simplify if label not in LABELS else ''}
  with_unfolding_all exact {early}.{side}_below (MirrorEndpoint.start .{label})
'''
    return stem,src+f'end PlasmaLean.Design.{stem}\n',['fwd','back']


def passage_source(label, clocks, counts, signed):
    name = 'DommaschkArea'+label.upper()+('Certified' if signed else 'AtCaps')
    signmod = 'DommaschkArea'+label.upper()+'Sides'
    imports = [SIGNS+'.'+signmod] if signed else [BOXES+'.'+m for m in clocks]
    src = source_start(name,imports)
    (fk,fn),(bk,bn) = counts
    src += f'''
theorem from_original_passage {{c : Checkpoint}} {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}}
    {{F B : List Step}} (path : c.Passage .{label} uC zC uA zA φ)
    (angle : |φ-azimuth (MirrorEndpoint.opposite .{label})| ≤ 1/64)
    (fl : c.forwardRows.length = c.length) (bl : c.backwardRows.length = c.length)
    (f : c.forwardRows = {clocks[0]}.rows ++ F)
    (b : c.backwardRows = {clocks[1]}.rows ++ B)'''
    if not signed:
        section = 'Real.pi/2' if label in LABELS else '0'
        for back,(m,(k,_)) in enumerate(zip(clocks,counts,strict=True)):
            src += f'''
    (low{back} : OnTubes (fun t x => strength (({section}) + clock {str(bool(back)).lower()} t) x < height false)
      (MirrorEndpoint.start .{label}) 0 ({m}.rows.take {k}))'''
    src += f''' :
    FromLaunch .{label} c {fk} {fn-1} {bk} {bn-1} uC zC uA zA φ := by
  apply from_passage path _ _ fl bl angle
  · rw [f]
    exact {signmod+'.fwd F' if signed else clocks[0]+'.side F low0'}
  · rw [b]
    exact {signmod+'.back B' if signed else clocks[1]+'.side B low1'}
end PlasmaLean.Design.{name}
'''
    return name,src,['from_original_passage']


def physical_source(label,counts,cal_counts):
    suffix = '_'.join(str(cal_counts[e]) for e in ENDPOINTS)
    cal,fam = 'DommaschkCalibratedFamily'+suffix,'DommaschkCommonEndpointTraces'+suffix
    binding = 'DommaschkArea'+label.upper()+'Certified'
    name = 'DommaschkFirstMirrorArea'+label.upper()+'On'+suffix
    (fk,fn),(bk,bn) = counts
    src = source_start(name,['CalibratedFamilyCache.'+cal,'FirstMirrorAreaPassageCache.'+binding])
    src += f'''open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open {fam} (checkpoint)
theorem from_common_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ-azimuth (MirrorEndpoint.opposite .{label})| ≤ MirrorEndpoint.width .{label} →
        FromLaunch .{label} (checkpoint .{label}) {fk} {fn-1} {bk} {bn-1} uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,_⟩ := {cal}.same_embedded_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  apply {binding}.from_original_passage (F := (checkpoint .{label}).forwardRows.drop {fn})
    (B := (checkpoint .{label}).backwardRows.drop {bn}) (each .{label} φ small)
    (small.trans (by norm_num [MirrorEndpoint.width,MirrorEndpoint.opposite]))
    ({fam}.row_counts _).1 ({fam}.row_counts _).2 <;> with_unfolding_all rfl
end PlasmaLean.Design.{name}
'''
    return name,src,['from_common_tori']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',required=True,choices=('q0r478',*LABELS))
    p.add_argument('--caps',type=Path,required=True)
    p.add_argument('--incoming',type=Path,help='full unshifted ordered incoming sign archive')
    p.add_argument('--calibrated',type=Path,help='ground the two first-mirror families at a physical original birth')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/physical-first-mirror-values')
    a = p.parse_args()
    e=a.endpoint
    caps=json.loads(a.caps.read_text())
    if e in LABELS:
        tables=list(bracket_nodes(e))
        packet=tables[0][1]
        traces=[next(row[0] for row in tables if row[2]==sign) for sign in (1,-1)]
        coords=[(next(t[4] for t in tables if t[2:4]==(sign,0)),
                 next(t[5] for t in tables if t[2:4]==(sign,1))) for sign in (1,-1)]
        expected='DommaschkOppositeMirrorCrossings'+e.upper()
    else:
        _,path,rows,bounds=load(478)
        packet=digest(path)
        traces=rows[::-1]
        coords=[(bounds[0][0],bounds[1][1])]*2
        expected='DommaschkQ0R478MirrorCrossings'
    if (caps['module']!=expected or caps['packet_sha256' if e in LABELS else 'record_sha256']!=packet or caps['endpoint'].lower()!=e
            or any(not 0 < k < n <= k+10 for k,n in coords)):
        p.error('wrong cap source, packet or ten-slab bracket')
    env(a)
    origin=list(map(Path,caps['import_paths']))
    admitted(origin[0],caps['module'],caps['key'])
    keys=[a.version,digest(DESIGN/(THEORY+'.trace')),packet,caps['key']]
    a.cache=a.cache.resolve()

    def check(item,paths,parents,package):
        root,mark=compile_modules(a.cache/item[0],[item],paths,parents,a,package)
        data={k:v for k,v in mark.items() if k!='artifacts'}
        data['import_paths']=list(map(str,[root,*paths]))
        return data

    checked=[]
    for back,(tr,(k,n)) in enumerate(zip(traces,coords,strict=True)):
        if tr['direction'] != (1,-1)[back] or [r['index'] for r in tr['steps'][:n]] != list(range(n)):
            p.error('signed position tubes are incomplete or in the wrong order')
        item=row_source(e,bool(back),tr['steps'],k,n,caps['module'])
        checked.append(check(item,origin,keys,BOXES))
    clocks=[r['module'] for r in checked]
    parents=keys+[r['key'] for r in checked]
    paths=[Path(s) for r in checked for s in r['import_paths']]
    result={'endpoint':e,'packet_sha256':packet,'brackets':coords,'clocks':checked,'original_birth':False}
    signed=a.incoming is not None
    if signed:
        data=json.loads(a.incoming.read_text())
        incoming=data['ordered'][e] if e in LABELS else data
        early='Dommaschk'+('Opposite' if e in LABELS else '')+e.upper()+f'SubmirrorPrefix{coords[0][0]:03}'
        if incoming['module']!=early or not coords[0][0]==coords[1][0]:
            p.error('incoming certificate does not reach both low bracket entrances')
        extra=list(map(Path,incoming['import_paths']))
        admitted(extra[0],early,incoming['key'])
        parents.append(incoming['key'])
        overlay=merge_import_roots(a.cache/'signs',paths+extra,parents)
        out=check(sign_source(e,clocks,early,coords),[overlay],parents,SIGNS)
        result['ordered']=out
        parents.append(out['key'])
        paths=list(map(Path,out['import_paths']))
    overlay=merge_import_roots(a.cache/'passage',paths,parents)
    link=check(passage_source(e,clocks,coords,signed),[overlay],parents,'FirstMirrorAreaPassageCache')
    result['passage']=link
    if a.calibrated:
        cal=json.loads(a.calibrated.read_text())
        ns=cal['lengths_each_direction']
        if (not signed or cal['module'] != 'DommaschkCalibratedFamily'+'_'.join(str(ns[x]) for x in ENDPOINTS)
                or ns[e]<max(n for k,n in coords)):
            p.error('requires the complete incoming signs and a signed physical trajectory through both high caps')
        cs=list(map(Path,cal['import_paths']))
        admitted(cs[0],cal['module'],cal['key'])
        parents.extend([cal['key'],link['key']])
        overlay=merge_import_roots(a.cache/'family',[*map(Path,link['import_paths']),*cs],parents)
        final=check(physical_source(e,coords,ns),[overlay],parents,'FirstMirrorAreaFamilyCache')
        result.update(original_birth=True,physical=final,calibrated=cal['key'])
    save(a.output,result)
    print(e,result.get('physical',link)['key'],flush=True)


if __name__=='__main__':
    main()
