"""Attach chosen original lower-action blocks to one Q0R478 trajectory from a genuine birth."""
import argparse
import json
from pathlib import Path
import subprocess

from screen_secondary_action_archive import ARCHIVE
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, key_of, save
from verify_secondary_action_cells import PHYSICAL
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'SecondaryLowerBirthCache'


def source(n, prefix, rows):
    name = f'DommaschkLowerActionBirthQ0R478{n:03}R' + key_of([r['index'] for r in rows])[:12]
    imports = [f'{SIGNED_PACKAGE}.{prefix}', 'PlasmaLean.Design.DommaschkEndpointMirrorBranch',
               *(f'{PHYSICAL}.{r["module"]}' for r in rows)]
    src = 'module\n' + ''.join(f'public import {m}\n' for m in imports)
    src += f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature
open DommaschkEndpointMirrorBranch DommaschkEndpointSignedTrace DommaschkMirrorLaunch
open DommaschkBounceField DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set {prefix}
set_option maxRecDepth 65536
set_option linter.style.longLine false

def Selected (y : ℝ → Plane) : Prop :=
'''
    bounds = []
    for row in rows:
        i, mod = row['index'], row['module']
        for tag, t, path in [('forward',f'({i}/64:ℝ)','f'),('backward',f'(-({i+1}:ℝ)/64)','b')]:
            bounds.append((i, mod, tag, t, path))
    src += ' ∧\n'.join(
        '  Cells false (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))\n'
        f'    {m}.height {t} 48 {m}.{tag}Block.packed' for _,m,tag,t,_ in bounds)
    src += f'''

def Observed (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  let duration := |φ - azimuth endpoint.opposite|
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * duration = azimuth endpoint.opposite ∧
    a 0 = birth uC zC uA zA endpoint.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    y 0 = coordinates.symm (a duration) ∧ Outward endpoint.start forwardRows 1 ({n}/64) y ∧
    Outward endpoint.start backwardRows (-1) ({n}/64) (fun t => y (-t)) ∧ Selected y

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (entry : SectionEntry endpoint uC zC uA zA φ) :
    Observed uC zC uA zA φ := by
  obtain ⟨s,a,hs,hφ,src,ode,joined⟩ := {prefix}.from_entry entry
  obtain ⟨y,hy,f,b⟩ := of_joined (show Joined 0 ({n}/64) _ _ _
    (physicalSlabs endpoint.start 0 forwardRows) (physicalSlabs endpoint.start 0 backwardRows)
    from joined)
  refine ⟨s,a,y,hs,hφ,src,ode,hy,f,b,?_⟩
  unfold Selected
  refine ⟨{', '.join(f'?goal{k}' for k in range(len(bounds)))}⟩
'''
    for k, (i, m, tag, _, path) in enumerate(bounds):
        src += f'''  case goal{k} =>
    have hi : {i} < {tag}Rows.length := by change {i} < {n}; norm_num
    obtain ⟨previous,tube⟩ := {path}.at_row hi
    have link : {tag}Rows[{i}] = {m}.{tag}Row := by with_unfolding_all rfl
    rw [link] at tube
    apply {m}.{tag}_cells (prev := previous)
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      show ({i}:ℝ)+1={i+1} by norm_num] using tube
'''
    src += '''
theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → Observed uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry (entry endpoint φ h)⟩
'''
    return name,src+f'\nend PlasmaLean.Design.{name}\n',['from_entry','from_nested_tori']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--signed',type=Path,required=True)
    p.add_argument('--rows',type=int,nargs='+',required=True)
    p.add_argument('--lower-cache',type=Path,default=ROOT/'.lake/secondary-lower-action')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-lower-birth')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    checksum=digest(load(478)[1])
    prefix=json.loads(a.signed.read_text())
    n=prefix['length_each_direction']
    pm=f'DommaschkSignedPrefixQ0R478{n:03}'
    if (prefix['module'],prefix['packet_sha256'])!=(pm,checksum):
        p.error('expected a signed prefix of the original Q0R478 trajectory')
    if len(set(a.rows))!=len(a.rows) or any(not 0<=i<min(327,n) for i in a.rows):
        p.error('choose distinct existing quadrature rows inside the signed prefix')
    roots=[Path(prefix['proof_root']),Path(prefix['import_path'])]
    keys=[prefix['key']]
    admitted(roots[0],pm,keys[0])
    rows=[]
    for i in sorted(a.rows):
        row=json.loads((a.lower_cache/'rows'/f'{i:03}.json').read_text())
        m=f'DommaschkLowerCellsQ0R478{i:03}'
        if (row['module'],row['packet_sha256'],row['archive_sha256'])!=(m,checksum,digest(ARCHIVE)):
            p.error(f'incorrect lower-action archive or physical tube at {i}')
        paths=list(map(Path,row['import_paths']))
        admitted(paths[0],m,row['key'])
        roots.extend(paths)
        keys.append(row['key'])
        rows.append(row)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    decl=source(n,pm,rows)
    merged=merge_import_roots(a.cache,roots,keys)
    base,r=compile_modules(a.cache/decl[0],[decl],[merged],
        [checksum,keys,lake('lean','--version'),digest(DESIGN/'DommaschkEndpointMirrorBranch.trace')],a,PACKAGE)
    report={k:v for k,v in r.items() if k!='artifacts'}
    report.update(endpoint='q0r478',indices=sorted(a.rows),cells=96*len(rows),signed_length=n,
                  packet_sha256=checksum,parents=keys,import_paths=[str(base),str(merged)])
    save(a.output,report)
    print(r['module'],r['key'],flush=True)


if __name__=='__main__':
    main()
