"""Attach an ordered signed exclusion archive to the genuine birth-to-section path of equal length."""
import argparse
import json
from pathlib import Path
import subprocess

from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_grouped_mirror_exclusion import FINAL
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'SecondarySubmirrorBirthCache'


def source(label,n,prefix,early,threshold='DommaschkFirstMirrorLaunchSign.height false'):
    name = f'Dommaschk{label}SubmirrorBirth{n:03}'
    text = f'''module
public import {SIGNED_PACKAGE}.{prefix}
public import {FINAL}.{early}
public import PlasmaLean.Design.DommaschkEndpointMirrorBranch

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkEndpointMirrorBranch DommaschkEndpointSignedTrace
open DommaschkMirrorTubeCrossing DommaschkMirrorLaunch DommaschkBounceField DommaschkKamC KamNewton
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set {prefix}
set_option maxRecDepth 32768
set_option linter.style.longLine false

/-- The physical approach from the interpolated birth and both halves of one submirror field line. -/
def BelowFromBirth (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  let duration := |φ - azimuth endpoint.opposite|
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * duration = azimuth endpoint.opposite ∧
    a 0 = birth uC zC uA zA endpoint.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    y 0 = coordinates.symm (a duration) ∧
    Outward endpoint.start forwardRows 1 ({n}/64) y ∧
    Outward endpoint.start backwardRows (-1) ({n}/64) (fun t => y (-t)) ∧
    (∀ t ∈ Icc (-({n}:ℝ)/64) ({n}/64), strength t (y t) < {threshold})

theorem from_entry_below {{uC zC uA zA : FA}} {{φ : ℝ}} (entry : SectionEntry endpoint uC zC uA zA φ) :
    BelowFromBirth uC zC uA zA φ := by
  obtain ⟨s,a,hs,hφ,src,ode,joined⟩ := {prefix}.from_entry entry
  obtain ⟨y,hy,f,b⟩ := of_joined (show Joined 0 ({n}/64) _ _ _
    (physicalSlabs endpoint.start 0 forwardRows) (physicalSlabs endpoint.start 0 backwardRows)
    from joined)
  refine ⟨s,a,y,hs,hφ,src,ode,hy,f,b,?_⟩
'''
    for name0,d,clock,paths in [('forward','fwd','t','f'),('backward','back','(-t)','b')]:
        rows = name0+'Rows'
        text += f'''  have {d}Cert : OnTubes (fun t x => strength {clock} x < {threshold})
      endpoint.start 0 {rows} := by with_unfolding_all exact {early}.{d}_below endpoint.start
  have {d}All := {d}Cert.on_nonempty_prefix (post := []) (y := {('y' if d=='fwd' else 'fun t => y (-t)')})
    (by intro h; have size := congrArg List.length h; change {n} = 0 at size; omega)
    (by simpa only [List.append_nil] using {paths}.contained)
  have {d}Bound : ∀ t ∈ Icc 0 ({n}/64:ℝ), strength {clock} (y {clock}) < {threshold} := by
    simpa only [show {rows}.length = {n} by rfl, Nat.cast_ofNat,zero_add] using {d}All
'''
    text += '''
  intro t ht
  by_cases pos : 0 ≤ t
  · exact fwdBound t ⟨pos,ht.2⟩
  · simpa only [neg_neg] using backBound (-t) ⟨by linarith,by linarith [ht.1]⟩

theorem from_birth :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → BelowFromBirth uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry_below (entry endpoint φ h)⟩
'''
    return name,text+f'\nend PlasmaLean.Design.{name}\n',['from_entry_below','from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--launch',type=int,default=478)
    p.add_argument('--signed',type=Path,required=True)
    p.add_argument('--exclusion',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-submirror-birth')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    label,path,_,_ = load(args.launch)
    checksum = digest(path)
    signed,exclusion = [json.loads(f.read_text()) for f in (args.signed,args.exclusion)]
    n = signed['length_each_direction']
    prefix = f'DommaschkSignedPrefix{label}{n:03}'
    early = f'Dommaschk{label}SubmirrorPrefix{n:03}'
    roots,keys = [],[]
    for d,m in [(signed,prefix),(exclusion,early)]:
        if d['endpoint'].upper()!=label or d['packet_sha256']!=checksum or d['module']!=m:
            p.error(f'wrong archive for {m}')
        paths = ([Path(d['proof_root']),Path(d['import_path'])] if m==prefix
                 else list(map(Path,d['import_paths'])))
        admitted(paths[0],m,d['key'])
        roots.extend(paths)
        keys.append(d['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    overlay = merge_import_roots(args.cache,roots,keys)
    decl = source(label,n,prefix,early)
    base,r = compile_modules(args.cache/decl[0],[decl],[overlay],
                             [checksum,lake('lean','--version'),keys,digest(DESIGN/'DommaschkEndpointMirrorBranch.trace')],
                             args,PACKAGE)
    result = {k:r[k] for k in ('module','key','theorems','axioms')}
    result.update(endpoint=label,signed_length=n,parents=keys,import_paths=[str(base),str(overlay)])
    save(args.output,result)
    print(decl[0],r['key'])


if __name__ == '__main__':
    main()
