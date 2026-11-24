"""Attach an existing phase-zero ordered clearance to a signed physical path of any archive length."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from bounce_mirror_pilot import HEIGHTS
from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_grouped_mirror_exclusion import FINAL
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'SubmirrorPrefixObservationCache'


def declaration(token,drop,signed,archive,physical,covered,observed):
    name = f'Dommaschk{token}Observation{observed:03}On{physical:03}From{covered:03}'
    threshold = 'DommaschkFirstMirrorLaunchSign.height false'
    if drop:
        threshold = f'(↑({threshold} - ({drop})) : ℝ)'
    source = f'''module
public import {SIGNED_PACKAGE}.{signed}
public import {FINAL}.{archive}
public import PlasmaLean.Design.DommaschkSubmirrorPrefixObservation

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointSignedTrace
open DommaschkSubmirrorPrefixObservation DommaschkMirrorTubeCrossing DommaschkKamC KamNewton
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set {signed}
set_option linter.style.longLine false
set_option maxRecDepth 32768

/-- The full signed physical line is kept with both exits, and its observed interval is explicit. -/
def BelowFromBirth (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  Observed endpoint uC zC uA zA φ ({physical}/64) (stateSet forwardExit) (stateSet backwardExit)
    forwardRows backwardRows {observed} (fun t x => strength t x < {threshold})

theorem from_entry_below {{uC zC uA zA : FA}} {{φ : ℝ}} (entry : SectionEntry endpoint uC zC uA zA φ) :
    BelowFromBirth uC zC uA zA φ := by
  apply of_birth ({signed}.from_entry entry) (by norm_num : 0 < {observed})
    (by change {observed} ≤ {physical}; norm_num) (by change {observed} ≤ {physical}; norm_num) (by norm_num)
'''
    for direction in ('fwd','back'):
        source += f'  · with_unfolding_all exact ({archive}.{direction}_below endpoint.start).take {observed}\n'
    source += '''
/-- A single pair of embedded nested tori supports every admitted birth angle. -/
theorem from_birth :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → BelowFromBirth uC zC uA zA φ := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,nested,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),fun φ small => from_entry_below
      (transfer_to_start (by simpa using cC) (by simpa using cA) endpoint small)⟩
'''
    return name,source+f'\nend PlasmaLean.Design.{name}\n',['from_entry_below','from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--launch',type=int,required=True)
    p.add_argument('--archive',type=Path,required=True,help='accepted ordered submirror or clearance receipt')
    p.add_argument('--signed',type=Path,required=True)
    p.add_argument('--length',type=int,help='observe this many rows, defaulting to the longest shared prefix')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/submirror-prefix-observations')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    label,path,_,_ = load(args.launch)
    checksum = digest(path)
    archive,signed = [json.loads(p.read_text()) for p in (args.archive,args.signed)]
    physical = signed['length_each_direction']
    covered = archive['groups'][-1]['stop']
    observed = min(physical,covered) if args.length is None else args.length
    drop = Fraction(archive.get('drop',0))
    target = HEIGHTS[0]-drop
    if not 0<observed<=min(physical,covered) or not 0 <= drop < HEIGHTS[0]:
        p.error('choose a positive observable length inside both archives and a valid field threshold')
    if Fraction(archive.get('target',target))!=target:
        p.error('wrong target for the declared height drop')
    token = label+(f'Drop{drop.numerator}Over{drop.denominator}' if drop else '')
    sname = f'DommaschkSignedPrefix{label}{physical:03}'
    aname = f'Dommaschk{token}SubmirrorPrefix{covered:03}'
    roots,keys = [],[]
    for info,name,paths in [(signed,sname,[signed['proof_root'],signed['import_path']]),
                            (archive,aname,archive['import_paths'])]:
        if (info['endpoint'].upper(),info['packet_sha256'],info['module'])!=(label,checksum,name):
            p.error('launch, archive digest or source theorem does not match')
        ps = list(map(Path,paths))
        root = admitted(ps[0],name,info['key'])
        roots.extend(ps)
        keys.append(root['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    overlay = merge_import_roots(args.cache,roots,keys)
    decl = declaration(token,drop,sname,aname,physical,covered,observed)
    root,rec = compile_modules(args.cache/decl[0],[decl],[overlay],
        [checksum,lake('lean','--version'),keys,digest(DESIGN/'DommaschkSubmirrorPrefixObservation.trace')],
        args,PACKAGE)
    result = {k:rec[k] for k in ('key','module','axioms','theorems','wall_seconds')}
    result.update(endpoint=label,signed_length=physical,ordered_length=covered,observed_length=observed,
                  drop=str(drop),target=str(target),packet_sha256=checksum,parents=keys,
                  import_paths=[str(root),str(overlay)])
    save(args.output,result)
    print(decl[0],rec['key'],flush=True)


if __name__ == '__main__':
    main()
