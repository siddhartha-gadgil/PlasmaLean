"""Verify Cartesian regular-birth tubes along the pilot and secondary signed physical arcs."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_first_well_action import NAME as WELL
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


NAME = 'DommaschkQ0R478RegularBirths'
PACKAGE = 'SecondaryRegularBirthCache'
THEORY = 'DommaschkPhaseZeroRegularBirth'


def family_source(counts):
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    name = 'DommaschkRegularBirthArcs' + suffix
    family = 'DommaschkCommonEndpointTraces' + suffix
    cal = 'DommaschkCalibratedFamily' + suffix
    n = counts['q0r478']
    src = f'''module
public import CalibratedFamilyCache.{cal}
public import {PACKAGE}.{NAME}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkPhaseZeroRegularBirth DommaschkFirstMirrorWell
open DommaschkMirrorLaunch DommaschkCommonPilotObservables DommaschkSignedTraceDomain
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open {family} (checkpoint)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
theorem pilot : Common checkpoint (fun φ y => {cal}.Observed φ y ∧ Population (316 / 64) y) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,var,each,calibrate⟩ := {cal}.same_embedded_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,var,each,fun φ small => ?_⟩
  obtain ⟨x,y,born,p,obs⟩ := calibrate φ small
  refine ⟨x,y,born,p,obs,?_⟩
  obtain ⟨⟨fw⟩,⟨bw⟩⟩ := obs.1.1
  have reg := DommaschkSignedTraceDomain.on_path p (by change 0 < 391; norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  apply population (signed_of_clock p p.forward p.backward) (b := 325 / 64)
    (by change 325 / 64 < (391 : ℝ) / 64; norm_num) _ fw bw
  intro t ht
  apply reg
  change -(391 : ℝ) / 64 ≤ t ∧ t ≤ 391 / 64
  exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
'''
    thms = ['pilot']
    if n > 327:
        src += f'''
theorem both : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → ∃ y z : ℝ → Plane,
      y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) ∧ {cal}.Observed φ y ∧
      Population (316 / 64) y ∧ z φ = coordinates.symm (birth uC zC uA zA (239 / 500) φ) ∧
      DommaschkLowerActionPath.Signed (MirrorEndpoint.start .q0r478)
        (checkpoint .q0r478).forwardRows (checkpoint .q0r478).backwardRows ({n} / 64) z ∧
      Population (317 / 64) z := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,pilotAt⟩ := pilot
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  obtain ⟨_,y,born,_,obs,first⟩ := pilotAt φ small
  have pass := each .q0r478 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)
  obtain ⟨z,bornZ,signed,second⟩ := {NAME}.from_passage
    (extraF := (checkpoint .q0r478).forwardRows.drop 327)
    (extraB := (checkpoint .q0r478).backwardRows.drop 327) small pass
    (by change 327 / 64 < ({n} : ℝ) / 64; norm_num) rfl rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  exact ⟨y,z,born,obs,first,bornZ,signed,second⟩
'''
        thms.append('both')
    return name, src + f'end PlasmaLean.Design.{name}\n', thms


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--well', required=True, type=Path)
    p.add_argument('--calibrated', type=Path)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/regular-birth-arcs')
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()

    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()

    def checked(report):
        roots = list(map(Path,report['import_paths']))
        admitted(roots[0],report['module'],report['key'])
        return roots

    def result(record, roots):
        return {k:record[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')} | {
            'import_paths': list(map(str,roots))}

    well = json.loads(a.well.read_text())
    packet = digest(load(478)[1])
    if well['module'] != WELL or well['packet_sha256'] != packet:
        p.error('expected the outer launch’s signed physical branches')
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    keys = [lake('lean','--version'),digest(DESIGN/(THEORY+'.trace')),well['key']]
    source = (Path(__file__).parent/'templates/secondary_regular_birth.lean.tpl').read_text()
    roots = checked(well)
    item = (NAME,source,['from_passage'])
    root,mark = compile_modules(a.cache/NAME,[item],roots,keys,a,PACKAGE)
    out = result(mark,[root,*roots]) | {'packet_sha256':packet, 'outer_from_birth':False}
    if a.calibrated:
        cal = json.loads(a.calibrated.read_text())
        counts = cal['lengths_each_direction']
        suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
        if cal['module'] != 'DommaschkCalibratedFamily'+suffix or counts['q0r470'] != 391:
            p.error('expected the physical family with the complete signed pilot')
        keys.extend([mark['key'],cal['key']])
        overlay = merge_import_roots(a.cache/'ground',[root,*roots,*checked(cal)],keys)
        item = family_source(counts)
        rb,done = compile_modules(a.cache/item[0],[item],[overlay],keys,a,'RegularBirthArcsCache')
        out.update(birth=result(done,[rb,overlay]), calibrated_key=cal['key'],
                   lengths_each_direction=counts,outer_from_birth=counts['q0r478']>327)
    save(a.output,out)
    print(out.get('birth',out)['key'])


if __name__ == '__main__':
    main()
