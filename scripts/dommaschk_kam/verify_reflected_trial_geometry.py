"""Kernel-check both frame projections, reflected centre gaps and rates on the signed archives."""
import argparse
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_mirror_pilot import Model, R0M
from emit_position_slabs import frame, rational, step
from emit_sparse_taylor_slab import model_literal
from endpoint_reflected_trials import paired_rows
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


def geometry(label, pairs):
    top = f'DommaschkTrialGeometry{label.upper()}_{pairs[0].index}_{pairs[-1].index}'
    lines = ['module','public import PlasmaLean.Design.DommaschkShiftedTrial',
             'public import PlasmaLean.Design.DommaschkSymmetricSections','',
             '/-! # Archived common physical rectangles for the two signed directions -/',
             '@[expose] public section','noncomputable section','namespace PlasmaLean.Design.'+top,
             'open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkBounceTaylor',
             'open DommaschkJacobianReflection DommaschkPhysicalTraceStep','']
    names=[]
    for p in pairs:
        i=p.index
        radial,height=p.common_radii
        pr,pz=p.backward_radii
        fm=Model(p.forward['coefficients'][0],radial)-R0M
        fz=Model(p.forward['coefficients'][1],height)
        lines.extend([f'namespace Row{i}',f'def forwardRow : Step := {step(p.forward)}',
                      f'def backRow : Step := {step(p.backward)}',
                      f'def forwardLeft : Frame := {frame(p.forward_left)}',
                      f'def backLeft : Frame := {frame(p.backward_left)}',
                      f'def box : Inputs := ⟨{model_literal(fm)}, {model_literal(fz)},',
                      '  exactPoly [], exactPoly []⟩',f'def rate : ℚ := {rational(p.common_rate)}',
                      'theorem geometry :',
                      '    CenterMatches forwardRow box ∧ backLeft = reflectFrame forwardLeft ∧',
                      '    backRow.frame = reflectFrame forwardRow.frame ∧',
                      '    PositionFrameProjection.Rectangle forwardLeft forwardRow.frame forwardRow.trial',
                      f'      {radial} {height} ∧',
                      '    PositionFrameProjection.Rectangle backLeft backRow.frame backRow.trial',
                      f'      {pr} {pz} ∧ DommaschkShiftedTrial.Fits backRow box {pr} {pz} ∧',
                      '    rate ≤ forwardRow.mu ∧ rate ≤ backRow.mu := by',
                      '  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩',
                      '  · constructor <;> with_unfolding_all rfl',
                      *(['  · constructor <;> unfold PositionFrameProjection.rowFits <;>',
                         "      apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl"]*2),
                      '  · constructor <;> kernel_fact','  · kernel_fact','  · kernel_fact',
                      f'end Row{i}',''])
        names.append(f'Row{i}.geometry')
    lines.extend(['end PlasmaLean.Design.'+top,''])
    return top,'\n'.join(lines),names


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',nargs='+',choices=ENDPOINTS,default=ENDPOINTS)
    p.add_argument('--range',nargs=2,type=int,default=(0,7),metavar=('FIRST','LAST'))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-trial-geometry')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version=lake('lean','--version')
    env=SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                        lean_path=lake('printenv','LEAN_PATH'))
    guards=[version,*(digest(DESIGN/(m+'.trace')) for m in ('DommaschkShiftedTrial','DommaschkSymmetricSections'))]
    records=[]
    for label in a.endpoints:
        path=RECORD.with_name(f'bounce_frame_q{label[1]}_u{label[3:]}.json.gz')
        name,source,thms=geometry(label,list(paired_rows(path,*a.range)))
        root,marker=compile_modules(a.cache/name,[(name,source,thms)],[],[*guards,digest(path)],env,'TrialGeometryCache')
        records.append({'endpoint':label,'packet_sha256':digest(path),'key':marker['key'],
                        'module':name,'theorems':marker['theorems'],'axioms':marker['axioms'],
                        'import_paths':[str(root)]})
        print(f'{label}: {len(thms)} reflected rows accepted {marker["key"]}',flush=True)
    if a.output:
        save(a.output,records)


if __name__ == '__main__':
    main()
