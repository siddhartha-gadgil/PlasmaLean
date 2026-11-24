"""Emit whole-slab or panel-wise physical Jacobian certificates for q0,u=.470 forward rows."""
import argparse
from fractions import Fraction as F
import gzip
import json
from math import ceil, floor, isqrt
from pathlib import Path

from bounce_mirror_pilot import Model, R0M, ZERO, angle_models
from bounce_phase_frame import FRAME_SCALE
from emit_sparse_jacobian import derivative, derivative_file, header, matrix_certificate
from emit_sparse_taylor_slab import DATA, DEST, RECORD, coefficients, field, model_literal, models


def emit(index, panels=False, shared=False):
    with gzip.open(RECORD,'rt') as fp:
        packet = json.load(fp)
    if (packet['coordinate_denominator'] != 2**80 or packet['frame_denominator'] != FRAME_SCALE
            or packet['step'] != '1/64' or packet['order'] != 7 or packet['launch_u'] != '47/100'
            or packet['section_in_half_pi'] != 0):
        raise ValueError('unexpected witness')
    direction, = (trace for trace in packet['traces'] if trace['direction'] == 1)
    step = direction['steps'][index]
    if step['index'] != index:
        raise ValueError('wrong slab')
    start = (direction['steps'][index-1]['frame_end'] if index else
             [[FRAME_SCALE,0],[0,FRAME_SCALE]])
    R, z = (Model(p,step['physical_trial_radius']) for p in step['coefficients'])
    waves = angle_models(F(2*index+1,128),F(1,128),F(0))
    columns = (R-R0M,z,waves[2],waves[1])
    stem = f'DommaschkJacobianForward{index:03}'
    inputs_module = stem+'Inputs'
    finish = 'end PlasmaLean.Design.'+stem+'\n'

    def head(imports, title):
        return header(imports,title,stem,'DommaschkJacobian')

    files = {inputs_module:head(['DommaschkJacobianFrames'], 'Full forward trial tube') +
             'def trial : Inputs := ⟨'+',\n  '.join(map(model_literal,columns))+'⟩\n\n'+finish}
    data = DATA.read_text()
    source_models = {}
    modules = []
    for source,tag in [('dD','D'),('dnR','R'),('dnZ','Z')]:
        p = coefficients(data,source)
        mod = stem+tag
        modules.append(mod)
        files[mod] = head([inputs_module],'Exact field on the trial tube')+field(source,columns)+'\n'+finish
        source_models[tag] = source+'0',source,sum(models(p,columns),ZERO)
        for axis, variable in enumerate('UZ'):
            name = 'grad'+tag+variable
            mod = stem+tag+variable
            modules.append(mod)
            blocks = models(derivative(p,axis),columns)
            files[mod] = derivative_file(source,name,axis,blocks,stem,inputs_module,'DommaschkJacobian')
            source_models[tag+variable] = name+'0',name,sum(blocks,ZERO)
    limits = {}
    def numeric(table, step):
        scale = 10**8
        lo,hi = table['den'][1].bound()
        mid = F(floor((lo+hi)*scale/2),scale)
        radius = F(ceil(max(mid-lo,hi-mid)*scale),scale)
        dl = mid-radius
        tr,di,off = (F(ceil(max(map(abs,table[tag][1].bound()))*scale),scale)
                     for tag in ('tr','dif','off'))
        disk = F(isqrt(int((di*scale)**2+(off*scale)**2))+1,scale)
        budget = F(ceil((tr+disk)/(2*dl)*scale),scale)
        if dl <= 0 or budget > F(step['log_norm_upper']):
            raise ValueError('full-slab trace enclosure exceeds the saved allowance')
        limits.update(dl=dl,tr=tr,di=di,off=off,disk=disk,mu=budget)
        return list(map(str,[mid,radius,dl,tr,di,off]))

    panel = None
    if panels:
        from emit_sparse_jacobian_panels import emit as emit_panels
        panel,source = emit_panels(index)
        modules.append(panel)
        files[panel] = source
        limits['mu'] = F(step['log_norm_upper'])
    core = matrix_certificate(source_models,step,namespace=stem,start=start,dependencies=modules,
                              context='DommaschkJacobian',numeric=numeric,panel=panel)
    core = core.replace('firstLeft','leftFrame').replace('firstRight','rightFrame')
    files[stem+'Bounds'] = core
    block,j = divmod(index,8)
    count = min(8,391-8*block)
    out = head([stem+'Bounds',f'DommaschkHarmonicBlock{block:02}'],
               'Physical forward-clock logarithmic norm on the full trial tube')
    out += 'open PlasmaLean.Certificates.PositionFrameSlabs\nopen scoped RealInnerProductSpace\n'
    if panels:
        matrix_application = f'''  exact spatial_log_norm_of_cover {panel}.accepted leftFrame rightFrame
    (128 * t - {2*index+1}) (R - dkR0) z _ _ hs (models_mem hs hin) x'''
    else:
        matrix_application = f'''  apply spatial_log_norm_of_bounds leftFrame rightFrame (128 * t - {2*index+1}) (R - dkR0) z _ _
    (dl := {limits['dl']}) (tr := {limits['tr']}) (di := {limits['di']}) (off := {limits['off']})
    (disk := {limits['disk']}) <;> first | exact symmetric_bounds hs hin | norm_num [logNorm]'''
    out += f'''
/-- Checked rational logarithmic norm, rounded upward to an eight-decimal grid. -/
def logNorm : ℚ := {limits['mu']}

/-- Both signed harmonic inputs hold on the full absolute-time slab. -/
theorem clock_inputs {{t R z : ℝ}} (ht : t ∈ Set.Icc ({index} / 64 : ℝ) ({index+1} / 64))
    (hu : trial.u.Mem (128 * t - {2*index+1}) (R - dkR0)) (hz : trial.z.Mem (128 * t - {2*index+1}) z)
    : trial.Mem (128 * t - {2*index+1}) (R - dkR0) z (Real.cos (2 * t)) (Real.sin (2 * t)) := by
  let packet := DommaschkHarmonicBlock{block:02}.packet ({j} : Fin {count})
  have ht' : t ∈ Set.Icc ((↑({8*block}+({j} : Fin {count}).val : ℕ) : ℝ)/64)
      (((↑({8*block}+({j} : Fin {count}).val : ℕ) : ℝ)+1)/64) := by norm_num at ht ⊢; exact ht
  have cos := Certificates.TrajectoryHarmonicPacket.physical packet false 0 false ht'
  have sin := Certificates.TrajectoryHarmonicPacket.physical packet false 0 true ht'
  refine ⟨hu,hz,?_,?_⟩
  · change ((packet false 0).model false).Mem _ _
    norm_num [Certificates.TrajectoryTrig.wave] at cos ⊢
    exact cos
  · change ((packet false 0).model true).Mem _ _
    norm_num [Certificates.TrajectoryTrig.wave] at sin ⊢
    exact sin

/-- The sparse field denominator is positive throughout the full moving tube. -/
theorem denominator_pos {{t R z : ℝ}} (ht : t ∈ Set.Icc ({index} / 64 : ℝ) ({index+1} / 64))
    (hu : trial.u.Mem (128 * t - {2*index+1}) (R - dkR0)) (hz : trial.z.Mem (128 * t - {2*index+1}) z)
    : 0 < evR (R - dkR0) z (Real.cos (2 * t)) (Real.sin (2 * t)) dD := by
  have hs : |128 * t - {2*index+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := dD_range hs (dD_checked.mem hs (clock_inputs ht hu hz))
  exact lt_of_lt_of_le (by norm_num) h.1

/-- The recorded outward clock and both position inputs imply the true
spatial quadratic bound through the entire trial tube. -/
theorem physical_clock_log_norm {{t R z : ℝ}} (ht : t ∈ Set.Icc ({index} / 64 : ℝ) ({index+1} / 64))
    (hu : trial.u.Mem (128 * t - {2*index+1}) (R - dkR0)) (hz : trial.z.Mem (128 * t - {2*index+1}) z)
    (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian
      (spatialMatrix (R - dkR0) z (Real.cos (2 * t)) (Real.sin (2 * t)))
      (frameEquiv leftFrame rightFrame (128 * t - {2*index+1})) (frameVelocity leftFrame rightFrame) x⟫ ≤
      (logNorm : ℝ) * ‖x‖ ^ 2 := by
  have hs : |128 * t - {2*index+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hin := clock_inputs ht hu hz
{matrix_application}

/-- This bound fits the exact allowance stored in the forward witness row. -/
theorem fits_record : logNorm ≤ {step['log_norm_upper']} := by norm_num [logNorm]

'''
    files[stem] = out+finish
    if shared:
        from shared_sparse_powers import add_shared_powers
        return add_shared_powers(files,inputs_module,stem,columns)
    return files


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index',default=1,type=int,choices=range(391),metavar='0..390')
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--panels',action='store_true',help='use the panel principal-minor bound')
    parser.add_argument('--shared-powers',action='store_true',help='reuse checked coordinate powers')
    parser.add_argument('--output-dir',default=DEST,type=Path)
    args = parser.parse_args()
    for name,source in emit(args.index,args.panels,args.shared_powers).items():
        target = args.output_dir/(name+'.lean')
        if args.check:
            if target.read_text() != source:
                raise SystemExit('regenerate '+target.name)
        else:
            target.write_text(source)
