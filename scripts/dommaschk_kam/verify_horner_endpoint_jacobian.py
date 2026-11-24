"""Prove two phase-zero endpoint Jacobians on one shared seven-harmonic spatial jet."""

import argparse
from fractions import Fraction as F
from pathlib import Path
import subprocess
import time

from bounce_mirror_pilot import R0M, angle_models
from emit_rectangular_jacobian import panel_certificate
from emit_sparse_jacobian import matrix_certificate
from emit_sparse_taylor_slab import model_literal
from endpoint_reflected_trials import paired_rows
from screen_endpoint_jacobian_sharing import frame_models, joint_models, native_jet, own_models
from screen_sparse_jacobians import field_jet
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_forward_jacobians import PACKAGE as JACOBIAN
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_native_action_models import (MATCH, WAVES, emit_horner_field, emit_static_field,
                                        footer, header, weighted_channels)
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, key_of, save
from verify_signed_mirror_passage import merge_import_roots


DATA = 'HornerJetDataCache'
FIELDS = 'HornerJetFieldCache'
INPUT = 'HornerJetInputCache'
TAGS = ('D','DU','DZ','R','RU','RZ','Z','ZU','ZZ')
SYMBOLS = [sym if op is None else f'(DkPoly.{op} {sym})'
           for sym in ['dD','dnR','dnZ'] for op in [None,'dU','dZ']]


def checked_shared_roots(jac, root, version):
    """Bind the exact imported data, input and jet modules to the audited matrix sources."""
    labels = jac['shared_endpoints']
    i, label = jac['index'], jac['endpoint']
    if (not 1 <= len(labels) <= 2 or len(set(labels)) != len(labels) or label not in labels
            or not set(labels) <= set(ENDPOINTS) or len({e[:2] for e in labels}) != 1):
        raise ValueError('invalid shared Jacobian endpoint pair')
    hashes = [digest(RECORD.with_name(f'bounce_frame_{e[:2]}_u{e[3:]}.json.gz')) for e in labels]
    stem = 'DommaschkHornerJet'+''.join(e.upper() for e in labels)+f'{i:03}'
    expected = [*['DommaschkHornerJetData'+t for t in TAGS], stem+'Inputs', *[stem+t for t in TAGS]]
    parents = jac['shared_parents']
    if [p['module'] for p in parents] != expected:
        raise ValueError('unexpected shared Jacobian dependencies')
    roots = []
    for parent in parents:
        base = Path(parent['root'])
        admitted(base,parent['module'],parent['key'])
        roots.append(base)
    name = jac['module']
    declarations = []
    for m in [name+'Panels',name+'Bounds',name]:
        proofs = [t.split('.')[-1] for t in jac['theorems']] if m == name else []
        declarations.append((m,(root/JACOBIAN/(m+'.lean')).read_text(),proofs))
    common = [JACOBIAN,version,digest(DESIGN/'DommaschkNativeActionModel.trace'),
              *hashes,*[p['key'] for p in parents],digest(DESIGN/'DommaschkJacobianPanels.trace')]
    if key_of([common,declarations]) != jac['key']:
        raise ValueError('shared dependency keys do not match the accepted Jacobian')
    return roots


def inputs_source(name, i, ins, section):
    _,u,z,phase = ins
    harmonic = f'DommaschkHarmonicBlock{i//8:02}'
    src = header(name,['PlasmaLean.Design.DommaschkNativeActionModel','PlasmaLean.Design.'+harmonic])
    src += f'def displacement : Model := {model_literal(u)}\ndef vertical : Model := {model_literal(z)}\n'
    src += 'def phase : Wave → Model\n' + ''.join(
        f'  | .{wave} => {model_literal(m)}\n' for wave,m in zip(WAVES,phase,strict=True))
    src += f'''theorem angles {{t : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64)) (w : Wave) :
    (phase w).Mem (128*t-{2*i+1}) (w.value (2*t)) := by
  cases w
  · have h : Matches (constant 1) (phase .one) := {MATCH}
    rw [← h.eq]
    simpa only [Wave.value, Rat.cast_one] using constant_mem 1 (128*t-{2*i+1})
'''
    for j in range(1,7):
        k, sine = (j-1)//2, 'true' if j%2 else 'false'
        phi = '(2*t)' if k == 0 else f'({k+1}*(2*t))'
        src += f'''  · have ht' : t ∈ Set.Icc ((({i}:ℕ):ℝ)/64) (((({i}:ℕ):ℝ)+1)/64) := by
      norm_num at ht ⊢; exact ht
    have h := Certificates.TrajectoryHarmonicPacket.physical
      (i := {i}) ({harmonic}.packet {i%8}) false ({k}:Fin 3) {sine} ht'
    rw [show 2*((({i}:ℕ):ℝ))+1 = {2*i+1} by norm_num,
      show 2*((({k}:Fin 3).val:ℝ)+1)*(if false then -t else t) = {phi} by norm_num <;> ring] at h
    exact h
'''
    if section:
        src = src.split('theorem angles')[0]
        src += f'''private theorem negate_value {{s x : ℝ}} {{m : Model}} (h : m.Mem s (-x)) :
    (Certificates.TrajectoryTrig.negative m).Mem s x := by
  change |x - Certificates.QPoly.eval (Certificates.QPoly.scale (-1) m.poly) s| ≤ _
  change |-x - Certificates.QPoly.eval m.poly s| ≤ _ at h
  simp only [Certificates.QPoly.eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul, sub_neg_eq_add]
  rw [show x + Certificates.QPoly.eval m.poly s = -(-x - Certificates.QPoly.eval m.poly s) by ring, abs_neg]
  exact h

theorem angles {{t : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64)) (w : Wave) :
    (phase w).Mem (128*t-{2*i+1}) (w.value (2*(Real.pi / 2+t))) := by
  cases w
  · have h : Matches (constant 1) (phase .one) := {MATCH}
    rw [← h.eq]
    simpa only [Wave.value, Rat.cast_one] using constant_mem 1 (128*t-{2*i+1})
'''
        for j in range(1,7):
            k, sine = (j-1)//2, 'true' if j%2 else 'false'
            m = f'(({harmonic}.packet {i%8} false ({k}:Fin 3)).model {sine})'
            reflected = f'(Certificates.TrajectoryTrig.negative {m})' if k%2==0 else m
            src += f'''  · have compare : Matches {reflected} (phase .{WAVES[j]}) := {MATCH}
    rw [← compare.eq]
'''
            if k%2==0:
                src += '    apply negate_value\n'
            src += f'''    have ht' : t ∈ Set.Icc ((({i}:ℕ):ℝ)/64) (((({i}:ℕ):ℝ)+1)/64) := by
      norm_num at ht ⊢; exact ht
    have h := Certificates.TrajectoryHarmonicPacket.physical_section
      (i := {i}) ({harmonic}.packet {i%8}) true false ({k}:Fin 3) {sine} ht'
    norm_num [Wave.value, Certificates.TrajectoryTrig.wave] at h ⊢
    convert h using 2 <;> ring
'''
        src=src.replace('public import PlasmaLean.Design.'+harmonic,
                        'public import PlasmaLean.Design.DommaschkOppositeHarmonic\npublic import PlasmaLean.Design.'+harmonic)
    return name,src+footer(name),['angles']


def endpoint_modules(label, pair, jet, fields, shared):
    i = pair.index
    stem = f'DommaschkJacobian{label.upper()}PairedForward{i:03}'
    panel, core = stem+'Panels',stem+'Bounds'
    psrc = panel_certificate(panel,frame_models(jet,pair),pair.common_rate)
    leaves = {tag:(f'{field}.model',symbol,m)
        for tag,field,symbol,m in zip(TAGS,fields,SYMBOLS,(m for g in jet for m in g),strict=True)}
    body = matrix_certificate(leaves,pair.forward,namespace=stem,start=pair.forward_left,
                              dependencies=[panel],context='DommaschkJacobian',panel=panel,free_leaves=True)
    body = body.replace('firstLeft','leftFrame').replace('firstRight','rightFrame')
    body = body.replace('public import PlasmaLean.Design.'+panel,
        'public import '+JACOBIAN+'.'+panel+'\n'+''.join('public import '+FIELDS+'.'+m+'\n' for m in fields))
    r,z = own_models(pair)
    src = header(stem,[JACOBIAN+'.'+core])
    src += 'open DommaschkKam.DkPoly DommaschkJacobian Certificates.PositionFrameSlabs\n'
    src += 'open scoped RealInnerProductSpace\n'
    src += f'''def trial : Inputs := ⟨{model_literal(r-R0M)}, {model_literal(z)},
    {shared}.phase .cos1, {shared}.phase .sin1⟩
def logNorm : ℚ := {pair.common_rate}

theorem clock_inputs {{t R z : ℝ}} (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hu : trial.u.Mem (128*t-{2*i+1}) (R-dkR0)) (hz : trial.z.Mem (128*t-{2*i+1}) z) :
    trial.Mem (128*t-{2*i+1}) (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) :=
  ⟨hu,hz,{shared}.angles ht .cos1,{shared}.angles ht .sin1⟩

private theorem common_box {{s u z : ℝ}} (hs : |s| ≤ 1) (hu : trial.u.Mem s u) (hz : trial.z.Mem s z) :
    {shared}.displacement.Mem s u ∧ {shared}.vertical.Mem s z :=
  ⟨enclose hs hu (by kernel_fact), enclose hs hz (by kernel_fact)⟩

theorem denominator_pos {{t R z : ℝ}} (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hu : trial.u.Mem (128*t-{2*i+1}) (R-dkR0)) (hz : trial.z.Mem (128*t-{2*i+1}) z) :
    0 < evR (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) dD := by
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨u,v⟩ := common_box hs hu hz
  have m := {fields[0]}.sound hs u v ({shared}.angles ht)
  have b := enclose (c := ⟨[1], 255/256⟩) hs m (by kernel_fact)
  norm_num [Model.Mem, abs_le] at b
  linarith

theorem physical_clock_log_norm {{t R z : ℝ}} (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hu : trial.u.Mem (128*t-{2*i+1}) (R-dkR0)) (hz : trial.z.Mem (128*t-{2*i+1}) z)
    (w : Plane) : ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (spatialMatrix (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)))
      (frameEquiv leftFrame rightFrame (128*t-{2*i+1})) (frameVelocity leftFrame rightFrame) w⟫ ≤
      (logNorm : ℝ)*‖w‖^2 := by
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨u,v⟩ := common_box hs hu hz
  apply spatial_log_norm_of_cover {panel}.accepted leftFrame rightFrame _ _ _ _ _ hs _ w
  exact models_mem hs
'''
    src += ''.join(f'    ({m}.sound hs u v ({shared}.angles ht))\n' for m in fields)
    src += f'''
theorem fits_record : logNorm ≤ {pair.forward['log_norm_upper']} := by norm_num [logNorm]
theorem fits_backward_record : logNorm ≤ {pair.backward['log_norm_upper']} := by norm_num [logNorm]
'''
    if label[1]=='1':
        src = src.replace('(2*t)', '(2*(Real.pi / 2+t))')
    return [(panel,psrc,[]),(core,body,[]),(stem,src+footer(stem),
            ['clock_inputs','denominator_pos','physical_clock_log_norm','fits_record','fits_backward_record'])]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',nargs='+',choices=ENDPOINTS,required=True)
    p.add_argument('--row',type=int,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-horner-jacobians')
    args=p.parse_args()
    if (not 1 <= len(args.endpoints) <= 2 or len(set(args.endpoints)) != len(args.endpoints)
            or len({e[:2] for e in args.endpoints})!=1 or not 0<=args.row<391):
        p.error('choose one or two distinct endpoints at the same section and an archived index')
    args.cache=args.cache.resolve()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path=lake('printenv','LEAN_PATH')
    version=lake('lean','--version')
    paths=[RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz') for label in args.endpoints]
    pairs=[next(paired_rows(path,args.row,args.row)) for path in paths]
    hashes=[digest(path) for path in paths]
    coords=[own_models(pair) for pair in pairs]
    r,z=joint_models(*coords) if len(coords)==2 else coords[0]
    i=args.row
    section=int(args.endpoints[0][1])
    waves=angle_models(F(2*i+1,128),F(1,128),F(0))
    if section:
        waves=[m.integer((-1)**((j+1)//2)) for j,m in enumerate(waves)]
    ins=(r,r-R0M,z,waves)
    polynomials=[m for g in field_jet() for m in g]
    groups=weighted_channels(polynomials,[m for g in native_jet() for m in g])
    base=[version,digest(DESIGN/'DommaschkNativeActionModel.trace')]
    def check(modules,dependencies,keys,package):
        name=modules[-1][0]
        result=compile_modules(args.cache/name,modules,dependencies,[package,*base,*keys],args,package)
        print(f'{name} accepted {result[1]["wall_seconds"]:.2f}s',flush=True)
        return result
    stem='DommaschkHornerJet'+''.join(x.upper() for x in args.endpoints)+f'{i:03}'
    t=time.monotonic()
    data=[check([emit_static_field('DommaschkHornerJetData'+tag,symbol,channels)],[],[],DATA)
          for tag,symbol,channels in zip(TAGS,SYMBOLS,groups,strict=True)]
    static_elapsed=time.monotonic()-t
    def merged(items):
        return merge_import_roots(args.cache,[x[0] for x in items],[x[1]['key'] for x in items])
    angle_dependencies=[digest(DESIGN/'DommaschkOppositeHarmonic.trace')] if section else []
    inp=check([inputs_source(stem+'Inputs',i,ins,section)],[],
              [*hashes,digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),*angle_dependencies],INPUT)
    jet,fields=[],[]
    for tag,symbol,channels,(root,record) in zip(TAGS,SYMBOLS,groups,data,strict=True):
        decl,m=emit_horner_field(stem+tag,symbol,channels,ins,record['module'],inp[1]['module'],DATA,INPUT)
        fields.append(check([decl],[root,inp[0]],[record['key'],inp[1]['key']],FIELDS))
        jet.append(m)
    jet=[jet[j:j+3] for j in range(0,9,3)]
    parents=[*data,inp,*fields]
    parent_imports=merged(parents)
    parent_keys=[r['key'] for _,r in parents]
    results=[]
    for label,pair,checksum in zip(args.endpoints,pairs,hashes,strict=True):
        modules=endpoint_modules(label,pair,jet,[r['module'] for _,r in fields],inp[1]['module'])
        root,record=check(modules,[parent_imports],[*hashes,*parent_keys,digest(DESIGN/'DommaschkJacobianPanels.trace')],JACOBIAN)
        report={k:v for k,v in record.items() if k!='artifacts'}
        report.update(endpoint=label,launch_u=str(F(int(label[3:]),1000)),section_in_half_pi=section,
            direction=1,index=i,projected_radii=pair.common_radii,paired_trials=True,
            common_rate=str(pair.common_rate),packet_sha256=checksum,lean_version=version,
            import_paths=[str(root)], shared_endpoints=args.endpoints,
            shared_parents=[{'root':str(base),'key':m['key'],'module':m['module']}
                                                     for base,m in parents])
        save(root/'row.json',report)
        results.append(report)
    save(args.output,results)
    print(f'Static checks/loads {static_elapsed:.1f}s, remaining total {time.monotonic()-t-static_elapsed:.1f}s',flush=True)


if __name__=='__main__':
    main()
