"""Verify a spatial bisection of an archived projected Jacobian.

Run --part lower and --part upper in independent workers, then --part join.
All three packages use the same signed widths, rates and physical clock.
"""
import argparse
from fractions import Fraction
import gzip
import json
import os
from pathlib import Path
import re
from string import Template
import subprocess
import time
from types import SimpleNamespace

from bounce_mirror_pilot import Model, R0M, ZERO, angle_models
from emit_rectangular_jacobian import CLOCK, panel_certificate, rectangular_data
from emit_sparse_jacobian import derivative_file, header, matrix_certificate
from emit_sparse_taylor_slab import RECORD, ROOT, field, model_literal, models
from screen_sparse_jacobians import field_jet, split_coordinate, symmetric_models
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import (ALLOWED, DESIGN, JACOBIAN_PACKAGE, artifact_hashes,
    digest, external_dependencies, key_of)


CACHE = ROOT/'.lake/vertical-jacobian'
TOP_THEOREMS = ['physical_clock_log_norm','denominator_pos','fits_record']


def branch(index, side):
    """Enclose all nine field polynomials on one closed vertical half-interval."""
    start,step,radii = rectangular_data(index)
    r,original_z = [Model(p,e) for p,e in zip(step['coefficients'],radii,strict=True)]
    z = tuple(split_coordinate(original_z,2))[side]
    stem = f'DommaschkSplitJacobian{index:03}'+('Lower','Upper')[side]
    inputs,panel = stem+'Inputs',stem+'Panels'
    waves = angle_models(Fraction(2*index+1,128),Fraction(1,128),Fraction(0))
    cols = (r-R0M,z,waves[2],waves[1])
    def head(deps,title): return header(deps,title,stem,'DommaschkJacobian')
    end = f'\nend PlasmaLean.Design.{stem}\n'
    files = {inputs:head(['DommaschkJacobianFrames'],'One closed vertical half of the trial')+
             'def trial : Inputs := ⟨'+',\n  '.join(map(model_literal,cols))+'⟩\n'+end}
    leaves = {}
    for scalar,tag,jets in zip(('dD','dnR','dnZ'),('D','R','Z'),field_jet(),strict=True):
        for axis,(suffix,terms) in enumerate(zip(('','U','Z'),jets,strict=True)):
            key = tag+suffix
            symbol = 'grad'+key if suffix else scalar
            blocks = models(terms,cols)
            leaves[key] = symbol+'0',symbol,sum(blocks,ZERO)
            files[stem+key] = (derivative_file(scalar,symbol,axis-1,blocks,stem,inputs,'DommaschkJacobian')
                               if suffix else head([inputs],'Sparse field on the vertical half')+
                               field(scalar,cols)+end)
    rate = Fraction(step['log_norm_upper'])
    files[panel] = panel_certificate(panel,symmetric_models(0,1,index,start,step,r,z),rate)
    body = matrix_certificate(leaves,step,namespace=stem,start=start,dependencies=list(files),
                              context='DommaschkJacobian',panel=panel)
    files[stem+'Bounds'] = body.replace('firstLeft','leftFrame').replace('firstRight','rightFrame')
    block,local = divmod(index,8)
    harmonic = f'DommaschkHarmonicBlock{block:02}'
    with gzip.open(RECORD,'rt') as fp:
        forward, = [x for x in json.load(fp)['traces'] if x['direction']==1]
    files[stem] = head([stem+'Bounds',harmonic],'Physical Jacobian on the closed vertical half') + (
        Template(CLOCK.read_text()).substitute(i=index,end=index+1,offset=2*index+1,
            local=local,base=8*block,count=min(8,391-8*block),harmonic=harmonic,panel=panel,
            rate=rate,forward_rate=forward['steps'][index]['log_norm_upper'])) + end
    return add_shared_powers(files,inputs,stem,cols)


def declarations(files):
    """Relocate the row-local imports; leave ordinary library imports on the Lake path."""
    last = next(reversed(files))
    def relocate(m):
        return 'public import '+JACOBIAN_PACKAGE+'.'+m[1] if m[1] in files else m[0]
    return [(n,re.sub(r'^public import PlasmaLean\.Design\.(\w+)$',relocate,s,flags=re.M),
             TOP_THEOREMS if n==last else []) for n,s in files.items()]


def branch_info(index, side, cache, version):
    files = branch(index,side)
    name = next(reversed(files))
    ds = declarations(files)
    common = [digest(RECORD),version,external_dependencies(list(files.items()))]
    return cache/name,ds,common


def known(root,key):
    record = json.loads((root/'accepted.json').read_text())
    if record['key'] != key or set(record['axioms']) != ALLOWED:
        raise ValueError(f'incorrect split certificate: {root}')
    artifact_hashes(root,record)
    return record


def join_source(index):
    _,step,radii = rectangular_data(index)
    zz = Model(step['coefficients'][1],radii[1])
    low,up = split_coordinate(zz,2)
    stem = f'DommaschkSplitJacobian{index:03}'
    s = f'(128*t-{2*index+1})'
    i = f'Set.Icc ({index}/64 : ℝ) ({index+1}/64)'
    shifts = low.a[0]-zz.a[0],up.a[0]-zz.a[0]
    with gzip.open(RECORD,'rt') as fp:
        forward, = [x for x in json.load(fp)['traces'] if x['direction']==1]
    forward_rate = forward['steps'][index]['log_norm_upper']
    return stem,f'''module
public import {JACOBIAN_PACKAGE}.{stem}Lower
public import {JACOBIAN_PACKAGE}.{stem}Upper
public import PlasmaLean.Certificates.DyadicTaylorCover

/-! # Two vertical boxes cover a complete projected physical trial -/
@[expose] public section
namespace PlasmaLean.Design.{stem}
open Certificates.TrajectoryTaylorModel DommaschkJacobian DommaschkBounceTaylor DommaschkKam
open DommaschkKam.DkPoly Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace
set_option linter.style.longLine false

def trial : Inputs := {{ {stem}Lower.trial with z := {model_literal(zz)} }}
abbrev leftFrame := {stem}Lower.leftFrame
abbrev rightFrame := {stem}Lower.rightFrame
abbrev logNorm := {stem}Lower.logNorm

/-- Every point of the original vertical model is in one of the two closed children. -/
theorem vertical_cover {{t z : ℝ}} (h : trial.z.Mem t z) :
    {stem}Lower.trial.z.Mem t z ∨ {stem}Upper.trial.z.Mem t z := by
  have h' := dyadic_cover (bits := 80) (c := {zz.a[0]}) (tail := {zz.a[1:]})
    (e := {zz.e}) (l := {shifts[0]}) (u := {shifts[1]}) (el := {low.e}) (eu := {up.e})
    (t := t) (y := z) (by norm_num) (by norm_num) (by norm_num) h
  exact h'

/-- Positivity of the physical denominator on the union of both children. -/
theorem denominator_pos {{t R z : ℝ}} (ht : t ∈ {i}) (hu : trial.u.Mem {s} (R-dkR0))
    (hz : trial.z.Mem {s} z) : 0 < evR (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) dD := by
  rcases vertical_cover hz with lo | hi
  · exact {stem}Lower.denominator_pos ht hu lo
  · exact {stem}Upper.denominator_pos ht hu hi

/-- Both children have the same affine frame, clock and signed rate. -/
theorem physical_clock_log_norm {{t R z : ℝ}} (ht : t ∈ {i}) (hu : trial.u.Mem {s} (R-dkR0))
    (hz : trial.z.Mem {s} z) (w : Plane) :
    ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (spatialMatrix (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)))
      (frameEquiv leftFrame rightFrame {s}) (frameVelocity leftFrame rightFrame) w⟫ ≤
      (logNorm : ℝ)*‖w‖^2 := by
  rcases vertical_cover hz with lo | hi
  · exact {stem}Lower.physical_clock_log_norm ht hu lo w
  · exact {stem}Upper.physical_clock_log_norm ht hu hi w

/-- The combined rate fits the stored forward allowance. -/
theorem fits_record : logNorm ≤ {forward_rate} := {stem}Lower.fits_record
end PlasmaLean.Design.{stem}
'''


def wait_for(marker, deadline):
    if deadline is None or marker.is_file():
        return
    print('Waiting for '+str(marker),flush=True)
    while not marker.is_file():
        remaining = deadline-time.monotonic()
        if remaining <= 0:
            raise FileNotFoundError(marker)
        time.sleep(min(remaining,5))


def join(index, cache, version, args=None, deadline=None):
    children=[]
    for side in range(2):
        base,ds,common = branch_info(index,side,cache,version)
        key=key_of([common,ds])
        root=base/key
        wait_for(root/'accepted.json',deadline)
        children.append((root,known(root,key)))
    name,source=join_source(index)
    ds=[(name,source,[*TOP_THEOREMS,'vertical_cover'])]
    common=[digest(RECORD),version,digest(DESIGN.parent/'Certificates/DyadicTaylorCover.trace'),
            [r['key'] for _,r in children]]
    key=key_of([common,ds])
    root=cache/name/key
    if args is not None:
        tree=root/JACOBIAN_PACKAGE
        tree.mkdir(parents=True,exist_ok=True)
        for child,record in children:
            for rel in record['artifacts']:
                if Path(rel).parts[0] == JACOBIAN_PACKAGE:
                    p=root/rel
                    try:
                        os.link(child/rel,p)
                    except FileExistsError:
                        if not p.samefile(child/rel): raise
        compile_modules(cache/name,ds,[],common,args,package=JACOBIAN_PACKAGE)
    wait_for(root/'accepted.json',deadline)
    result=known(root,key)
    artifacts=dict(result['artifacts'])
    for _,r in children:
        artifacts.update({n:h for n,h in r['artifacts'].items() if Path(n).parts[0]==JACOBIAN_PACKAGE})
    result={**result,'artifacts':artifacts}
    artifact_hashes(root,result)
    return root,result


def physical(index, cache, version, args, deadline=None):
    """Attach the joined rectangles to the archived scalar row and its true central ODE defect."""
    import verify_physical_trace_slabs as verifier
    jacobian = join(index,cache,version,args,deadline)
    packet_hash = digest(RECORD)
    job = next(j for j in verifier.jobs(RECORD,8,False) if j[1:3]==(1,index))
    info = verifier.upstream(ROOT/'.lake/trace-residual',list(verifier.emit_selected([job])),
                             'verify_sparse_reference_slabs.py',packet_hash,version,'TraceCache')
    residual = verifier.accepted(info,index,0)
    packages = [jacobian,residual]
    common = [packet_hash,version,verifier.ROW_SCHEMA_V1,
              [(m,digest(DESIGN/(m+'.trace'))) for m in verifier.LIBRARIES]]
    _,step,radii = rectangular_data(index)
    args.cache = ROOT/'.lake/physical-frame-checks'
    root,record,_ = verifier.verify_row(index,step['physical_trial_radius'],packages,args,common,radii)
    verifier.overlay(args.cache,[record],[*packages,(root,record)],args.lean,args.lean_path)
    return root,record


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index',type=int,default=226,choices=range(391),metavar='INDEX')
    parser.add_argument('--part',choices=('lower','upper','join','physical'),required=True)
    parser.add_argument('--cache',type=Path,default=CACHE)
    parser.add_argument('--wait-seconds',type=int,default=0)
    a=parser.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    deps=['PlasmaLean.Design.DommaschkStoredPowers','PlasmaLean.Design.DommaschkJacobianPanels',
          f'PlasmaLean.Design.DommaschkHarmonicBlock{a.index//8:02}']
    if a.part in ('join','physical'): deps.append('PlasmaLean.Certificates.DyadicTaylorCover')
    if a.part=='physical':
        deps.extend(['PlasmaLean.Design.DommaschkProjectedTrial','PlasmaLean.Design.DommaschkPositionFramesFwd',
                     'PlasmaLean.Design.DommaschkFramedTaylorResidual'])
    subprocess.run(['lake','build','--no-build',*deps],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
    version=lake('lean','--version')
    args=SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                         lean_path=lake('printenv','LEAN_PATH'))
    deadline=time.monotonic()+a.wait_seconds
    if a.part=='physical':
        root,record=physical(a.index,a.cache.resolve(),version,args,deadline)
    elif a.part=='join':
        root,record=join(a.index,a.cache.resolve(),version,args,deadline)
    else:
        base,ds,common=branch_info(a.index,int(a.part=='upper'),a.cache.resolve(),version)
        root,record=compile_modules(base,ds,[],common,args,package=JACOBIAN_PACKAGE)
    print(json.dumps({'index':a.index,'part':a.part,'root':str(root),'key':record['key'],
                      'axioms':record['axioms']}),flush=True)


if __name__=='__main__':
    main()
