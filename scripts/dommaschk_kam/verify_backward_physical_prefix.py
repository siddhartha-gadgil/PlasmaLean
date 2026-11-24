"""Prove a nested Q-16 birth follows a backward prefix using the forward spatial packages.

Run with --length 3 for the first additional backward row. One Lean process
checks each reflected defect, physical step, and the final connected prefix in
sequence. For forward shared-power jobs use --shared-from 16.
"""
import argparse
import fcntl
import gzip
import json
import os
from pathlib import Path
import re
import subprocess
from string import Template
import time

from emit_backward_panel_rate import backward_rate
from emit_reflected_reference import render
from verify_physical_trace_slabs import (ALLOWED, DESIGN, HERE, JACOBIAN_PACKAGE, RECORD, ROOT, TRACKED_PANEL_ROWS,
    accepted, artifact_hashes, digest, emit_jacobian, emit_selected, jobs, key_of, run_lean, save,
    tracked_jacobian, upstream)


PACKAGE = 'BackwardTraceCache'
TEMPLATE = HERE/'templates/physical_backward_step.lean.tpl'
STATIC = ('DommaschkBackwardPrefix','DommaschkSectionReflection','DommaschkJacobianReflection',
          'DommaschkPhysicalTraceStep','DommaschkPositionFramesBack')


def compile_modules(work, declarations, links, common, args, package=PACKAGE):
    key = key_of([common,declarations])
    root = work/key
    tree = root/package
    tree.mkdir(parents=True,exist_ok=True)
    top = declarations[-1][0]
    with (root/'lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        marker = root/'accepted.json'
        if marker.exists():
            record = json.loads(marker.read_text())
            if record['key'] != key or record['module'] != top or set(record['axioms']) != ALLOWED:
                raise ValueError(f'wrong cached backward result: {marker}')
            artifact_hashes(root,record)
            return root, record
        env = {**os.environ,'LEAN_NUM_THREADS':'1','LEAN_PATH':os.pathsep.join(
            [str(root),*[str(x) for x in links],args.lean_path])}
        cmd = [args.lean,'-j1','-DwarningAsError=true','-R',str(root)]
        total = peak = 0
        files = []
        for name,source,theorems in declarations:
            src,obj = tree/(name+'.lean'),tree/(name+'.olean')
            src.write_text(source)
            seconds,rss = run_lean([*cmd,'-o',str(obj),str(src)],env,root/'peak',root/(name+'.log'))
            total,peak = total+seconds,max(peak,rss)
            files.extend([src,*tree.glob(name+'.olean*')])
        audit = root/'Audit.lean'
        fq = [f'PlasmaLean.Design.{n}.{t}' for n,_,ts in declarations for t in ts]
        audit.write_text(f'import {package}.{top}\n'+''.join(f'#print axioms {t}\n' for t in fq))
        log = root/'audit.log'
        seconds,rss = run_lean([*cmd,str(audit)],env,root/'peak',log)
        for t in fq:
            match = re.search(re.escape(t+"'") + r' depends on axioms:\s*\[([^]]*)\]',log.read_text())
            if not match or set(map(str.strip,match[1].split(','))) != ALLOWED:
                raise ValueError(f'axiom audit failed: {t}')
        record = {'module':top,'key':key,'theorems':fq,'axioms':sorted(ALLOWED),
                  'wall_seconds':round(total+seconds,3),'peak_rss_kib':max(peak,rss),
                  'artifacts':{str(path.relative_to(root)):digest(path) for path in [*files,audit,log]}}
        save(marker,record)
        return root,record


def prefix_source(n, maximum):
    ids = ['DommaschkJacobianBackward000.row','DommaschkPhysicalBackwardSecondStep.row',
           *[f'DommaschkPhysicalBackward{i:03}.row' for i in range(2,n)]]
    proofs = ['DommaschkPhysicalBackwardFirstStep','DommaschkPhysicalBackwardSecondStep',
              *[f'DommaschkPhysicalBackward{i:03}' for i in range(2,n)]]
    name = f'DommaschkBackwardPrefix{n:03}'
    lines = ['module','public import PlasmaLean.Design.DommaschkBackwardPrefixRadius',
             *['public import '+PACKAGE+'.'+m for m in proofs[2:]],'',
             '/-! # Joined physical backward QA2R prefix. Generated from the accepted trace rows. -/',
             '@[expose] public section','noncomputable section','namespace PlasmaLean.Design.'+name,
             'open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkBackwardPrefix',
             'set_option maxRecDepth 8192','',
             '/-- Stored rows in chronological order. -/','def rows : List Step := [',
             ',\n  '.join(ids)+']','/-- Ellipsoid at the terminal clock. -/',
             'abbrev exitState := next '+ids[-1],
             f'theorem checked : Chain pilotLimits (MirrorEndpoint.start .q0r470) [rows] {n} exitState := by',
             '  apply Chain.cons (m := exitState) (n := 0)','  · unfold rows',
             *['    refine cons_run '+m+'.checked ?_' for m in proofs],'    rfl','  · exact .nil _',
             'theorem field_bounds : FieldBoundsOn (DommaschkJacobian.euclideanFlow 0 (-1))',
             '    (DommaschkJacobian.velocityJacobian 0 (-1)) (MirrorEndpoint.start .q0r470) 0 rows ballDomain := by',
             '  unfold rows','  conv in FieldBoundsOn _ _ _ 0 _ _ =>',
             '    arg 4','    rw [show (0 : ℝ) = (0:ℕ)/64 by norm_num]']
    for i, m in enumerate(proofs):
        clock = '0' if i == 0 else f'{i}/64'
        lines.extend([f'  refine cons_bounds {i} ?_ ?_',
                      f'  · rw [show (({i}:ℕ):ℝ)/64 = {clock} by norm_num]',
                      f'    with_unfolding_all exact {m}.field_bounds'])
    lines.extend(['  trivial',
                  f'theorem exists_nested_prefix : Passage {n} exitState rows := passage checked field_bounds',
                  '/-- Uniform numerator bounding all Python-proposed physical outgoing radii. -/',
                  f'def maximumRadius : ℕ := {maximum}',
                  'theorem radius_bound {r : Step} (h : r ∈ rows) : r.physicalOut ≤ maximumRadius := by',
                  '  have all : rows.all (fun e => e.physicalOut.ble maximumRadius) = true := by',
                  '    with_unfolding_all rfl',
                  '  exact Nat.ble_eq.mp ((List.all_eq_true.mp all) r h)',
                  'theorem uniform_tube_error {path : ℝ → Plane}',
                  '    (inside : ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 rows,',
                  '      ∀ t ∈ Set.Icc slab.start slab.stop, path t ∈ slab.tube t) :',
                  '    ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 rows,',
                  '      ∃ r ∈ rows, ∀ t ∈ Set.Icc slab.start slab.stop,',
                  '        dist (path t) (reference slab.start r t) ≤ maximumRadius / (2 : ℝ)^80 :=',
                  '  tube_error (fun _ h => radius_bound h) inside',
                  'end PlasmaLean.Design.'+name,''])
    return name,'\n'.join(lines),['checked','field_bounds','exists_nested_prefix','radius_bound',
                                   'uniform_tube_error']


def stored(i):
    return f'DommaschkPositionFramesBack.block{i//16}[{i%16}]'


def union(cache,packages):
    root = cache/'imports'/key_of([r['key'] for _,r in packages])
    root.mkdir(parents=True,exist_ok=True)
    with (root/'lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        for base, r in packages:
            for rel in r['artifacts']:
                p = Path(rel)
                if '.olean' not in p.suffixes or p.parts[0] == 'PlasmaLean':
                    continue
                link = root/p
                link.parent.mkdir(exist_ok=True)
                if link.is_symlink():
                    if link.resolve(strict=True) != (base/p).resolve():
                        raise ValueError(f'conflicting import {p}')
                else:
                    link.symlink_to((base/p).resolve())
    return root


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--length',type=int,default=3)
    parser.add_argument('--shared-from',type=int,default=16)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/backward-physical')
    parser.add_argument('--jacobian-cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    parser.add_argument('--residual-cache',type=Path,default=ROOT/'.lake/trace-residual')
    parser.add_argument('--wait-seconds',type=int,default=0)
    parser.add_argument('--output',type=Path)
    a = parser.parse_args()
    if not 3 <= a.length <= 391:
        parser.error('length must be in [3,391]')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    subprocess.run(['lake','build','--no-build',*['PlasmaLean.Design.'+m
                    for m in (*STATIC,'DommaschkBackwardPrefixRadius')]],
                   cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    version = lake('lean','--version')
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    cache = a.cache.resolve()
    packet = json.loads(gzip.decompress(RECORD.read_bytes()))
    back,fwd = [trace['steps'] for trace in packet['traces']]
    checksum = digest(RECORD)
    common = [checksum,version,[(m,digest(DESIGN/(m+'.trace'))) for m in STATIC],
              digest(ROOT/'.lake/build/lib/lean/PlasmaLean/Certificates/PositionFrameProjection.trace')]
    packages, proof_keys = [], []
    for job in jobs(RECORD,8,False):
        _,direction,i,*_ = job
        if direction != 1 or not 2 <= i < a.length:
            continue
        deadline = time.monotonic()+a.wait_seconds
        if i in TRACKED_PANEL_ROWS:
            jac = tracked_jacobian(TRACKED_PANEL_ROWS[i],checksum,version)
        else:
            jm = emit_jacobian(i,shared=True) if i >= a.shared_from else emit_jacobian(i)
            info = upstream(a.jacobian_cache.resolve(),list(jm.items()),'verify_sparse_forward_jacobians.py',
                            checksum,version,JACOBIAN_PACKAGE)
            jac = accepted(info,i,deadline)
        res = upstream(a.residual_cache.resolve(),list(emit_selected([job])),'verify_sparse_reference_slabs.py',
                       checksum,version,'TraceCache')
        parents = [jac,accepted(res,i,deadline)]
        ref = f'DommaschkReflectedBack{i:03}'
        row = f'DommaschkPhysicalBackward{i:03}'
        declarations = [(ref,render(RECORD,i,'TraceCache'),['exact_pair','forward_sharp','physical_defect'])]
        jac_name = jac[1]['module']
        source = TEMPLATE.read_text().replace('public import JacobianTraceCache.',
                                              'public import '+jac[1].get('package',JACOBIAN_PACKAGE)+'.')
        if i in TRACKED_PANEL_ROWS:
            rate = backward_rate(i,fwd[i-1]['frame_end'],fwd[i],jac_name,back[i]['log_norm_upper'])
            declarations.append(rate)
            source = source.replace('module\n',f'module\n\npublic import {PACKAGE}.{rate[0]}\n',1)
            source = source.replace('${jac}.logNorm',rate[0]+'.rate')
            source = source.replace('${jac}.physical_clock_log_norm',rate[0]+'.physical_clock_log_norm')
        source = Template(source).substitute(name=row,reflected=ref,jac=jac_name,index=i,end=i+1,
                                             offset=2*i+1,radius=fwd[i]['physical_trial_radius'],
                                             stored=stored(i),previous=stored(i-1))
        declarations.append((row,source,['projections','checked','field_bounds','physical_step']))
        result = compile_modules(cache/row,declarations,[d for d,_ in parents],
                                 [common,[(r['key'],r['artifacts']) for _,r in parents]],a)
        packages.extend([*parents,result])
        proof_keys.append(result[1]['key'])
        print(f'verified backward physical row {i}: {result[1]["key"][:12]}',flush=True)
    overlay = union(cache,packages)
    maximum = max(row['physical_radius_out'] for row in back[:a.length])
    declaration = prefix_source(a.length,maximum)
    extra = digest(DESIGN/'DommaschkBackwardPrefixRadius.trace')
    root,result = compile_modules(cache/declaration[0],[declaration],[overlay],
                                  [common,proof_keys,'BackwardPrefixCache',extra],a,'BackwardPrefixCache')
    public = {k:v for k,v in result.items() if k != 'artifacts'}
    public.update(length=a.length,direction=-1,packet_sha256=checksum,maximum_radius_numerator=maximum,
                  coordinate_denominator=2**80,row_keys=proof_keys,import_paths=[str(root),str(overlay)])
    if a.output:
        save(a.output,public)
    print(json.dumps(public),flush=True)


if __name__ == '__main__':
    main()
