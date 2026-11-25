"""Serve one requested row from a shared group while idle producer slots can prepare later groups."""
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from plan_grouped_central_defects import MARKER,validate
from verify_physical_trace_slabs import HERE,ROOT,digest,save


def dispatch(args, *, marker_name=MARKER, labels=('q0r523','q0r531'), check_plan=validate,
             producer='verify_grouped_central_defects.py'):
    output=args.output
    i,label=args.row,args.endpoint
    if (label not in labels or output.parent.name!='references' or
            output.name!=f'{i:03}.json' or output.parent.parent.name!=label):
        return False
    campaign=output.parent.parent
    marker=campaign/marker_name
    if not marker.exists():
        return False
    plan=json.loads(marker.read_text())
    check_plan(plan,label)
    checksum=plan['packet_sha256']
    if output.exists():
        from verify_endpoint_trace_campaign import records_for
        return i in records_for(output,'references',label,checksum)
    groups=plan['groups']
    ordinal=next(j for j,g in enumerate(groups) if g['start']<=i<g['stop'])
    if groups[ordinal]['mode']=='singleton':
        return False
    state=json.loads((campaign/'status.json').read_text())
    if state['endpoint']!=label or state['packet_sha256']!=checksum:
        raise ValueError('grouped reference request does not match the live physical campaign')
    target=state['target_length_each_way']
    work=campaign/'grouped-central'/digest(marker)
    work.mkdir(parents=True,exist_ok=True)
    slots=max(1,state.get('worker_target',1))
    for j in range(ordinal,min(len(groups),ordinal+slots+1)):
        g=groups[j]
        a,b=g['start'],g['stop']
        if g['mode']!='grouped' or a>=target:
            continue
        failed=work/f'{a:03}-{b:03}.failed.json'
        if failed.exists() and time.time()-failed.stat().st_mtime<1800:
            if j==ordinal:
                return False
            continue
        with (work/f'{a:03}-{b:03}.lock').open('a') as lock:
            try:
                fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                continue
            if output.exists():
                break
            missing=[k for k in range(max(1,a),min(target,b))
                     if not (campaign/'references'/f'{k:03}.json').exists()]
            if not missing:
                continue
            # A fresh group with only one needed original row costs more than the singleton.
            if len(missing)==1:
                if j==ordinal:
                    return False
                continue
            log=work/f'{a:03}-{b:03}.log'
            group_out=work/f'{a:03}-{b:03}.json'
            cmd=[sys.executable,HERE/producer,'--endpoint',label,
                 '--span',str(a),str(b),'--handoff',campaign,'--output',group_out]
            with log.open('a') as handle:
                rc=subprocess.run(cmd,cwd=ROOT,stdout=handle,stderr=subprocess.STDOUT,
                    env={**os.environ,'LEAN_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}).returncode
            if rc:
                save(failed,dict(start=a,stop=b,code=rc,log=str(log)))
                print(f'Group {a}:{b} deferred after a failed proof. Individual physical checks continue.',flush=True)
                if j==ordinal:
                    return False
            if output.exists():
                break
    if not output.exists():
        g=groups[ordinal]
        lockfile=work/f'{g["start"]:03}-{g["stop"]:03}.lock'
        with lockfile.open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_SH)
    if not output.exists():
        return False
    from verify_endpoint_trace_campaign import records_for
    return i in records_for(output,'references',label,checksum)
