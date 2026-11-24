"""Choose the first overlap of the original and coarse signed action proofs and join them."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

from verify_physical_trace_slabs import ROOT,save


def frontiers(fine,coarse):
    inner=next((i for i in range(322) if not (fine/'rows'/f'{i:03}.json').is_file()),322)
    outer=next((i+1 for i in reversed(range(325)) if not (coarse/'rows'/f'{i:03}.json').is_file()),0)
    return inner,outer


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for k in ['packet','band','well','output']:
        p.add_argument('--'+k,type=Path,required=True)
    p.add_argument('--signed',type=Path)
    p.add_argument('--fine',type=Path,default=ROOT/'.lake/secondary-lower-action')
    p.add_argument('--coarse',type=Path,default=ROOT/'.lake/coarse-secondary-lower')
    p.add_argument('--work',type=Path,default=ROOT/'.lake/coarse-secondary-meeting')
    p.add_argument('--wait',action='store_true')
    p.add_argument('--readiness-only',action='store_true',help='stop after locating the meeting point')
    a=p.parse_args()
    a.work.mkdir(parents=True,exist_ok=True)
    inner,outer=frontiers(a.fine,a.coarse)
    while a.wait and inner<outer:
        time.sleep(30)
        inner,outer=frontiers(a.fine,a.coarse)
    if inner<outer or inner==0:
        p.error(f'fine outward rows end at {inner-1} and the uninterrupted outer coarse ring starts at {outer}')
    # Prefer a prior native tree inside this overlap. This can reuse dozens of audited
    # composition nodes and lets a new proof build retain its chosen cut on replay.
    dest=a.work/'cut.json'
    if dest.exists():
        size=json.loads(dest.read_text())['pairs']
        if not outer<=size<=inner:
            p.error('saved meeting point is no longer backed by the signed rows')
    else:
        center_candidates=(ROOT/'.lake/secondary-lower-cover/checkpoints').glob('core???-*.json')
        existing=sorted({int(t.name[4:7]) for t in center_candidates if outer<=int(t.name[4:7])<=inner})
        size=existing[0] if existing else max(1,outer)
        save(dest,dict(pairs=size,native_ready=inner,coarse_first=outer))
    if a.readiness_only:
        print(f'physical action fronts meet at {size}',flush=True)
        return
    def execute(cmd,options):
        subprocess.run([sys.executable,str(Path(__file__).parent/cmd),*map(str,options)],check=True,cwd=ROOT)
    suffix=f'{size:03}'
    fine=a.work/f'native{suffix}.json'
    center=a.work/f'coarse{suffix}.json'
    execute('verify_secondary_action_cover.py',['--band',a.band,'--pairs',size,'--row-cache',a.fine,'--output',fine])
    execute('verify_coarse_native_center.py',['--packet',a.packet,'--native-cover',fine,'--output',center])
    params=['--packet',a.packet,'--band',a.band,'--pairs',325,'--row-cache',a.coarse,
            '--native-center',center,'--output',a.output]
    if a.signed:
        if not a.signed.exists():
            p.error('the full coarse cover can be checked without --signed until the actual 328-row prefix is ready')
        params.extend(['--signed',a.signed,'--well',a.well])
    execute('verify_coarse_secondary_cover.py',params)


if __name__=='__main__':
    main()
