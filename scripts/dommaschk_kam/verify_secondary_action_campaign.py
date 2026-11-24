"""Attach the second launch's lower-action checkpoints as their physical prerequisites arrive."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

from verify_physical_trace_slabs import ROOT, save


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--band',type=Path,required=True)
    p.add_argument('--prefix-dir',type=Path,default=ROOT/'.lake/secondary-trace-campaign/q0r478/prefixes')
    p.add_argument('--row-cache',type=Path,default=ROOT/'.lake/secondary-lower-action')
    p.add_argument('--reports',type=Path,default=ROOT/'.lake/secondary-lower-cover/checkpoints')
    p.add_argument('--checkpoints',type=int,nargs='+',default=[16,32,64,128,256,322])
    p.add_argument('--poll-seconds',type=int,default=45)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    steps=sorted(set(a.checkpoints))
    if any(not 1<=k<=322 for k in steps) or not 1<=a.poll_seconds<=3600:
        p.error('choose checkpoint sizes from 1 to 322 and a positive polling interval')
    a.reports.mkdir(parents=True,exist_ok=True)
    covered={}
    attached={}
    original=Path(__file__).parent
    def check(name,args):
        subprocess.run([sys.executable,str(original/name),'--band',str(a.band),*map(str,args)],
                       check=True,cwd=ROOT)
    def emit():
        save(a.output,dict(requested=steps,covered=covered,attached=attached,complete=False))
    emit()
    while len(attached)<len(steps):
        sizes=sorted(int(x.stem) for x in a.prefix_dir.glob('[0-9][0-9][0-9].json'))
        for k in steps:
            if k in attached:
                continue
            if not all((a.row_cache/'rows'/f'{i:03}.json').is_file() for i in range(k)):
                continue
            # Use the first existing prefix extending past both endpoints. At the final
            # checkpoint a single prefix must extend beyond the actual two first contacts.
            length=next((n for n in sizes if n>(327 if k==322 else k)),None)
            if k in covered and length is None:
                continue
            suffix='cover' if length is None else f'birth{length:03}'
            target=a.reports/f'core{k:03}-{suffix}.json'
            params=['--pairs',k,'--row-cache',a.row_cache,'--output',target]
            if length is not None:
                params.extend(['--signed',a.prefix_dir/f'{length:03}.json'])
            check('verify_secondary_action_cover.py',params)
            checked=json.loads(target.read_text())
            covered[k]=dict(key=checked['key'],report=str(target),physical_cells=96*k)
            if length is not None:
                attached[k]=dict(key=checked['birth']['key'],signed_length=length,report=str(target))
            emit()
        if len(attached)<len(steps):
            time.sleep(a.poll_seconds)
    final=None
    if 322 in attached:
        target=a.reports/'first-well.json'
        length=attached[322]['signed_length']
        check('verify_secondary_first_well_action.py',[
            '--cover',attached[322]['report'],'--signed',a.prefix_dir/f'{length:03}.json','--output',target])
        m=json.loads(target.read_text())
        if not m['complete']:
            raise RuntimeError('the full first-well attachment did not complete')
        final=dict(key=m['birth']['key'],report=str(target))
    save(a.output,dict(requested=steps,covered=covered,attached=attached,first_well=final,complete=True))


if __name__=='__main__':
    main()
