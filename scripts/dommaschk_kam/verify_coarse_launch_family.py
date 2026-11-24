"""Verify opposite-section launch cells and their true birth passages with one active checker."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from verify_physical_trace_slabs import ROOT,save


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packets',type=Path,required=True)
    p.add_argument('--prefixes',type=Path,default=ROOT/'.lake/secondary-trace-campaign')
    p.add_argument('--length',type=int,default=5)
    p.add_argument('--endpoints',nargs='+',choices=['q1r456','q1r464','q1r509','q1r517'],
                   default=['q1r456','q1r464','q1r509','q1r517'])
    p.add_argument('--receipts',type=Path,default=ROOT/'.lake/coarse-action-birth/checkpoints')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    a.receipts.mkdir(parents=True,exist_ok=True)
    reports=[]
    for e in a.endpoints:
        packet=a.packets/(e+'.json')
        prefix=a.prefixes/e/'prefixes'/f'{a.length:03}.json'
        rows=a.receipts/(e+'-rows.json')
        birth=a.receipts/(e+'-birth.json')
        for task,args in [
            ('verify_coarse_physical_action.py',['--row','0','--output',rows]),
            ('verify_coarse_action_birth.py',['--cells',rows,'--signed',prefix,'--output',birth])]:
            subprocess.run([sys.executable,str(Path(__file__).parent/task),'--packet',str(packet),*map(str,args)],
                           check=True,cwd=ROOT)
        result=json.loads(birth.read_text())
        reports.append(dict(endpoint=e,birth=result['key'],source=str(birth),rows=str(rows)))
        save(a.output,dict(requested=a.endpoints,completed=reports,chronological_cells=96*len(reports),
                           independent_panels=24*len(reports),length=a.length))


if __name__=='__main__':
    main()
