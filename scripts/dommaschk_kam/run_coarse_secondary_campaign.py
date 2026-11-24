"""Check Q0R478 coarse rows from the outside inward, sharing already proved fine rows."""
import argparse
import json
from pathlib import Path
from types import SimpleNamespace

from verify_coarse_action_models import env
from verify_coarse_lower_transfer import transfer
from verify_coarse_secondary_lower import packet_inputs, verify
from verify_mirror_physical_hit import admitted
import verify_native_action_models as native
from verify_physical_trace_slabs import ROOT, save


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--first',type=int,default=0)
    p.add_argument('--last',type=int,default=324)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-action-profiles')
    p.add_argument('--model-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--fine-cache',type=Path,default=ROOT/'.lake/secondary-lower-action')
    p.add_argument('--cell-cache',type=Path,default=ROOT/'.lake/coarse-secondary-lower')
    a=p.parse_args()
    pack,root,traces,blocks,n,mass=packet_inputs(a.packet)
    if not 0<=a.first<=a.last<n:
        p.error(f'target-crossing proof rows lie between 0 and {n-1}')
    env(a)
    (a.cell_cache/'rows').mkdir(parents=True,exist_ok=True)
    data=native.static_data()
    static=native.verify_static(SimpleNamespace(**{**vars(a),'cache':a.model_cache,'fields':range(4)}),data)
    completed={}
    for i in range(a.last,a.first-1,-1):
        dest=a.cell_cache/'rows'/f'{i:03}.json'
        if dest.exists():
            rows=json.loads(dest.read_text())
        elif (a.fine_cache/'rows'/dest.name).is_file():
            rows=transfer(a,pack,root,blocks,i)
        else:
            rows=verify(i,a,pack,root,traces,blocks,data,static)
        if sorted((r['index'],r['direction'],r['coarse_packet']) for r in rows)!=[
                (i,-1,pack['key']),(i,1,pack['key'])]:
            raise ValueError(f'wrong signed proof receipt for outward row {i}')
        for r in rows:
            admitted(Path(r['import_paths'][0]),r['module'],r['key'])
        completed[i]=dict(source=str(dest),mode='fine' if 'native' in rows[0] else 'direct',
                          signed_keys=[r['key'] for r in rows])
        save(a.output,dict(endpoint='q0r478',target_pairs=n,core_mass=str(mass),
                           requested=[a.first,a.last],completed=completed,physical_cells=96*len(completed),
                           finished=(i==a.first)))


if __name__=='__main__':
    main()
