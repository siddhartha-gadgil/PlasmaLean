"""Check canonical forward and backward chain segments as their physical row receipts arrive."""
import argparse
import json
from pathlib import Path
import time

from ribbon_central_data import LENGTH, WITNESS_SHA
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import ROOT, save
from verify_ribbon_through_chains import checked_segment


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--packets",required=True,type=Path)
    p.add_argument("--physical",type=Path,default=ROOT/".lake/ribbon-physical-campaign")
    p.add_argument("--cache",type=Path,default=ROOT/".lake/ribbon-through-checks")
    p.add_argument("--output",required=True,type=Path)
    p.add_argument("--from-row",type=int,default=0)
    p.add_argument("--count",type=int,default=LENGTH)
    p.add_argument("--wait",action="store_true")
    a=p.parse_args()
    if not 0<=a.from_row<a.count<=LENGTH or a.from_row%8:
        p.error("start at a canonical eight-row group and use an original exterior index")
    env(a)
    packets=json.loads(a.packets.read_text())
    for k in range(4):
        item=packets[str(k)]
        if (item["module"],item["ribbon"],item["tile"])!=(f"DommaschkRadialRibbonRows{k}",WITNESS_SHA,k):
            raise ValueError(f"different original packet for tile {k}")
        root,=map(Path,item["import_paths"])
        admitted(root,item["module"],item["key"])
    pending=[(k,i,min(i+8,a.count)) for i in range(a.from_row,a.count,8) for k in range(4)]
    done=[]
    checked={}
    while pending:
        found=False
        for k,lo,hi in pending.copy():
            folder=a.physical/f"tile{k}"/"steps"
            if not all((folder/f"{i:03}.json").exists() for i in range(lo,hi)):
                continue
            module,key,root,_=checked_segment(a,k,lo,hi,packets[str(k)],checked)
            result=admitted(root,module,key)
            done.append({"tile":k,"span":[lo,hi],"module":module,"key":key,
                         "kernel_seconds":result["wall_seconds"]})
            pending.remove((k,lo,hi))
            found=True
            save(a.output,{"ribbon":WITNESS_SHA,"from":a.from_row,"count":a.count,
                           "complete":not pending,"segments":done})
        if not found and pending:
            if not a.wait:
                raise RuntimeError(f"{len(pending)} original physical segments are still missing")
            time.sleep(10)


if __name__=="__main__":
    main()
