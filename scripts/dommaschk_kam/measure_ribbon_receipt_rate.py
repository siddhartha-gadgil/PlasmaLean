"""Measure real signed ribbon receipts in two time windows and reauthenticate counted proofs."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path

from ribbon_central_data import WITNESS_SHA,label
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import ROOT, save
from verify_ribbon_central_group import authenticate


def window(low, high, root):
    if not 0 < low < high:
        raise ValueError("invalid timestamp interval")
    result={}
    for kind,folder in [("central","references"),("spatial","jacobians"),("physical","steps")]:
        seen={}
        by_tile=[]
        for k in range(4):
            indices=[]
            for path in sorted((root/f"ribbon-{kind}-campaign"/f"tile{k}"/folder).glob("[0-9]*.json")):
                if not low <= path.stat().st_mtime < high:
                    continue
                i=int(path.stem)
                row=json.loads(path.read_text())
                if kind=="central":
                    authenticate(row,k,i,seen)
                else:
                    if (row["tile"],row["packet_sha256"])!=(k,WITNESS_SHA):
                        raise ValueError(f"wrong original row in {path}")
                    module=row.get("import_module",row["module"])
                    parent=(Path(row["import_paths"][0]),module,row["key"])
                    if parent not in seen:
                        seen[parent]=set(admitted(*parent)["theorems"])
                    if kind=="physical":
                        claims=[f"DommaschkPhysical{label(k).upper()}{d}{i:03}.physical_step"
                                for d in ("Forward","Back")]
                    else:
                        claims=[f"DommaschkJacobian{label(k).upper()}PairedForward{i:03}.physical_clock_log_norm"]
                    if any("PlasmaLean.Design."+t not in seen[parent] for t in claims):
                        raise ValueError(f"missing real {kind} claim in {path}")
                indices.append(i)
            by_tile.append(indices)
        count=sum(map(len,by_tile))
        result[kind]={"tile_indices":by_tile,"row_pairs":count,"pairs_per_hour":3600*count/(high-low)}
    fmt=lambda t: datetime.fromtimestamp(t,timezone.utc).isoformat()
    return {"start_utc":fmt(low),"end_utc":fmt(high),"seconds":high-low,**result}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--before-end",type=float,required=True,help="Unix seconds, exclusive")
    p.add_argument("--after-start",type=float,required=True,help="Unix seconds, inclusive")
    p.add_argument("--seconds",type=float,required=True)
    p.add_argument("--lake",type=Path,default=ROOT/".lake")
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    if not 0<a.seconds or a.before_end>a.after_start or a.after_start+a.seconds>datetime.now().timestamp():
        p.error("give two elapsed nonoverlapping windows of equal positive length")
    before=window(a.before_end-a.seconds,a.before_end,a.lake)
    after=window(a.after_start,a.after_start+a.seconds,a.lake)
    report={"witness":WITNESS_SHA,"before":before,"after":after}
    save(a.output,report)
    print(json.dumps({tag:{k:r[k]["row_pairs"] for k in ("central","spatial","physical")}
                      for tag,r in [("before",before),("after",after)]}))


if __name__=="__main__":
    main()
