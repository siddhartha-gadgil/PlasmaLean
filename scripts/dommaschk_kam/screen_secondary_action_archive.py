"""Exactly replay all signed density, squared-speed and speed columns of the Q0R478 lower packet."""
import argparse
from dataclasses import replace
from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path
import re

from bounce_mirror_pilot import HEIGHTS, polynomial_data
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import TARGET, panel_row
from replay_physical_action_archive import segment
from verify_physical_trace_slabs import ROOT, digest, save
from verify_secondary_mirror_caps import load


COUNT = 327
ARCHIVE = ROOT/'PlasmaLean/Design/DommaschkActionQ0R478.lean'


@lru_cache(maxsize=1)
def archive():
    source=ARCHIVE.read_text()
    rows=[(int(x,16),int(m)) for x,m in re.findall(r'^  ⟨0x([0-9a-fA-F]+), (\d+), rfl⟩',source,re.M)]
    if len(rows)!=2*COUNT or 'theorem checked : Packet false slabs 327 327' not in source:
        raise ValueError('wrong direction or block count in the original lower action archive')
    return rows


def screen():
    _,packet,traces,_=load(478)
    data=polynomial_data()
    model=ShiftedStrength(data)
    records=archive()
    counts={'individual':0,'paired':0}
    different=[]
    mask=2**72-1
    for i in range(COUNT):
        b,f=(segment(t,i) for t in traces)
        common=replace(f,outgoing_radius=max(b.outgoing_radius,f.outgoing_radius))
        common_row,_=panel_row(common,data,model,HEIGHTS[1],False,48)
        for j,row in [(COUNT-1-i,b),(COUNT+i,f)]:
            word,mass=panel_row(row,data,model,HEIGHTS[1],False,48)
            if (word,mass)!=records[j]:
                raise ValueError(f'original signed trajectory differs from action archive at chronological row {j}')
            counts['individual']+=48
            for n in range(48):
                expected=word >> (72*(47-n if row.sign<0 else n)) & mask
                observed=common_row >> (72*n) & mask
                if expected!=observed:
                    different.append([i,row.sign,n])
                else:
                    counts['paired']+=1
    mass=F(sum(m for _,m in records),3072*2**40)
    subtotal=0
    for count in range(1,COUNT+1):
        previous=subtotal
        subtotal+=records[COUNT-count][1]+records[COUNT+count-1][1]
        if F(subtotal,3072*2**40)>TARGET:
            break
    else:
        raise ValueError('the entire lower packet misses the target')
    return dict(endpoint='q0r478',direction='lower',height=str(HEIGHTS[1]),target=str(TARGET),
                mass=str(mass),excess=str(mass-TARGET),slabs_per_direction=COUNT,
                first_symmetric_count=count,first_symmetric_mass=str(F(subtotal,3072*2**40)),
                previous_mass=str(F(previous,3072*2**40)),
                original_cells=counts['individual'],identical_paired_cells=counts['paired'],
                unequal_paired_cells=different,packet_sha256=digest(packet),archive_sha256=digest(ARCHIVE))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    report=screen()
    save(args.output,report)
    print(json.dumps({k:v for k,v in report.items() if k!='unequal_paired_cells'}))
    print('unequal paired cells:', len(report['unequal_paired_cells']))
    if report['unequal_paired_cells']:
        raise SystemExit(1)
