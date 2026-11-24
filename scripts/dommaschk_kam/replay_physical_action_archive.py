"""Replay each original Q0R470 quadrature record from its recorded physical trajectory tube."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS, MirrorSegment, polynomial_data
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import panel_row
from emit_sparse_taylor_slab import RECORD
from screen_physical_action_panels import packed_rows
from verify_physical_trace_slabs import digest, save


def segment(trace,i):
    row=trace['steps'][i]
    return MirrorSegment(i,trace['direction'],F(1,64),F(0),row['coefficients'],
                         0,row['physical_radius_out'],row['physical_trial_radius'],F(0))


def replay():
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    if (packet['section_in_half_pi'],packet['launch_u'],packet['step'])!=(0,'47/100','1/64'):
        raise ValueError('unexpected trajectory')
    data=polynomial_data()
    strength=ShiftedStrength(data)
    original=packed_rows()
    cells=0
    for trace in packet['traces']:
        back=trace['direction']==-1
        for i in range(325):
            row=segment(trace,i)
            packed,_=panel_row(row,data,strength,HEIGHTS[1],True,48)
            expected=original[324-i if back else 325+i]
            if expected!=packed:
                raise ValueError(f'physical row {i}, sign {trace["direction"]}: packed columns differ')
            cells+=48
    return {'trajectory_sha256':digest(RECORD),'slabs':len(original),'cells':cells,
            'directions':[-1,1],'bits_per_cell':72,'height':str(HEIGHTS[1]),
            'archived_packed_integers_reproduced':True}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    report=replay()
    print(json.dumps(report))
    if args.output:
        save(args.output,report)
