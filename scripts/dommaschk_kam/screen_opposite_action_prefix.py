"""Export the two physical opposite-section trajectories and find a strictly interior action floor."""
import argparse
from fractions import Fraction as F
import gzip
from itertools import islice
import json
from pathlib import Path

from bounce_action_pilot import S, TARGET, integrate_segment
from bounce_common_section import common_section_inputs
from bounce_frame_witness import encode_step
from bounce_mirror_pilot import HEIGHTS, SCALE
from bounce_phase_frame import FRAME_SCALE, framed_segments
from bounce_phase_strength import ShiftedStrength
from bounce_screen import FIELD_FILE_SHA, SEEDS
from verify_physical_trace_slabs import save

STEP = F(1,64)
RADIUS = F(47,100)
WIDTH = F(1,2**19)
PANELS = 24
COUNT = 392
LIMIT = 330


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    inputs,transfer=common_section_inputs(WIDTH,F(0),RADIUS,1)
    data,seed=inputs[:2]
    shifted=ShiftedStrength(data)
    traces=[]
    for sign in (-1,1):
        rows=[]
        gen=framed_segments(*inputs,sign,STEP,COUNT,F(0),
                            record=lambda checked,end: rows.append(encode_step(checked,end)))
        for seg in islice(gen,LIMIT):
            tube,angles,values=seg.fields(data)
            gap=shifted.numerators(tube,angles,values,HEIGHTS[1:])[0]
            row_mass=integrate_segment(tube[0],values,HEIGHTS[1:],PANELS,[-gap])[0]
            rows[-1]['lower_sum']=row_mass.lo
            rows[-1]['upper_gap']=str(gap.bound()[1])
        traces.append(dict(direction=sign,steps=rows))
        print('evaluated',sign,len(rows),flush=True)
    tot=0
    threshold=TARGET*PANELS*S/STEP
    prefix=None
    for n,(back,front) in enumerate(zip(*[t['steps'] for t in traces],strict=True),1):
        tot+=back['lower_sum']+front['lower_sum']
        if prefix is None and tot>threshold:
            prefix=n
            before=tot-back['lower_sum']-front['lower_sum']
            trial=tot
    if prefix is None or any(F(s['upper_gap'])>=0 for t in traces for s in t['steps'][:prefix]):
        raise ValueError('no strict incoming subwell crosses target')
    packet=dict(section_in_half_pi=1,launch_u=str(RADIUS),birth_phase_half_width=str(WIDTH),
                coordinate_denominator=SCALE,frame_denominator=FRAME_SCALE,step=str(STEP),
                proposal_count=COUNT,slabs_per_direction=LIMIT,panels_per_step=PANELS,transfer=transfer,
                seed_center_radius=[[m.a[0],m.e] for m in seed],traces=traces,
                field_sha256=FIELD_FILE_SHA,seed_sha256={k:x[1] for k,x in SEEDS.items()})
    packed=gzip.compress(json.dumps(packet,separators=(',',':')).encode(),mtime=0)
    a.packet.write_bytes(packed)
    from hashlib import sha256
    result=dict(packet_sha256=sha256(packed).hexdigest(),prefix=prefix,panel_count=2*prefix*PANELS,
                height=str(HEIGHTS[1]),target=str(TARGET),lower=str(trial*STEP/(PANELS*S)),
                previous=str(before*STEP/(PANELS*S)),full=str(tot*STEP/(PANELS*S)),
                upper_gap=str(max(F(s['upper_gap']) for t in traces for s in t['steps'][:prefix])))
    save(a.output,result)
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
