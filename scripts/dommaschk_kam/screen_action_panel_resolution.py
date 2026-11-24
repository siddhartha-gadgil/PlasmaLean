"""Evaluate coarse action panels on the actual signed position tubes at the eight QA2R endpoints."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import re

from bounce_common_section import section_polynomial_data
from bounce_mirror_pilot import HEIGHTS
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import PANELS, SPATIAL, TARGET, panel_row
from replay_physical_action_archive import segment
from verify_common_endpoint_traces import ENDPOINTS
from verify_physical_trace_slabs import RECORD, ROOT, digest, save


DENOM = 64 * PANELS * SPATIAL**2
PACKED = re.compile(r'^  ⟨0x([0-9a-fA-F]+), (\d+), rfl⟩',re.M)


def endpoint_inputs(endpoint):
    section,radius = int(endpoint[1]),int(endpoint[3:])
    path = RECORD.with_name(f'bounce_frame_q{section}_u{radius}.json.gz')
    src = ROOT/'PlasmaLean/Design'/('DommaschkAction'+endpoint.upper()+'.lean')
    packet = json.loads(gzip.decompress(path.read_bytes()))
    code = src.read_text()
    match = re.search(r'checked : Packet (true|false) slabs (\d+) (\d+)',code)
    upper = match[1] == 'true'
    height = F(re.search(r'phys : Covers (?:true|false) w f \((\d+ / \d+)',code)[1].replace(' ',''))
    rows = [(int(word,16),int(mass)) for word,mass in PACKED.findall(code)]
    counts = [int(match[i]) for i in (2,3)]
    if (packet['section_in_half_pi'] != section or F(packet['launch_u']) != F(radius,1000)
            or F(packet['step']) != F(1,64) or [tr['direction'] for tr in packet['traces']] != [-1,1]
            or height not in HEIGHTS or len(rows) != sum(counts)):
        raise ValueError(f'inconsistent original action inputs at {endpoint}')
    return upper,height,counts,rows,packet['traces'],digest(path),digest(src)


def screen(endpoint, splits, *, groups=None):
    upper,h,counts,original,traces,packet_key,action_key = endpoint_inputs(endpoint)
    data = section_polynomial_data(int(endpoint[1]))
    field = ShiftedStrength(data)
    sums = {m:[] for m in splits}
    for trace, count in zip(traces,counts,strict=True):
        direction = trace['direction']
        for i in range(count):
            if trace['steps'][i]['index'] != i:
                raise ValueError(f'nonconsecutive slab on the {direction} branch at {i}')
            slab = segment(trace,i)
            if i in {0,count//2,count-1}:
                j = counts[0]-1-i if direction == -1 else counts[0]+i
                if panel_row(slab,data,field,h,upper,PANELS) != original[j]:
                    raise ValueError(f'incorrect physical angle or archive at {endpoint} {direction} {i}')
            for m in splits:
                word,mass = panel_row(slab,data,field,h,upper,m)
                sums[m].append(mass)
                if groups is not None:
                    groups[m][int(direction == 1)].append((word,mass))
    if groups is not None:
        for negative,_ in groups.values():
            negative.reverse()
    margins = {}
    for m,blocks in sums.items():
        value = F(sum(blocks),DENOM)
        margin = TARGET-value if upper else value-TARGET
        margins[m] = dict(action=str(value),margin=str(margin),accepted=margin>0,
                          panels=m*sum(counts))
    return dict(endpoint=endpoint,upper=upper,height=str(h),target=str(TARGET),counts=counts,
                packet_sha256=packet_key,action_sha256=action_key,original_samples=6,coarse=margins)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--endpoints',nargs='+',choices=ENDPOINTS,default=ENDPOINTS)
    parser.add_argument('--splits',nargs='+',type=int,choices=(1,2,3,4,6,8,12,16,24,48),default=[2])
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    reports=[]
    for endpoint in args.endpoints:
        rec=screen(endpoint,args.splits)
        reports.append(rec)
        print(endpoint,rec['coarse'],flush=True)
        save(args.output,reports)


if __name__=='__main__':
    main()
