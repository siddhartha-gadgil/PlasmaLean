"""Select group clocks through both archived exterior cap nodes for each physical launch."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS
from verify_grouped_endpoint_jacobians import trial_data
from verify_physical_trace_slabs import RECORD, digest, save
from verify_secondary_mirror_caps import ARCHIVE


LABELS=('q0r523','q0r531','q1r456','q1r464','q1r509','q1r517')


def exterior(label):
    original=json.loads(ARCHIVE.read_text())
    section,=(s for s in original['sections'] if s['section_in_half_pi']==int(label[1]))
    entry,=(r for r in section['endpoints'] if Fraction(r['launch_radius'])==Fraction(int(label[3:]),1000))
    if list(map(Fraction,entry['heights']))!=list(HEIGHTS):
        raise ValueError(f'equatorial and action archive heights differ at {label}')
    brackets={}
    for crossing in entry['crossings']:
        sign=crossing['direction']
        if sign in brackets or sign not in (-1,1) or not crossing['success'] or len(crossing['brackets'])!=2:
            raise ValueError(f'invalid signed crossings at {label}')
        indices=[[64*Fraction(t) for t in pair] for pair in crossing['brackets']]
        if not all(0<a<b<=391 and a.denominator==b.denominator==1 for a,b in indices):
            raise ValueError(f'missing a physical grid endpoint at {label}')
        brackets[sign]=[[int(a),int(b)] for a,b in indices]
    if set(brackets)!={-1,1}:
        raise ValueError(f'missing one direction at {label}')
    return brackets,max(b for pairs in brackets.values() for _,b in pairs)


def groups(label,start,stop):
    _,_,_,_,failures=trial_data(label,start,stop)
    if not failures or stop-start==1:
        return [dict(start=start,stop=stop,mode='singleton' if failures else 'grouped',failures=failures)]
    middle=(start+stop)//2
    return groups(label,start,middle)+groups(label,middle,stop)


def endpoint_plan(label,max_width):
    brackets,cap=exterior(label)
    stop=cap+1
    if stop>391:
        raise ValueError(f'no archived continuation beyond the final exterior cap at {label}')
    spans=[]
    for i in range(0,stop,max_width):
        spans.extend(groups(label,i,min(i+max_width,stop)))
    return dict(endpoint=label,packet_sha256=digest(RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')),
                target=stop,exterior_node=cap,caps_in_64ths=brackets,spans=spans)


def checked_plan(plan,label):
    spec=plan['endpoints'][label]
    caps,cap=exterior(label)
    checksum=digest(RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz'))
    if (spec['endpoint']!=label or spec['packet_sha256']!=checksum or spec['exterior_node']!=cap or
            spec['target']!=cap+1 or plan['archive_sha256']!=digest(ARCHIVE) or
            {int(k):v for k,v in spec['caps_in_64ths'].items()}!=caps):
        raise ValueError(f'group plan uses different archived caps, packet, or label for {label}')
    at,grouped=0,{}
    for item in spec['spans']:
        a,b=item['start'],item['stop']
        if a!=at or not a<b<=cap+1 or item['mode'] not in ('grouped','singleton'):
            raise ValueError(f'group plan has missing, overlapping or invalid clock indices at {label}')
        if item['mode']=='grouped':
            grouped.update({i:(a,b) for i in range(a,b)})
        at=b
    if at!=cap+1:
        raise ValueError(f'group plan does not continue past the exterior cap at {label}')
    return spec,grouped


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',choices=LABELS,nargs='+',default=LABELS)
    p.add_argument('--max-width',type=int,default=12)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 1<=a.max_width<=64 or len(set(a.endpoints))!=len(a.endpoints):
        p.error('choose unique endpoints and an initial width between 1 and 64')
    result={}
    for label in a.endpoints:
        result[label]=endpoint_plan(label,a.max_width)
        print(label,result[label]['target'],len(result[label]['spans']),'spans',flush=True)
    save(a.output,dict(archive_sha256=digest(ARCHIVE),max_width=a.max_width,endpoints=result))


if __name__=='__main__':
    main()
