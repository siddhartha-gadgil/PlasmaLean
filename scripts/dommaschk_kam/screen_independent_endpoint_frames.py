"""Test each signed frame on its own reflected spatial matrix, including nonconjugate endpoints."""

import argparse
from dataclasses import replace
from fractions import Fraction as F
import gzip
import json
from pathlib import Path

from endpoint_reflected_trials import TrialPair
from screen_endpoint_jacobian_sharing import NEIGHBOURS, first_failure, harmonic_jet, joint_models, own_models
from screen_projected_jacobians import projected_radii
from screen_reflected_reference import conjugate
from verify_physical_trace_slabs import RECORD


def trial_frames(path, lo, hi):
    with gzip.open(path,'rt') as handle:
        packet = json.load(handle)
    trace = {t['direction']: t['steps'] for t in packet['traces']}
    den = packet['frame_denominator']
    unit = [[den,0],[0,den]]
    for i in range(lo,hi+1):
        f,b = trace[1][i],trace[-1][i]
        lf,lb = (trace[s][i-1]['frame_end'] if i else unit for s in (1,-1))
        fr,br = (projected_radii(l,r['frame_end'],r['frame_trial_radius']) for l,r in ((lf,f),(lb,b)))
        gap = tuple(sum(abs(a-s*c) for a,c in zip(p,q,strict=True)) for p,q,s in
                    zip(f['coefficients'],b['coefficients'],(1,-1),strict=True))
        widths = tuple(max(a,b+c) for a,b,c in zip(fr,br,gap,strict=True))
        original = TrialPair(i,lf,f,lb,b,fr,br,gap,widths,F(f['log_norm_upper']))
        reflected = replace(original,forward_left=conjugate(lb),forward={**f,'frame_end':conjugate(b['frame_end'])},
                            common_rate=F(b['log_norm_upper']))
        yield original,reflected


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--range',type=int,nargs=2,default=[0,390])
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    lo,hi = args.range
    if not 0<=lo<=hi<=390:
        p.error('indices must lie between 0 and 390')
    rows = []
    for e,f in NEIGHBOURS:
        groups = [trial_frames(RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz'),lo,hi)
                  for label in (e,f)]
        for branches in zip(*groups,strict=True):
            sec,i = int(e[1]),branches[0][0].index
            own = [own_models(x[0]) for x in branches]
            jets = [harmonic_jet(sec,i,x) for x in own]
            shared = harmonic_jet(sec,i,joint_models(*own))
            rows.append({'indices':[e,f,i],
                'conjugate':[a.forward_left==b.forward_left and a.forward['frame_end']==b.forward['frame_end']
                             for a,b in branches],
                'individual_failures':[[first_failure(jet,x) for x in branch]
                                       for jet,branch in zip(jets,branches,strict=True)],
                'shared_failures':[[first_failure(shared,x) for x in branch] for branch in branches]})
    args.output.write_text(json.dumps(rows,indent=2)+'\n')


if __name__ == '__main__':
    main()
