"""Write or independently replay the two 391-slab N-60 traces at each listed endpoint.

write uses DOP853 and a matrix exponential to propose dyadic polynomials and
frames. check reads those integers, re-identifies the candidate inputs, checks
the transferred seed and every frame step, and reproduces both archived action
intervals and first-mirror tests. Time is outward geometric angle, with the
local polynomial argument s=2*(abs(phi)/step-index)-1 on each slab. Frame
matrices interpolate linearly in s from the previous endpoint (initially the
identity) to the stored endpoint. The JSON uses exact integers or fractions.

Run with OPENBLAS_NUM_THREADS=1 and the workstation Python environment. The
default is section 0, u=0.470. --all processes all eight archived endpoints.
"""
import argparse
import gzip
import json
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from hashlib import sha256
from itertools import islice
from pathlib import Path
from tempfile import NamedTemporaryFile

from bounce_action_pilot import enclose_action
from bounce_common_section import common_section_inputs, section_polynomial_data, transfer
from bounce_launch_box import TARGET as FIELD_SOURCE
from bounce_mirror_pilot import Model, ORDER, SCALE, angle_models
from bounce_phase_frame import FRAME_SCALE, check_frame_step, framed_segments, norm_upper
from bounce_phase_strength import ShiftedStrength
from bounce_screen import FIELD_FILE_SHA, SEEDS


HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / 'results' / 'bounce_local_graphs_20261123.json'
DEFAULT_WITNESS = HERE / 'results' / 'bounce_frame_q0_u470.json.gz'
STEP = F(1,64)
RADIUS = F(47,100)
PHASE_WIDTH = F(1,4096)
SLABS = 391
# The archived DOP853 fit ran to 49/8 before stopping at the mirrors.
PROPOSAL_COUNT = 392


def archive_endpoint(section=0, radius=RADIUS):
    archive = json.loads(ARCHIVE.read_text())
    source, = [s for s in archive['sections'] if s['section_in_half_pi'] == section]
    matches = [r for r in source['endpoints'] if F(r['launch_radius']) == radius]
    if len(matches) != 1:
        raise ValueError(f'no unique N-60 endpoint at section {section}, radius {radius}')
    record = matches[0]
    if (record['section_in_half_pi'] != section or F(record['phase_half_width']) != PHASE_WIDTH
            or F(record['step']) != STEP or record['trajectory_denominator'] != SCALE
            or record['panels_per_step'] != 48):
        raise ValueError('archived endpoint has different trace parameters')
    if (sha256(Path(FIELD_SOURCE).read_bytes()).hexdigest() != FIELD_FILE_SHA
            or archive['field_file_sha256'] != FIELD_FILE_SHA
            or archive['seed_sha256'] != {tag: entry[1] for tag,entry in SEEDS.items()}):
        raise ValueError('candidate field or seed identifiers differ')
    return record


def header(seed, report, section, radius):
    return {
        'format': 'DommaschkN60Frame/v1',
        'field_sha256': FIELD_FILE_SHA,
        'seed_sha256': {tag: entry[1] for tag,entry in SEEDS.items()},
        'section_in_half_pi': section,
        'launch_u': str(radius),
        'birth_phase_half_width': str(PHASE_WIDTH),
        'step': str(STEP),
        'slabs_per_direction': SLABS,
        'proposal_count': PROPOSAL_COUNT,
        'order': ORDER,
        'coordinate_denominator': SCALE,
        'frame_denominator': FRAME_SCALE,
        'seed_center_radius': [[x.a[0],x.e] for x in seed],
        'transfer': report,
    }


def encode_step(checked, end):
    segment = checked.segment
    return {
        'index': segment.index,
        'coefficients': [list(row) for row in segment.coeffs],
        'frame_end': end,
        'jump': list(checked.jump),
        'jump_norm_upper': checked.jump_upper,
        'frame_radius_in': checked.incoming,
        'frame_radius_out': checked.outgoing,
        'frame_trial_radius': checked.trial,
        'physical_radius_in': segment.incoming_radius,
        'physical_radius_out': segment.outgoing_radius,
        'physical_trial_radius': segment.trial_radius,
        'determinant_lower': str(checked.determinant_lower),
        'frame_norm_upper': str(checked.operator_upper),
        'log_norm_upper': str(checked.log_norm),
        'defect_upper': str(segment.defect),
    }


def verify_archived_prefix(data, traces, report, archived):
    if report != archived['transfer']:
        raise ValueError('transferred birth differs from the archived endpoint')

    def saved_trace(data_arg, seed_arg, proposer, initial, sign, dt, count, jitter, origin):
        if dt != STEP or count != PROPOSAL_COUNT or jitter != 0 or origin:
            raise ValueError('action integration requested a different clock')
        return iter(traces[sign])

    result = enclose_action((data,None,None,None),STEP,48,F(0),PROPOSAL_COUNT*STEP,
                            ShiftedStrength(data),segment_builder=saved_trace)
    for key,value in result.items():
        # The archive replaced the two-height straddle test with the single
        # directed sign appropriate to this endpoint.
        if key != 'straddles' and value != archived[key]:
            raise ArithmeticError(f'replayed endpoint disagrees with archived {key}')


def generate(section=0, radius=RADIUS):
    archived = archive_endpoint(section,radius)
    inputs,report = common_section_inputs(PHASE_WIDTH,F(0),radius,section)
    data,seed,_,_ = inputs
    packet = header(seed,report,section,radius)
    packet['traces'] = []
    traces = {}
    for sign in (-1,1):
        rows = []
        trace = framed_segments(*inputs,sign,STEP,PROPOSAL_COUNT,F(0),
                                record=lambda checked,end: rows.append(encode_step(checked,end)))
        traces[sign] = list(islice(trace,SLABS))
        if len(rows) != SLABS:
            raise ArithmeticError('short proposal trace')
        packet['traces'].append({'direction': sign, 'steps': rows})
    verify_archived_prefix(data,traces,report,archived)
    return packet


def integer_matrix(value, columns):
    if (type(value) is not list or len(value) != 2 or any(
            type(row) is not list or len(row) != columns or
            any(type(x) is not int for x in row) for row in value)):
        raise ValueError(f'expected a 2-by-{columns} integer matrix')
    return value


def same_record(left, right):
    # JSON distinguishes integers from rounded floats and from booleans.
    # Python's numeric structural equality would accept 1.0 and True for 1.
    return json.dumps(left,sort_keys=True) == json.dumps(right,sort_keys=True)


def replay(packet, section=None, radius=None):
    section = packet['section_in_half_pi'] if section is None else section
    radius = F(packet['launch_u']) if radius is None else radius
    if type(section) is not int or section not in (0,1):
        raise ValueError('expected an integer symmetry-section index')
    archived = archive_endpoint(section,radius)
    data = section_polynomial_data(section)
    seed,report = transfer(PHASE_WIDTH,F(0),radius,section)
    if not same_record({k:v for k,v in packet.items() if k != 'traces'},header(seed,report,section,radius)):
        raise ValueError('trace parameters, transfer or initial ball changed')
    if not same_record([part['direction'] for part in packet['traces']],[-1,1]):
        raise ValueError('one trace in each outward direction required')
    traces = {}
    for part in packet['traces']:
        sign = part['direction']
        if len(part['steps']) != SLABS:
            raise ValueError('wrong number of consecutive slabs')
        previous = [x.a[0] for x in seed]
        radius = norm_upper(x.e for x in seed)
        start = [[FRAME_SCALE,0],[0,FRAME_SCALE]]
        trace = []
        for i,row in enumerate(part['steps']):
            coeffs = integer_matrix(row['coefficients'],ORDER+1)
            end = integer_matrix(row['frame_end'],2)
            nominal = [Model(coeff) for coeff in coeffs]
            angles = angle_models(sign*(i+F(1,2))*STEP,sign*STEP/2,F(0))
            checked = check_frame_step(data,angles,nominal,previous,radius,start,end,
                                       i,sign,STEP,F(0))
            if not same_record(row,encode_step(checked,end)):
                raise ArithmeticError(f'exact step comparison failed, direction {sign}, slab {i}')
            trace.append(checked.segment)
            previous = [x.endpoint(1) for x in nominal]
            start,radius = end,checked.outgoing
        traces[sign] = trace
    verify_archived_prefix(data,traces,report,archived)


def process(job):
    mode,section,radius,path = job
    if mode == 'write':
        packet = generate(section,radius)
        payload = json.dumps(packet,separators=(',',':')).encode()
        out = NamedTemporaryFile(dir=path.parent,delete=False)
        temporary = Path(out.name)
        try:
            with out:
                out.write(gzip.compress(payload,mtime=0))
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)
    else:
        replay(json.loads(gzip.decompress(path.read_bytes())),section,radius)
    return f'{path.name}: 2 × {SLABS} verified framed slabs; archived action bounds and crossings match'


def witness_path(section,radius):
    index = 1000*radius
    if index.denominator != 1:
        raise ValueError('archive radius must be an integral number of thousandths')
    return DEFAULT_WITNESS.parent/f'bounce_frame_q{section}_u{int(index)}.json.gz'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['write','check'])
    parser.add_argument('file',type=Path,nargs='?')
    parser.add_argument('--section',type=int,choices=(0,1))
    parser.add_argument('--u',type=F)
    parser.add_argument('--all',action='store_true')
    parser.add_argument('--workers',type=int,default=1,help='concurrent single-thread endpoints with --all')
    args = parser.parse_args()
    if args.workers < 1 or args.workers > 8:
        parser.error('--workers must be from 1 to 8')
    if args.all:
        if args.section is not None or args.u is not None or args.file:
            parser.error('--all selects endpoint identities and output paths from the archive')
        archive = json.loads(ARCHIVE.read_text())
        endpoints = [(s['section_in_half_pi'],F(r['launch_radius']))
                     for s in archive['sections'] for r in s['endpoints']]
        if len(set(endpoints)) != 8 or len(endpoints) != 8:
            raise ValueError('eight distinct archived endpoints are required')
        jobs = [(args.mode,q,u,witness_path(q,u)) for q,u in endpoints]
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            for result in pool.map(process,jobs):
                print(result,flush=True)
    else:
        if args.workers != 1:
            parser.error('--workers applies only to --all')
        if args.mode == 'check' and args.file and args.section is None and args.u is None:
            # An explicitly named file may identify either section.
            job = (args.mode,None,None,args.file)
        else:
            section = 0 if args.section is None else args.section
            u = RADIUS if args.u is None else args.u
            job = (args.mode,section,u,args.file or witness_path(section,u))
        print(process(job))


if __name__ == '__main__':
    main()
