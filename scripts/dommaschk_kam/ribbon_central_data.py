"""Central physical ODE enclosures for the four widened phase-zero launch intervals."""
from fractions import Fraction as F
from functools import lru_cache
import gzip
import json
from pathlib import Path

from bounce_frame_witness import FRAME_SCALE
from grouped_central_models import boxes,compress,field_models,quotient
from screen_reflected_reference import conjugate
from verify_physical_trace_slabs import digest

WITNESS_SHA='c4f65ab5d7727fc5fdbae645c6924ecde6b474f521663a8b1b9de6be8d45a486'
ENDPOINTS=('203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d',
           '07763b1926fb24bb93889e651ced079f4871c59c72f443f6b7f2392fc5eb6f83')
LENGTH=332


def label(tile):
    return f'q0r{471+2*tile}'


@lru_cache(maxsize=1)
def load(source):
    source=Path(source)
    if source.suffix=='.gz':
        import hashlib
        raw=gzip.decompress(source.read_bytes())
        checksum=hashlib.sha256(raw).hexdigest()
        data=json.loads(raw)
    else:
        checksum=digest(source)
        data=json.loads(source.read_text())
    arcs=data['traces']
    if (checksum!=WITNESS_SHA or data['tiles']!=4 or data['seed_radius']!='1/65536' or
            tuple(data['endpoints'])!=ENDPOINTS or
            [(x['tile'],x['direction']) for x in arcs]!=[(k,s) for k in range(4) for s in (-1,1)]):
        raise ValueError('expected the authenticated four signed radial ribbons')
    out={}
    for trace in arcs:
        k,s=trace['tile'],trace['direction']
        start=[[FRAME_SCALE,0],[0,FRAME_SCALE]]
        rows=[]
        if len(trace['rows'])<LENGTH:
            raise ValueError('reference ribbon ends before elapsed time 332/64')
        for i,item in enumerate(trace['rows'][:LENGTH]):
            pos=item['position']
            if pos['index']!=i or item['index']!=i or [len(v) for v in pos['coefficients']]!=[8,8]:
                raise ValueError('missing or malformed signed ribbon row')
            rows.append((0,s,i,pos['coefficients'],start,pos['frame_end'],pos['defect_upper'],8))
            start=pos['frame_end']
        out[k,s]=rows
    for k in range(4):
        for f,b in zip(out[k,1],out[k,-1],strict=True):
            if (f[3][0]!=b[3][0] or [-v for v in f[3][1]]!=b[3][1]
                    or conjugate(f[4])!=b[4] or conjugate(f[5])!=b[5]):
                raise ValueError(f'original signed ribbon curves or frames differ after reflection at {k},{f[2]}')
    return out


def data(source,tile,a,b):
    if tile not in range(4) or not 0<=a<b<=LENGTH:
        raise ValueError('choose a radial tile and an original half-open group')
    arcs=load(source)
    fw=arcs[tile,1][a:b]
    ins=boxes(fw)
    fields=field_models(ins)
    rows={}
    for f in fw:
        i=f[2]
        back=arcs[tile,-1][i]
        local=[compress(m,i,a,b) for m in fields]
        ratios,box,sharp=quotient(f,local)
        rows[i]=(f,back,local,ratios,box,sharp/min(F(f[6]),F(back[6])))
    return ins,fields,rows
