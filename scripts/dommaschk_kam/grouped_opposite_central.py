"""Independent signed group models for the original opposite-section ODE references."""
from fractions import Fraction as F

from bounce_mirror_pilot import Model,R0M,angle_models
from grouped_central_models import compress,field_models,fit,quotient
from screen_sparse_reference_defects import jobs
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_physical_trace_slabs import RECORD

LABELS=ENDPOINTS[4:]


def coordinates(job):
    section,sign,i,coeffs,*_=job
    if section!=1 or sign not in (-1,1):
        raise ValueError('the opposite-section model requires an original signed row')
    r,z=map(Model,coeffs)
    phases=angle_models(F(sign*(2*i+1),128),F(sign,128),F(0))
    phases=[m.integer((-1)**((j+1)//2)) for j,m in enumerate(phases)]
    return r,r-R0M,z,phases


def direction_data(rows,start,stop):
    columns=[]
    for j in rows:
        r,_,z,waves=coordinates(j)
        columns.append([r,z,*waves])
    r,z,*waves=[fit(col) for col in zip(*columns,strict=True)]
    ins=r,r-R0M,z,waves
    values=field_models(ins)
    checked={}
    for job in rows:
        _,sign,i,_,_,_,budget,_=job
        local=[compress(m,i,start,stop) for m in values]
        d,nr,nz=local
        ratio,box,sharp=quotient(job,(d,nr.integer(sign),nz.integer(sign)))
        checked[i]=(job,local,ratio,box,sharp/F(budget))
    return ins,values,checked


def data(label,start,stop):
    if label not in LABELS or not 0<=start<stop<=391:
        raise ValueError('choose an original opposite-section span')
    packet=RECORD.with_name(f'bounce_frame_q1_u{label[3:]}.json.gz')
    selected={s:[] for s in (1,-1)}
    for job in jobs(packet,8,False):
        if start<=job[2]<stop:
            selected[job[1]].append(job)
    for signed in selected.values():
        if [j[2] for j in signed]!=list(range(start,stop)):
            raise ValueError('incomplete signed central group')
    return packet,{sign:direction_data(signed,start,stop) for sign,signed in selected.items()}


def stem(label,sign,a,b):
    direction='Forward' if sign==1 else 'Back'
    return f'Dommaschk{label.upper()}{direction}Central{a:03}To{b:03}'
