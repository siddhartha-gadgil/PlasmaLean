"""Sparse field Jacobians on the two coordinate projections of both signed trial balls."""
from fractions import Fraction
import gzip
import json
from pathlib import Path
from string import Template

from bounce_mirror_pilot import Model, ORDER, R0M, SCALE, ZERO, angle_models
from emit_sparse_jacobian import derivative_file, header, matrix_certificate
from emit_sparse_taylor_slab import RECORD, field, model_literal, models
from screen_projected_jacobians import projected_jobs, projected_radii
from screen_sparse_jacobians import field_jet, symmetric_models
from screen_sparse_reference_defects import bounds
from shared_sparse_powers import add_shared_powers


CLOCK = Path(__file__).with_name('templates') / 'rectangular_jacobian_clock.lean.tpl'


def rectangular_data(index):
    """Return both signed trials' common widths and stricter growth rate."""
    job = next(j for j in projected_jobs(RECORD,1,True) if j[2] == index)
    start, step = job[3:5]
    radii = projected_radii(start,step['frame_end'],step['frame_trial_radius'])
    return start, step, radii


def panel_certificate(name, packet, rate):
    """Build the binary cover of eight rational normalized-time panels."""
    count = 8
    source = header(['DommaschkJacobianPanels'],'Joint principal-minor bounds on a rectangle',
                    name,'DommaschkJacobian')
    source += 'def models : SymmetricModels := ⟨'+',\n  '.join(map(model_literal,packet))+'⟩\n'
    source += f'def budget : ℚ := {rate}\n\n'
    leaves = []
    for j, (den, aa, dd, off) in enumerate(zip(*(bounds(x,count) for x in packet),strict=True)):
        dl,a,d,w = [Fraction(x,SCALE*count**ORDER) for x in
                    (den[0],aa[1],dd[1],max(map(abs,off)))]
        radial, vertical = rate*dl-a, rate*dl-d
        if dl <= 0 or rate <= 0 or min(radial,vertical) < 0 or w*w > 4*radial*vertical:
            raise ValueError(f'{name} needs a spatial subdivision on time panel {j}')
        lo,hi = Fraction(2*j-count,count),Fraction(2*j+2-count,count)
        source += f'''private theorem p{j} : MinorCover models budget ({lo}) ({hi}) := by
  apply MinorCover.panel
  refine ⟨{dl}, {a}, {d}, {w}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_fact
'''
        leaves.append(f'p{j}')
    while len(leaves) > 1:
        leaves = [f'(MinorCover.join {a} {b})' for a,b in zip(leaves[::2],leaves[1::2],strict=True)]
    return source+f'theorem accepted : MinorCover models budget (-1) 1 := {leaves[0]}\n\nend PlasmaLean.Design.{name}\n'


def clock_template(section):
    source = CLOCK.read_text()
    if not section:
        return Template(source)
    parts = ['  refine ⟨hu,hz,?_,?_⟩']
    for field, sine in [('cos','false'),('sin','true')]:
        parts.append(f'''  · have m : trial.{field} = Certificates.TrajectoryTrig.negative ((p false 0).model {sine}) := by
      apply Matches.eq
      constructor <;> apply eq_of_beq <;> kernel_fact
    rw [m]
    have v := DommaschkOppositeHarmonic.first p false {sine} h
    norm_num [Certificates.TrajectoryTrig.wave] at v ⊢
    exact v''')
    # The two clocks share every matrix operation. Only their input harmonic
    # witnesses and the physical angular argument differ.
    begin = source.index('  have hc := Certificates.TrajectoryHarmonicPacket.physical')
    end = source.index('\n\n/-- The physical field denominator',begin)
    shifted = (source[:begin] + '\n'.join(parts) + source[end:]).replace('(2*t)','(2*(Real.pi / 2 + t))')
    return Template(shifted)


def emit_rectangle(index, section, start, step, radii, stem, forward_rate):
    """Compile sparse fields and derivatives on one positive-clock physical rectangle."""
    if section not in (0,1):
        raise ValueError('only the two archived QA2R toroidal sections are defined')
    r,z = [Model(p,e) for p,e in zip(step['coefficients'],radii,strict=True)]
    rate = Fraction(step['log_norm_upper'])
    waves = angle_models(Fraction(2*index+1,128),Fraction(1,128),Fraction(0))
    columns = (r-R0M,z,waves[2].integer((-1)**section),waves[1].integer((-1)**section))
    inputs, panel, core = stem+'Inputs',stem+'Panels',stem+'Bounds'
    end = f'\nend PlasmaLean.Design.{stem}\n'
    def module(imports,title): return header(imports,title,stem,'DommaschkJacobian')
    files = {inputs:module(['DommaschkJacobianFrames'],'Coordinatewise trial rectangle')+
             'def trial : Inputs := ⟨'+',\n  '.join(map(model_literal,columns))+'⟩\n'+end}
    leaves = {}
    for tag,scalar,jet in zip(('D','R','Z'),('dD','dnR','dnZ'),field_jet(),strict=True):
        files[stem+tag] = module([inputs],'Sparse field on a trial rectangle')+field(scalar,columns)+end
        leaves[tag] = scalar+'0',scalar,sum(models(jet[0],columns),ZERO)
        for axis,letter in enumerate('UZ'):
            label = tag+letter
            symbol = 'grad'+label
            blocks = models(jet[axis+1],columns)
            files[stem+label] = derivative_file(scalar,symbol,axis,blocks,stem,inputs,'DommaschkJacobian')
            leaves[label] = symbol+'0',symbol,sum(blocks,ZERO)
    packets = symmetric_models(section,1,index,start,step,r,z)
    files[panel] = panel_certificate(panel,packets,rate)
    body = matrix_certificate(leaves,step,namespace=stem,start=start,dependencies=list(files),
                              context='DommaschkJacobian',panel=panel)
    files[core] = body.replace('firstLeft','leftFrame').replace('firstRight','rightFrame')
    block,local = divmod(index,8)
    harmonic = f'DommaschkHarmonicBlock{block:02}'
    clock = clock_template(section).substitute(i=index,end=index+1,offset=2*index+1,
        local=local,base=8*block,count=min(8,391-8*block),harmonic=harmonic,panel=panel,
        rate=rate,forward_rate=forward_rate)
    deps = [core,harmonic] + (['DommaschkOppositeHarmonic'] if section else [])
    files[stem] = module(deps,'Physical field Jacobian on the projected rectangle')+clock+end
    return add_shared_powers(files,inputs,stem,columns)


def emit(index):
    start, step, radii = rectangular_data(index)
    with gzip.open(RECORD,'rt') as fp:
        forward, = [x for x in json.load(fp)['traces'] if x['direction']==1]
    return emit_rectangle(index,0,start,step,radii,f'DommaschkProjectedJacobian{index:03}',
                          forward['steps'][index]['log_norm_upper'])
