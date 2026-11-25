"""Certify outward mirror slopes on closed groups of physical radial-ribbon tubes."""
import argparse
from collections import defaultdict
from fractions import Fraction
import json
from math import ceil
from pathlib import Path

from bounce_collar import S, harmonic_terms
from bounce_frame_witness import DEFAULT_WITNESS
from bounce_mirror_pilot import HEIGHTS, Model, R0M, ZERO, horner
from emit_position_slabs import step
from emit_sparse_taylor_slab import model_literal
from screen_sparse_jacobians import field_jet
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_grouped_mirror_exclusion import compose
from verify_harmonic_group_exclusion import harmonics, inputs
from verify_native_action_models import MATCH, emit_static_field, emit_horner_field, header, footer
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_slopes import joint_row

THEORY = 'DommaschkCompensatedMirrorSlope'
STATIC = 'RadialRibbonSlopeDataCache'
INPUT = 'RadialRibbonSlopeInputCache'
FIELDS = 'RadialRibbonSlopeFieldCache'
RESULT = 'RadialRibbonSlopeCache'
RATE = Fraction(1, 16384)
GROUPS = [(tiles, start, stop) for tiles in [(0, 1), (2, 3)]
          for start, stop in [(317, 324), (324, 327), (327, 329), (329, 331)]]


def channels(terms):
    coefficients = defaultdict(Fraction)
    for q, (u, z, c, s) in terms:
        for wave, weight in harmonic_terms(c, s):
            if weight.lo != weight.hi:
                raise ValueError('inexact harmonic coefficient')
            coefficients[wave, u, z] += q * Fraction(weight.lo, S)
    coefficients = {k: v for k, v in coefficients.items() if v}
    result = []
    for wave in sorted({w for w, _, _ in coefficients}):
        rows = []
        zdeg = max(z for w, _, z in coefficients if w == wave)
        for z in reversed(range(zdeg + 1)):
            udeg = max((u for w, u, h in coefficients if (w, h) == (wave, z)), default=0)
            weights = [coefficients.get((wave, u, z), 0) for u in reversed(range(udeg + 1))]
            rows.append([(q, Model.rational(q)) for q in weights])
        result.append((wave, rows))
    return result


def slope_fields():
    jets = field_jet()
    for tag, sym, terms in zip('DRZ', ('dD', 'dnR', 'dnZ'), jets, strict=True):
        for key, target, poly in zip(('', 'U', 'Z'), (sym, '(DkPoly.dU '+sym+')',
                '(DkPoly.dZ '+sym+')'), terms, strict=True):
            if key != 'U' or tag != 'D':
                yield tag+key, target, channels(poly)
        angular = defaultdict(Fraction)
        for q, (u, z, c, s) in terms[0]:
            if s:
                angular[u,z,c+1,s-1] += 2*s*q
            if c:
                angular[u,z,c-1,s+1] -= 2*c*q
        yield tag+'P', f'({THEORY}.angular {sym})', channels((q,e) for e,q in angular.items())
    radial = defaultdict(Fraction)
    for q, (u, z, c, s) in jets[0][0]:
        radial[u,z,c,s] += (u-7)*q
        if u:
            radial[u-1,z,c,s] += Fraction(29,32)*u*q
    yield 'L', THEORY+'.radial', channels((q,e) for e,q in radial.items())


def load_ribbon(path):
    packet = json.loads(path.read_text())
    traces = packet['traces']
    expected = [digest(DEFAULT_WITNESS), digest(DEFAULT_WITNESS.with_name('bounce_frame_q0_u478.json.gz'))]
    if (packet['tiles'] != 4 or packet['endpoints'] != expected or packet['seed_radius'] != '1/65536'
            or Fraction(packet['height']) != HEIGHTS[1] or [(a['tile'],a['direction']) for a in traces]
            != [(k,s) for k in range(4) for s in [-1,1]]):
        raise ValueError('the complete original widened four-tile archive is required')
    for a in traces:
        if (len(a['rows']) < 331 or any(r['index'] != j or r['position']['index'] != j
                for j,r in enumerate(a['rows']))):
            raise ValueError('missing or unordered physical row')
    return [[{'steps':[r['position'] for r in a['rows']]} for a in traces[2*k:2*k+2]] for k in range(4)]


def cover(traces, tiles, a, b):
    """Choose the mean dyadic reference, then charge all coefficient differences and output radii."""
    n, mid = b-a, (a+b-1)//2
    saved = []
    for j in range(a,b):
        for k in tiles:
            r, (_,z,c,s), _ = joint_row(j,traces[k])
            saved.append((j, [r,z,c,s]))
    result = []
    for axis in range(4):
        centres = [m[axis].a for j,m in saved if j==mid]
        mean = [round(Fraction(sum(v),len(centres))) for v in zip(*centres,strict=True)]
        poly = compose(mean,a+b-1-2*mid,n)
        radius = 0
        for j, mdl in saved:
            back = compose(poly,Fraction(2*j+1-a-b,n),Fraction(1,n))
            fit = sum(abs(x-y) for x,y in zip(mdl[axis].a,back,strict=True))
            radius = max(radius,ceil(mdl[axis].e+fit))
        result.append(Model(poly,radius))
    return result


def static(tables, a):
    trace = digest(DESIGN/(THEORY+'.trace'))
    out = {}
    for tag, target, table in tables:
        n,s,th = emit_static_field('DommaschkRibbonSlopeData'+tag, target, table)
        s = s.replace('public import PlasmaLean.Design.DommaschkNativeActionModel',
                      f'public import PlasmaLean.Design.{THEORY}\npublic import PlasmaLean.Design.DommaschkNativeActionModel')
        out[tag] = compile_modules(a.cache/n,[(n,s,th)],[],[a.version, trace],a,STATIC)
    return out


def value(table, q):
    u,z,angles=q
    total=ZERO
    for wave,rows in reversed(table):
        total=horner([horner([v for _,v in row],u) for row in rows],z)*angles[wave]+total
    return total


def assemble(name, inp, providers, values, tube):
    imports = [INPUT+'.'+inp, 'PlasmaLean.Design.DommaschkRibbonSlopeCover',
               'PlasmaLean.Design.DommaschkNativeActionGeometry',
               *[FIELDS+'.'+p for p in providers.values()]]
    src = header(name,imports)
    src += ('open DommaschkRibbonSlopeCover DommaschkNativeActionGeometry DommaschkPreMirrorSigns '
            'DommaschkBounceField DommaschkMirrorStrengthSlope\n')
    src += f'abbrev group := {inp}.group\n'
    cols = {**values,'radius':tube[0],'rate':Model.rational(RATE)}
    defs = [f'def rate : Weight := ⟨({RATE}), {cols["rate"].a[0]}, 0, by kernel_fact⟩']
    lines = [f'  have hu := shifted_mem (u := {inp}.displacement) hr (eq_of_beq (by kernel_fact)) (by kernel_fact)',
             f'  have waves := {inp}.angles hw hc hs', '  have h_radius := hr',
             f'  have h_rate := rate.mem w']
    for tag, provider in providers.items():
        lines.append(f'  have h_{tag} := {provider}.sound hw hu hz waves')
    def op(dst, kind, x, y=None):
        if kind == '*':
            m = cols[x]*cols[y]
            proof = f'checked_product (out := {dst}) hw h_{x} h_{y}'
        elif kind == '+':
            m = cols[x]+cols[y]
            proof = f'checked_sum (out := {dst}) h_{x} h_{y}'
        else:
            m = -cols[x]
            proof = f'checked_neg (out := {dst}) h_{x}'
        cols[dst] = m
        defs.append(f'private def {dst} : Model := {model_literal(m)}')
        lines.append(f'  have h_{dst} := {proof} ({MATCH})')
    for tag in 'RZ':
        op('u'+tag,'*','R',tag+'U')
        op('z'+tag,'*','Z',tag+'Z')
        op('p'+tag,'*','D',tag+'P')
        op('s'+tag,'+','u'+tag,'z'+tag)
        op('m'+tag,'+','s'+tag,'p'+tag)
    ops=[('NL','*','R','L'),('verticalD','*','Z','DZ'),('angularD','*','D','DP'),
         ('tailD','+','verticalD','angularD'),('radTail','*','radius','tailD'),('tor','+','NL','radTail'),
         ('r2','*','radius','radius'),('r2D','*','r2','D'),('part1','*','r2D','tor'),
         ('nM','*','R','mR'),('zM','*','Z','mZ'),('spatial','+','nM','zM'),
         ('part2','*','radius','spatial'),('both','+','part1','part2'),('twice','+','both','both'),
         ('nSq','*','R','R'),('zSq','*','Z','Z'),('poloid','+','nSq','zSq'),
         ('drift','*','R','poloid'),('dr2','+','drift','drift'),('dr4','+','dr2','dr2'),
         ('dr8','+','dr4','dr4'),('dr16','+','dr8','dr8'),('negative','-','dr16'),
         ('derivNum','+','twice','negative'),('r4','*','r2','r2'),('r8','*','r4','r4'),
         ('r16','*','r8','r8'),('r17','*','radius','r16'),('den','*','r17','D'),
         ('allow','*','rate','den'),('minusAllow','-','allow'),('margin','+','derivNum','minusAllow')]
    for args in ops:
        op(*args)
    for tag in ('D','margin'):
        lo,hi=cols[tag].bound()
        if lo <= 0:
            raise ValueError(f'{name}: {tag} does not have a strict margin')
        lines.append(f'  have box{tag} := enclose (c := ⟨[({(lo+hi)/2})],({(hi-lo)/2})⟩) hw h_{tag} (by kernel_fact)')
        lines.append(f'  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at box{tag}')
    lines.extend(['  refine ⟨by unfold atPoint; linarith only [boxD.1], ?_⟩',
                  '  rw [DommaschkCompensatedMirrorSlope.numerator_eq]',
                  '  unfold atPoint',
                  '  dsimp only [rate] at boxmargin',
                  '  linarith only [boxmargin.1]'])
    src+='\n'.join(defs)+f'\ntheorem outward : Outward group ({RATE}) := by\n'
    src+='  intro w R z t hw hr hz hc hs\n'+'\n'.join(lines)+footer(name)
    return (name,src,['outward']),cols['margin'].bound()[0]


def run_group(index,traces,tables,data,a):
    tiles,start,stop=GROUPS[index]
    name=f'DommaschkRibbonSlopeT{tiles[0]}{tiles[1]}R{start}To{stop}'
    tube=cover(traces,tiles,start,stop)
    inp, coords=inputs(name+'Inputs',tube)
    keys=[a.version,digest(a.ribbon),tiles,start,stop,digest(DESIGN/'DommaschkGroupedHarmonicGap.trace')]
    ir=compile_modules(a.cache/inp[0],[inp],[],keys,a,INPUT)
    packages=[ir,*data.values()]
    providers,values={},{}
    for tag,target,table in tables:
        field,model=emit_horner_field(name+tag,target,table,coords,data[tag][1]['module'],inp[0],STATIC,INPUT)
        product=compile_modules(a.cache/field[0],[field],[ir[0],data[tag][0]],[keys,ir[1]['key'],data[tag][1]['key']],a,FIELDS)
        providers[tag],values[tag]=field[0],model
        packages.append(product)
    final,slack=assemble(name,inp[0],providers,values,tube)
    overlay=union(a.cache,packages)
    root,record=compile_modules(a.cache/name,[final],[overlay],
        [keys,[r['key'] for _,r in packages],digest(DESIGN/'DommaschkRibbonSlopeCover.trace')],a,RESULT)
    return {'group':index,'module':name,'tiles':tiles,'start':start,'stop':stop,'key':record['key'],
            'margin':str(slack),'squared_slope':str(RATE),'axioms':record['axioms'],
            'import_paths':[str(root),str(overlay)]}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-ribbon-slopes')
    p.add_argument('--static',action='store_true')
    p.add_argument('--groups',type=int,nargs='+',choices=range(len(GROUPS)))
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    tables=list(slope_fields())
    traces=load_ribbon(a.ribbon)
    env(a)
    fields=static(tables,a)
    if a.static:
        save(a.output,{'ribbon':digest(a.ribbon),'fields':{k:r['key'] for k,(_,r) in fields.items()}})
        return
    groups = []
    for i in (a.groups if a.groups is not None else range(len(GROUPS))):
        row=run_group(i,traces,tables,fields,a)
        groups.append(row)
        save(a.output,dict(ribbon=digest(a.ribbon),groups=groups))
        print(row['module'],row['key'],flush=True)


if __name__=='__main__':
    main()
