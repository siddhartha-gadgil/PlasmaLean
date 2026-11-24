"""Kernel-check centered squared-strength separation on both signed QA2R endpoint tubes."""
import argparse
from fractions import Fraction as F
from math import ceil
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_mirror_pilot import HEIGHTS, Model, R0M, SCALE, ZERO, angle_models
from emit_sparse_taylor_slab import model_literal, models
from screen_sparse_jacobians import field_jet
from verify_backward_physical_prefix import compile_modules, union
from verify_horner_endpoint_jacobian import inputs_source
from verify_native_action_models import (DATA_PACKAGE, MATCH, SP_FIELDS, emit_horner_field,
                                        static_data, verify_static)
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import JET, jet_files, joint_row


PACKAGE = 'CenteredStrengthCache'
INPUTS = 'CenteredInputCache'
FIELDS = 'CenteredFieldCache'
SIDES = 'CenteredSideCache'
PAIRS = 'CenteredPairCache'
HEIGHT = F(17,16)
DROP = F(1,18000)


def header(name, imports):
    return ('module\n'+''.join('public import '+m+'\n' for m in imports)+f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates Certificates.TrajectoryTaylorModel Certificates.PositionFrameSlabs
open DommaschkBounceTaylor DommaschkKam DkPoly DommaschkBounceField DommaschkMirrorTubeCrossing
open DommaschkNativeActionGeometry DommaschkCenteredStrength
set_option linter.style.longLine false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option Elab.async false
''')


def footer(name):
    return f'\nend PlasmaLean.Design.{name}\n'


class Arithmetic:
    """Each step exposes its rounded model and a proof on the same normalized clock."""
    def __init__(self):
        self.values, self.expr, self.proofs = {}, {}, {}
        self.defs, self.body, self.locals = [], [], []

    def leaf(self, name, model, expr, proof):
        self.values[name],self.expr[name],self.proofs[name] = model,expr,proof

    def literal(self, name, value):
        m = Model.rational(value)
        self.defs.append(f'private def tm{name} : Model := {model_literal(m)}')
        self.body.append(f'''  have in{name} : tm{name}.Mem s (({value}:ℚ):ℝ) :=
    enclose hs (constant_mem ({value}) s) (by kernel_fact)''')
        self.leaf(name,m,f'(({value}:ℚ):ℝ)',f'in{name}')

    def op(self, name, a, op, b=None):
        if op == '-':
            self.op(name+'Neg',b,'neg')
            return self.op(name,a,'+',name+'Neg')
        left = self.values[a]
        if op == 'neg':
            val = -left
            expression = '-'+self.expr[a]
            proof = f'checked_neg (out := tm{name}) {self.proofs[a]}'
        else:
            val = left*self.values[b] if op=='*' else left+self.values[b]
            expression = self.expr[a]+' '+op+' '+self.expr[b]
            tactic = 'checked_product' if op=='*' else 'checked_sum'
            clock = ' hs' if op=='*' else ''
            proof = f'{tactic} (out := tm{name}){clock} {self.proofs[a]} {self.proofs[b]}'
        self.defs.append(f'private def tm{name} : Model := {model_literal(val)}')
        self.body += [f'  let val{name} := {expression}',
                      f'  have in{name} : tm{name}.Mem s val{name} := {proof} ({MATCH})']
        self.locals.append('val'+name)
        self.leaf(name,val,'val'+name,'in'+name)
        return name

    def interval(self, name):
        lo,hi = self.values[name].bound()
        self.body.append(f'''  have bound{name} := DommaschkPairedActionProfiles.range
    (lo := {lo}) (hi := {hi}) hs {self.proofs[name]} (by kernel_fact)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_natCast,
    Rat.cast_intCast] at bound{name}''')
        return lo,hi


def gradient_item(stem, jet, data):
    r,cols,_ = data
    name = stem+'Gradient'
    a = Arithmetic()
    first = f'''theorem gradients {{s R z t : ℝ}} (hs : |s| ≤ 1)
    (inp : {jet}.trial.Mem s (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)))'''
    body = [f'''  have off : (constant (29/32)).Mem s dkR0 := by
    convert constant_mem (29/32) s using 1
    norm_num [dkR0]
  have hr : ({model_literal(r)}).Mem s R := by
    have h := enclose (c := {model_literal(r)}) hs (mem_add inp.1 off) (by kernel_fact)
    simpa only [sub_add_cancel] using h''']
    a.leaf('r',r,'R','hr')
    for symbol,tag,spec in zip(('dD','dnR','dnZ'),'DRZ',field_jet(),strict=True):
        for j,terms in enumerate(spec):
            suf=('','U','Z')[j]
            label=tag+suf
            model=symbol if not j else 'grad'+label
            poly=symbol if not j else f'(d{suf} {symbol})'
            expr='val'+label
            body.append(f'  let {expr} := atPoint {poly} R t z')
            body.append(f'  have in{label} : {jet}.{model}0.Mem s {expr} := {jet}.{model}_checked.mem hs inp')
            a.locals.append(expr)
            a.leaf(label,sum(models(terms,cols),ZERO),expr,'in'+label)
    for key,value in [('h',HEIGHTS[0]),('h7',7*HEIGHTS[0]),('two',2),('seven',7),('sixteen',16)]:
        a.literal(key,value)
    op=a.op
    op('r2','r','*','r');op('r4','r2','*','r2');op('r8','r4','*','r4');op('r16','r8','*','r8')
    op('r17','r16','*','r');op('r6','r2','*','r4');op('r7','r','*','r6')
    op('delta','D','-',op('href','h','*','r7'))
    op('deltaR','DU','-',op('dref','h7','*','r6'))
    op('q',op('R2','R','*','R'),'+',op('Z2','Z','*','Z'))
    op('r2d','r2','*','D')
    for suf in ['U','Z']:
        op('q'+suf,'two','*',op('dot'+suf,op('nr'+suf,'R','*','R'+suf),'+',op('nz'+suf,'Z','*','Z'+suf)))
    op('term','r','*','deltaR')
    op('dr','term','-',op('d7','seven','*','delta'))
    op('gradR',op('gradR2',op('gradR1','two','*',op('radialTerm','r2d','*','dr')),'+',op('rqu','r','*','qU')),
       '-',op('q16','sixteen','*','q'))
    op('gradZ',op('gradZ1','two','*',op('verticalTerm','r2d','*','DZ')),'+','qZ')
    limits = {}
    for tag in ['r','D','gradR','gradZ','r17','r16']:
        limits[tag] = a.interval(tag)
    rates = [F(ceil(10**7*max(map(abs,limits[g]))/limits[d][0]),10**7)
             for g,d in [('gradR','r17'),('gradZ','r16')]]
    if min(limits['r'][0],limits['D'][0],limits['r17'][0],limits['r16'][0]) <= 0:
        raise ValueError('gradient denominator crosses zero')
    body += a.body
    body += ['  have Rpos : 0 < R := by linarith only [boundr.1]',
             '  refine ⟨Rpos, by linarith only [boundD.1], ?_, ?_⟩']
    for field,g,d,pow_,rate in zip(['radial','vertical'],['gradR','gradZ'],['r17','r16'],[17,16],rates,strict=True):
        args = f'({HEIGHTS[0]}:ℝ) t R z' if field=='radial' else 't R z'
        lo,hi=limits[g]
        body.append(f'''  · have eq : {field} {args} = val{g}/val{d} := by
      dsimp only [{', '.join([field,*a.locals])}]
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_intCast]
      ring
    rw [eq,abs_div,abs_of_pos (show 0 < val{d} by linarith only [bound{d}.1])]
    apply (div_le_iff₀ (show 0 < val{d} by linarith only [bound{d}.1])).mpr
    rw [abs_le]
    constructor <;> linarith only [bound{g}.1, bound{g}.2, bound{d}.1]''')
    s=header(name,[JET+'.'+jet,'PlasmaLean.Design.DommaschkCenteredStrength',
                   'PlasmaLean.Design.DommaschkNativeActionGeometry','PlasmaLean.Design.DommaschkPairedActionProfiles'])
    s+='\n'.join(a.defs)+'\n'+first+f''' :
    0 < R ∧ 0 < atPoint dD R t z ∧ |radial ({HEIGHTS[0]}) t R z| ≤ {rates[0]} ∧
      |DommaschkCenteredStrength.vertical t R z| ≤ {rates[1]} := by\n'''
    return (name,s+'\n'.join(body)+footer(name),['gradients']),rates


def prepare_side(label, i, path, traces, cache, env, version, static, channels):
    data=joint_row(i,traces)
    r,cols,_=data
    jet,files,deps=jet_files(label,i,data)
    key=[digest(path),version]
    enclosure=compile_modules(ROOT/'.lake/secondary-mirror-slopes'/jet,files,[],[key,deps],env,JET)
    name=f'DommaschkCentered{label}{i:03}'
    item,rates=gradient_item(name,jet,data)
    gradient=compile_modules(cache/item[0],[item],[enclosure[0]],
        [key,enclosure[1]['key'],digest(DESIGN/'DommaschkCenteredStrength.trace'),
         digest(DESIGN/'DommaschkPairedActionProfiles.trace')],env,PACKAGE)
    print('Gradient',label,i,rates,gradient[1]['key'],flush=True)
    waves=angle_models(F(2*i+1,128),F(1,128),F(0))
    ins=(Model(r.a),Model(cols[0].a),Model(cols[1].a),waves)
    item=inputs_source(name+'Center',i,ins,0)
    center=compile_modules(cache/item[0],[item],[],[INPUTS,key,digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),
                                                    digest(DESIGN/'DommaschkNativeActionModel.trace')],env,INPUTS)
    fields=[]
    values=[]
    for j,tag in enumerate(['D','NR','NZ']):
        item,m=emit_horner_field(name+'Center'+tag,SP_FIELDS[j],channels[j],ins,static[j][1]['module'],
            center[1]['module'],DATA_PACKAGE,INPUTS)
        checked=compile_modules(cache/item[0],[item],[union(cache,[static[j],center])],
            [key,center[1]['key'],static[j][1]['key']],env,FIELDS)
        fields.append(checked)
        values.append(m)
    print('Reference field',label,i,flush=True)
    return dict(stem=name,data=data,jet=jet,gradient=gradient,center=center,fields=fields,
                values=values,rates=rates,enclosure=enclosure,ins=ins,
                packages=[enclosure,gradient,center,*fields])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--row',type=int,required=True)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/centered-strength')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if not 0<=args.row<391:
        parser.error('row must be between 0 and 390')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],text=True,cwd=ROOT).strip()
    env=SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),lean_path=lake('printenv','LEAN_PATH'))
    version=lake('lean','--version')
    channels=static_data()
    static=verify_static(SimpleNamespace(**vars(env),cache=ROOT/'.lake/native-action-checks',fields=range(3)),channels)
    sides=[]
    for k in (470,478):
        label,path,traces,_=load(k)
        sides.append(prepare_side(label,args.row,path,traces,args.cache,env,version,static,channels))
    from centered_strength_pair import finish
    finish(args.row,sides,static,args.cache,env,version,args.output)


if __name__=='__main__':
    main()
