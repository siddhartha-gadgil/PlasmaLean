"""Certify a same-angle arclength comparison on both signed outgoing tubes at two QA2R radii."""
import argparse
from fractions import Fraction as F
from pathlib import Path
import subprocess

from bounce_mirror_pilot import ZERO
from emit_sparse_taylor_slab import ROOT, model_literal, models
from screen_sparse_reference_defects import sparse_fields
from verify_backward_physical_prefix import compile_modules, union
from verify_centered_strength import Arithmetic
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import JET, jet_files, joint_row


PACKAGE = 'PairedArcRatioCache'
FIELDS = 'PairedArcFieldCache'
THEORY = 'DommaschkPairedArcRatio'
RATIO = F(3999,4000)


def physical_inputs(data):
    radius_model,columns,_ = data
    fields = [sum(models(poly,columns),ZERO) for poly in sparse_fields()]
    return dict(r=radius_model,values=fields)


def side(radius,index,backend,cache,args):
    label,path,traces,_ = load(radius)
    data = joint_row(index,traces)
    values = physical_inputs(data)
    jet,modules,deps = jet_files(label,index,data)
    packet = digest(path)
    if backend == 'shared':
        package = JET
        base = ROOT/'.lake/secondary-mirror-slopes'
    else:
        # Retain exactly the three field-value blocks and their shared powers. The prefix
        # replacement gives these leaner providers their own module names and cache keys.
        name = f'DommaschkArc{label}Values{index:03d}'
        keep = {jet+tail for tail in ['Inputs','Stored','D','R','Z','']}
        short = []
        for n,src,thms in modules:
            if n not in keep:
                continue
            src = '\n'.join(line for line in src.split('\n')
                            if not line.startswith('public import '+JET+'.')
                            or line.rsplit('.',1)[1] in keep)
            short.append((n.replace(jet,name),src.replace(jet,name).replace(JET+'.',FIELDS+'.'),thms))
        modules, jet, package, base = short, name, FIELDS, cache
    proof = compile_modules(base/jet,modules,[],[[packet,args.version],deps],args,package)
    return dict(jet=jet,package=package,proof=proof,checksum=packet,**values)


def margin_data(sides):
    arithmetic = Arithmetic()
    for label,suffix,side_data in zip(('i','o'),('I','O'),sides,strict=True):
        for term, model, val, proof in [
            ('r',side_data['r'],f'({label} 0)','hR'+suffix),
            *[(k,m,f'(atPoint {d} ({label} 0) t ({label} 1))','in'+k+suffix)
              for k,d,m in zip(('d','n','z'),('dD','dnR','dnZ'),side_data['values'],strict=True)]]:
            arithmetic.leaf(term+suffix,model,val,proof)
    arithmetic.literal('k2',RATIO**2)
    arithmetic.literal('loss',1-RATIO**2)
    arithmetic.literal('ceiling2',F(17,16)**2)
    op = arithmetic.op
    for end in ('I','O'):
        op('D'+end,'d'+end,'*','d'+end)
        op('A'+end,op('n2'+end,'n'+end,'*','n'+end),'+',op('z2'+end,'z'+end,'*','z'+end))
        power = 'r'+end
        for n in (2,4,8,16):
            power = op(f'r{n}{end}',power,'*',power)
        rd = op('rd'+end,'r'+end,'*','d'+end)
        full = op('full'+end,op('rd2'+end,rd,'*',rd),'+','A'+end)
        op('cap'+end,op('capScaled'+end,'ceiling2','*',power),'-',full)
    op('diff','rO','-','rI')
    op('sum','rO','+','rI')
    op('rad',op('change','diff','*','sum'),'+',op('allow','loss','*',op('r2','rI','*','rI')))
    op('main','rad','*',op('den','DI','*','DO'))
    op('plus','main','+',op('up','AO','*','DI'))
    op('gap','plus','-',op('sub','k2','*',op('down','AI','*','DO')))
    for tag in ('rI','rO','dI','dO','gap','capI','capO'):
        if arithmetic.interval(tag)[0] <= 0:
            raise ValueError(f'the whole-slab correlated certificate fails at {tag}')
    return arithmetic


def source(index,sides):
    name = f'DommaschkPairedArcRatio{index:03d}'
    arc = margin_data(sides)
    out = ('module\n'+''.join('public import '+s['package']+'.'+s['jet']+'\n' for s in sides)
           +'public import PlasmaLean.Design.'+THEORY+'\n'
           +'public import PlasmaLean.Design.DommaschkNativeActionReflection\n'
           +f'\n@[expose] public section\nnoncomputable section\nnamespace PlasmaLean.Design.{name}\n'
           +'open Certificates.TrajectoryTaylorModel Certificates.PositionFrameSlabs DommaschkKam\n'
           +'open DommaschkBounceField DommaschkBounceTaylor DommaschkMirrorTubeCrossing DommaschkNativeActionGeometry\n'
           +'open DommaschkPairedActionProfiles DommaschkPhysicalActionPanel\n'
           +'set_option maxRecDepth 16384\nset_option maxHeartbeats 2000000\n'
           +'set_option linter.style.longLine false\nset_option Elab.async false\n')
    clock = f'(128*t-{2*index+1})'
    ht = f'(ht : t ∈ Set.Icc ({index}/64:ℝ) ({index+1}/64))'
    names = []
    for suffix,s in zip(('I','O'),sides,strict=True):
        jet, rm = s['jet'],model_literal(s['r'])
        out += f'def radius{suffix} : Model := {rm}\n'
        for neg,tag in [('false','fwd'),('true','back')]:
            out += f'''abbrev {tag}Row{suffix} := {jet}.{tag}Row
private theorem {tag}{suffix} : DommaschkPreMirrorSigns.Matches {neg} {tag}Row{suffix} radius{suffix} {jet}.trial := by
  constructor
  · apply eq_of_beq; kernel_fact
  · apply eq_of_beq; kernel_fact
  · apply eq_of_beq; kernel_fact
  · kernel_fact
  · kernel_fact
  · kernel_fact
'''
    out += '\n'.join(arc.defs)+'\n'
    out += f'\nprivate theorem at_angle {{t : ℝ}} {{i o : Plane}} {ht}\n'
    for tag,end,s in zip(('i','o'),('I','O'),sides,strict=True):
        jet=s['jet']
        out += f'''    (hR{end} : radius{end}.Mem {clock} ({tag} 0))
    (hU{end} : {jet}.trial.u.Mem {clock} ({tag} 0-dkR0)) (hZ{end} : {jet}.trial.z.Mem {clock} ({tag} 1))
'''
    out += f'''    : 0 < i 0 ∧ 0 < o 0 ∧ strength t i ≤ 17/16 ∧ strength t o ≤ 17/16 ∧
      DommaschkPairedArcRatio.ratio * weight t i ≤ weight t o := by
  let s := {clock}
  have hs : |s| ≤ 1 := abs_le.mpr ⟨by dsimp [s]; linarith only [ht.1],by dsimp [s]; linarith only [ht.2]⟩
'''
    for tag,end,side_data in zip(('i','o'),('I','O'),sides,strict=True):
        jet = side_data['jet']
        out += f'  have coords{end} := {jet}.clock_inputs ht hU{end} hZ{end}\n'
        for k,d in zip(('d','n','z'),('dD','dnR','dnZ'),strict=True):
            out += f'''  have in{k}{end} : {jet}.{d}0.Mem s (atPoint {d} ({tag} 0) t ({tag} 1)) :=
    {jet}.{d}_checked.mem hs coords{end}
'''
    out += '\n'.join(arc.body)
    for tag,end in [('i','I'),('o','O')]:
        out += f'''
  have pos{end} : 0 < {tag} 0 := by linarith only [boundr{end}.1]
  have den{end} : 0 < atPoint dD ({tag} 0) t ({tag} 1) := by linarith only [boundd{end}.1]
  have id{end} := DommaschkPairedArcRatio.physical_identity (φ := t) (x := {tag}) pos{end} den{end}
  have cap{end} : strength t {tag} ≤ 17 / 16 := by
    apply DommaschkPairedArcRatio.ceiling pos{end}
    convert (by linarith only [boundcap{end}.1] : 0 ≤ valcap{end}) using 1
    dsimp only [{', '.join(arc.locals)}]
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
    ring
'''
    out += f'''  refine ⟨posI,posO,capI,capO, DommaschkPairedArcRatio.compare denI denO idO.1 idI.2 idO.2 ?_⟩
  convert (by linarith only [boundgap.1] : 0 ≤ valgap) using 1
  dsimp only [{', '.join(arc.locals)}]
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast,DommaschkPairedArcRatio.ratio]
  ring
'''
    # An explicit statement for each sign leaves the original physical row and its predecessor visible.
    for back,direction in [(False,'forward'),(True,'backward')]:
        tag = 'back' if back else 'fwd'
        phi = '(-t)' if back else 't'
        names.extend([direction+'_bounds',direction])
        declaration = f'''{{a b : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{i o : Plane}} {ht}
    (hi : i ∈ (physicalSlab a {tag}RowI ({index}/64)).tube t)
    (ho : o ∈ (physicalSlab b {tag}RowO ({index}/64)).tube t)'''
        out += f'''theorem {direction}_bounds {declaration} :
    strength {phi} i ≤ 17/16 ∧ strength {phi} o ≤ 17/16 ∧
    DommaschkPairedArcRatio.ratio * weight {phi} i ≤ weight {phi} o := by
  have clock_eq : coord ({index}/64) t = {clock} := by unfold coord; ring
  obtain ⟨ri,ui,zi⟩ := {tag}I.mem hi
  obtain ⟨ro,uo,zo⟩ := {tag}O.mem ho
  rw [clock_eq] at ri ui zi ro uo zo
'''
        if not back:
            out += '  exact (at_angle ht ri ui zi ro uo zo).2.2\n'
        else:
            out += '''  have h := at_angle (i := DommaschkJacobianReflection.flip i)
    (o := DommaschkJacobianReflection.flip o) ht
    (by simpa only [DommaschkJacobianReflection.flip_zero] using ri)
    (by simpa only [DommaschkJacobianReflection.flip_zero] using ui)
    (by simpa only [DommaschkJacobianReflection.flip_one,↓reduceIte] using zi)
    (by simpa only [DommaschkJacobianReflection.flip_zero] using ro)
    (by simpa only [DommaschkJacobianReflection.flip_zero] using uo)
    (by simpa only [DommaschkJacobianReflection.flip_one,↓reduceIte] using zo)
  have reflect (x : Plane) (hr : 0 < x 0) : weight (-t) x = weight t (DommaschkJacobianReflection.flip x) := by
    simpa only [weight,neg_neg,DommaschkJacobianReflection.flip_zero,DommaschkJacobianReflection.flip_one] using arcDensity_reflected hr t (-(x 1))
  have pi : 0 < i 0 := by simpa only [DommaschkJacobianReflection.flip_zero] using h.1
  have po : 0 < o 0 := by simpa only [DommaschkJacobianReflection.flip_zero] using h.2.1
  rw [DommaschkNativeActionReflection.norm pi t, DommaschkNativeActionReflection.norm po t,
    reflect i pi, reflect o po]
  exact h.2.2
'''
        out += f'''theorem {direction} {declaration} :
    DommaschkPairedArcRatio.ratio * weight {phi} i ≤ weight {phi} o :=
  ({direction}_bounds ht hi ho).2.2
'''
    return (name,out+f'\nend PlasmaLean.Design.{name}\n',names), arc.values['gap'].bound()[0]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--row',type=int,choices=range(325),metavar='0..324')
    mode.add_argument('--screen',action='store_true',help='screen every original slab with exact arithmetic')
    p.add_argument('--backend',choices=('shared','sparse'),default='sparse',
                   help='reuse full spatial jets also needed by the centered field drop, or build only three values')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-arc-ratio')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    if args.screen:
        records = [load(radius) for radius in (470,478)]
        bounds = []
        for i in range(325):
            sides = [physical_inputs(joint_row(i,traces)) for _,_,traces,_ in records]
            ar = margin_data(sides)
            bounds.append({k:str(ar.values[k].bound()[0]) for k in ('gap','capI','capO')})
        worst = {}
        for k in ('gap','capI','capO'):
            i = min(range(len(bounds)),key=lambda j:F(bounds[j][k]))
            worst[k] = dict(index=i,margin=bounds[i][k])
        save(args.output,dict(status='external exact arithmetic',rows=325,
             packets=[digest(path) for _,path,_,_ in records],minimum=worst,bounds=bounds))
        return
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.version = lake('lean','--version')
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    cache = args.cache.resolve()
    sides = [side(radius,args.row,args.backend,cache,args) for radius in (470,478)]
    item,margin = source(args.row,sides)
    packages = [s['proof'] for s in sides]
    imports = union(cache,packages)
    keys = [r['key'] for _,r in packages]
    packets = [s['checksum'] for s in sides]
    root,r = compile_modules(cache/item[0],[item],[imports],
                             [args.version,packets,keys,digest(DESIGN/(THEORY+'.trace')),
                              digest(DESIGN/'DommaschkNativeActionReflection.trace')],args,PACKAGE)
    result = {k:r[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')}
    result.update(row=args.row,backend=args.backend,field_keys=keys,packets=packets,
                  margin=str(margin),import_paths=[str(root),str(imports)])
    save(args.output,result)
    print(item[0],r['key'],flush=True)


if __name__=='__main__':
    main()
