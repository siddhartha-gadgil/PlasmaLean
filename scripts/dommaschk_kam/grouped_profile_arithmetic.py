"""Sound group enclosures of QA2R strength and arclength at two radial launches."""
from fractions import Fraction as F

from bounce_mirror_pilot import HEIGHTS, Model, R0M, SCALE
from emit_position_slabs import step
from emit_sparse_taylor_slab import model_literal
from verify_backward_physical_prefix import compile_modules, union
from verify_centered_strength import Arithmetic, HEIGHT, DROP, footer, header
from verify_grouped_mirror_exclusion import group_literal
from verify_paired_arc_ratio import margin_data, physical_inputs
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_slopes import JET


GROUP = 'GroupedProfileProofCache'
SIDES = 'GroupedProfileSideCache'
PAIRS = 'GroupedProfilePairCache'
ROWS = 'GroupedProfileRowsCache'
THEORY = 'DommaschkGroupedProfileCompare'


def preamble(name, deps):
    return (header(name,[*deps,'PlasmaLean.Design.'+THEORY])
            +'open DommaschkGroupedMirrorModels DommaschkGroupedProfileCompare\n'
            +'open DommaschkPairedActionProfiles DommaschkPhysicalActionPanel\n')


def physical_values(tube):
    r,z,c,s = tube
    return physical_inputs((r,(r-R0M,z,c,s),{}))


def reference_arithmetic(tube):
    r,z,c,s = tube
    center = (Model(r.a),Model(z.a),c,s)
    a = Arithmetic()
    a.leaf('r',center[0],'(referenceR s)','hr')
    for tag,d,v in zip('DNZ',('dD','dnR','dnZ'),physical_values(center)['values'],strict=True):
        a.leaf(tag,v,f'(atPoint {d} (referenceR s) t (referenceZ s))','in'+tag)
    power = 'r'
    for k in ('r2','r4','r8','power'):
        power = a.op(k,power,'*',power)
    rd = a.op('rd','r','*','D')
    subtotal = a.op('subtotal',a.op('rd2',rd,'*',rd),'+',a.op('n2','N','*','N'))
    a.op('num',subtotal,'+',a.op('z2','Z','*','Z'))
    a.interval('r')
    return a


def side_source(name,center_jet,jet,gradient,tube,common,rates):
    r = tube[0]
    e = F(r.e,SCALE)
    k,l = rates
    error = e*(k+l)
    a = reference_arithmetic(tube)
    src = preamble(name,[GROUP+'.'+gradient,JET+'.'+center_jet,JET+'.'+jet])
    src += f'''def group : Group := {group_literal(tube)}
def shared : Group := {group_literal(common)}
def referenceR (s : ℝ) := QPoly.eval group.radial.poly s
def referenceZ (s : ℝ) := QPoly.eval group.height.poly s
def error : ℚ := {error}
def power : Model := {model_literal(a.values['power'])}
def numerator : Model := {model_literal(a.values['num'])}
'''
    src += '\n'.join(a.defs)+f'''
theorem reference_values {{s t : ℝ}} (hs : |s| ≤ 1)
    (hc : group.cosine.Mem s (Real.cos (2*t))) (hsi : group.sine.Mem s (Real.sin (2*t))) :
    0 < referenceR s ∧ power.Mem s ((referenceR s)^16) ∧
      numerator.Mem s ((referenceR s)^16 * physicalSq t (referenceR s) (referenceZ s)) := by
  let mr := {model_literal(Model(r.a))}
  have hr : mr.Mem s (referenceR s) := by
    rw [Model.Mem, show mr.poly = group.radial.poly by with_unfolding_all rfl,
      show mr.radius = 0 by with_unfolding_all rfl]
    simp [referenceR]
  have hz : {center_jet}.trial.z.Mem s (referenceZ s) := by
    rw [Model.Mem,show {center_jet}.trial.z.poly = group.height.poly by with_unfolding_all rfl,
      show {center_jet}.trial.z.radius = 0 by with_unfolding_all rfl]
    simp [referenceZ]
  have coords : {center_jet}.trial.Mem s (referenceR s-dkR0) (referenceZ s)
      (Real.cos (2*t)) (Real.sin (2*t)) :=
    ⟨DommaschkPreMirrorSigns.shifted_mem hr (eq_of_beq (by kernel_fact)) (by kernel_fact),hz,hc,hsi⟩
'''
    for tag,symbol in zip('DNZ',('dD','dnR','dnZ'),strict=True):
        src += f'''  have in{tag} : {center_jet}.{symbol}0.Mem s (atPoint {symbol} (referenceR s) t (referenceZ s)) :=
    {center_jet}.{symbol}_checked.mem hs coords
'''
    src += '\n'.join(a.body)+f'''
  have pos : 0 < referenceR s := by linarith only [boundr.1]
  refine ⟨pos, ?_, ?_⟩
  · have eq : valpower = (referenceR s)^16 := by dsimp only [{', '.join(a.locals)}]; ring
    rw [← eq]
    exact inpower
  · rw [scaled_sq pos]
    have eq : valnum = (referenceR s * atPoint dD (referenceR s) t (referenceZ s))^2 +
        (atPoint dnR (referenceR s) t (referenceZ s))^2 + (atPoint dnZ (referenceR s) t (referenceZ s))^2 := by
      dsimp only [{', '.join(a.locals)}]
      ring
    rw [← eq]
    exact innum

theorem field_inputs {{s t : ℝ}} {{x : Plane}} (m : InputsAt group s t x) :
    {jet}.trial.Mem s (x 0-dkR0) (x 1) (Real.cos (2*t)) (Real.sin (2*t)) :=
  ⟨DommaschkPreMirrorSigns.shifted_mem m.1 (eq_of_beq (by kernel_fact)) (by kernel_fact),
    m.2.1,m.2.2.1,m.2.2.2⟩

theorem error_on {{s t : ℝ}} {{x : Plane}} (hs : |s| ≤ 1) (m : InputsAt group s t x) :
    |physicalSq t (x 0) (x 1) - physicalSq t (referenceR s) (referenceZ s)| ≤ (error:ℝ) := by
  have equal : group.height.radius = group.radial.radius := by with_unfolding_all rfl
  have hz : |x 1-referenceZ s| ≤ (group.radial.radius:ℝ) := by
    rw [←equal]
    exact m.2.1
  have result := centered (h := ({HEIGHTS[0]}:ℝ)) (k := ({k}:ℝ)) (l := ({l}:ℝ))
    (show |x 0-referenceR s| ≤ (group.radial.radius:ℝ) from m.1) hz (by
      intro R z ur uz
      have sr := enclose (c := shared.radial) hs (show group.radial.Mem s R from ur) (by kernel_fact)
      have sz := enclose (c := shared.height) hs
        (show group.height.Mem s z from (show |z-referenceZ s| ≤ (group.height.radius:ℝ) by rw [equal]; exact uz))
        (by kernel_fact)
      have sc := enclose (c := shared.cosine) hs m.2.2.1 (by kernel_fact)
      have ss := enclose (c := shared.sine) hs m.2.2.2 (by kernel_fact)
      apply {gradient}.gradients hs
      exact ⟨DommaschkPreMirrorSigns.shifted_mem sr (eq_of_beq (by kernel_fact)) (by kernel_fact),sz,sc,ss⟩)
  have eq : (group.radial.radius:ℝ)*(({k}:ℝ)+({l}:ℝ)) = (error:ℝ) := by
    rw [show group.radial.radius = ({e}:ℚ) by with_unfolding_all rfl]
    norm_num [error]
  exact result.trans_eq eq
'''
    return (name,src+footer(name),['reference_values','field_inputs','error_on']),a,error


def drop_arithmetic(sides):
    g = Arithmetic()
    for j,(ns,a,_) in enumerate(sides):
        power=f'(({ns}.referenceR s)^16)'
        field=f'(physicalSq t ({ns}.referenceR s) ({ns}.referenceZ s))'
        g.leaf('p'+str(j),a.values['power'],power,'hp'+str(j))
        g.leaf('u'+str(j),a.values['num'],'('+power+'*'+field+')','hu'+str(j))
    g.literal('allowance',2*HEIGHT*DROP+sides[0][2]+sides[1][2])
    g.op('pp','p0','*','p1')
    g.op('u0p','u0','*','p1')
    g.op('u1p','u1','*','p0')
    g.op('margin',g.op('dif','u0p','-','u1p'),'-',g.op('charge','allowance','*','pp'))
    if g.interval('margin')[0] <= 0:
        raise ValueError('the group mean-value strength margin crosses zero')
    return g


def screen_group(a,b,tubes,common):
    from verify_centered_strength import gradient_item
    r,z,c,s = common
    _,rates = gradient_item('Screen','Jet',(r,(r-R0M,z,c,s),{}))
    references = [(ns, reference_arithmetic(tube), F(tube[0].e,SCALE)*sum(rates))
                  for ns,tube in zip(('Inner','Outer'),tubes,strict=True)]
    gap = drop_arithmetic(references)
    arc = margin_data(list(map(physical_values,tubes)))
    return dict(start=a,stop=b,radial_rate=str(rates[0]),vertical_rate=str(rates[1]),
                errors=[str(x[2]) for x in references],centered_margin=str(gap.values['margin'].bound()[0]),
                arclength_margin=str(arc.values['gap'].bound()[0]),
                ceiling_margins=[str(arc.values[tag].bound()[0]) for tag in ('capI','capO')])


def pair_source(name,sides,tubes,field_jets):
    arc = margin_data(list(map(physical_values,tubes)))
    gap = drop_arithmetic(sides)
    inner,outer = [ns for ns,_,_ in sides]
    src = preamble(name,[SIDES+'.'+ns for ns,_,_ in sides])
    src += '\n'.join([*arc.defs,*gap.defs])+f'''
theorem compared : Comparison {inner}.group {outer}.group := by
  intro s t i o hs mi mo
'''
    for j,(side,label,ns,end,jet) in enumerate(zip(['mi','mo'],['i','o'],[inner,outer],
                                                     ['I','O'],field_jets,strict=True)):
        src += f'''  obtain ⟨pos{j},hp{j},hu{j}⟩ := {ns}.reference_values hs {side}.2.2.1 {side}.2.2.2
  have err{j} := {ns}.error_on hs {side}
  have hR{end} := {side}.1
  have coords{end} := {ns}.field_inputs {side}
'''
        for k,d in zip('dnz',('dD','dnR','dnZ'),strict=True):
            src += f'''  have in{k}{end} : {jet}.{d}0.Mem s (atPoint {d} ({label} 0) t ({label} 1)) :=
    {jet}.{d}_checked.mem hs coords{end}
'''
    src += '\n'.join(gap.body)+f'''
  have drop : 2*(17/16:ℝ)*(1/18000) ≤ (strength t i)^2-(strength t o)^2 := by
    apply DommaschkCenteredStrength.compare (pow_pos pos0 16) (pow_pos pos1 16) err0 err1
    convert (by linarith only [boundmargin.1] : 0 ≤ valmargin) using 1
    dsimp only [{', '.join(gap.locals)}, {inner}.error, {outer}.error]
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
    ring
'''
    src += '\n'.join(arc.body)
    for end,label in [('I','i'),('O','o')]:
        src += f'''
  have pos{end} : 0 < {label} 0 := by linarith only [boundr{end}.1]
  have den{end} : 0 < atPoint dD ({label} 0) t ({label} 1) := by linarith only [boundd{end}.1]
  have id{end} := DommaschkPairedArcRatio.physical_identity (φ := t) (x := {label}) pos{end} den{end}
  have cap{end} : strength t {label} ≤ 17 / 16 := by
    apply DommaschkPairedArcRatio.ceiling pos{end}
    convert (by linarith only [boundcap{end}.1] : 0 ≤ valcap{end}) using 1
    dsimp only [{', '.join(arc.locals)}]
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
    ring
'''
    src += f'''  refine ⟨posI,posO,DommaschkPairedArcRatio.compared_of_squared capI capO drop ?_⟩
  apply DommaschkPairedArcRatio.compare denI denO idO.1 idI.2 idO.2
  convert (by linarith only [boundgap.1] : 0 ≤ valgap) using 1
  dsimp only [{', '.join(arc.locals)}]
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast,DommaschkPairedArcRatio.ratio]
  ring
'''
    return (name,src+footer(name),['compared']),gap.values['margin'].bound()[0],arc.values['gap'].bound()[0]


def row_source(stem,a,b,sides,records):
    name = stem+'Rows'
    harmonics = [f'DommaschkHarmonicBlock{h:02}' for h in range(a//8,(b-1)//8+1)]
    src = preamble(name,[PAIRS+'.'+stem,*['PlasmaLean.Design.'+h for h in harmonics]])
    labels = []
    for i in range(a,b):
        packet = f'(DommaschkHarmonicBlock{i//8:02}.packet {i%8})'
        shift,scale = F(2*i+1-a-b,b-a),F(1,b-a)
        for d,(sign,back,phase) in enumerate([('back','true','(-t)'),('fwd','false','t')]):
            for tag,(ns,_,_),(_,_,traces,_) in zip(('Inner','Outer'),sides,records,strict=True):
                row = sign+tag+f'{i:03}'
                src += f'''def {row} : Step := {step(traces[d]['steps'][i])}
private theorem {row}Covers : Covers (i := {i}) {packet} {back} {row} ({shift}) ({scale}) {ns}.group := by
  constructor <;> kernel_fact
'''
            tag = sign+f'{i:03}'
            labels.append(tag)
            src += f'''theorem {tag} {{a b : PositionFrameSlabs.State}} {{t : ℝ}} {{i o : Plane}}
    (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hi : i ∈ (physicalSlab a {sign}Inner{i:03} ({i}/64)).tube t)
    (ho : o ∈ (physicalSlab b {sign}Outer{i:03} ({i}/64)).tube t) : Compared {phase} i o := by
  apply compare_rows {sign}Inner{i:03}Covers {sign}Outer{i:03}Covers {stem}.compared _ hi ho
  norm_num at ht ⊢
  exact ht
'''
    return (name,src+footer(name),labels),harmonics


def finish(stem,a,b,tubes,common,records,fields,gradient,rates,values,args):
    packages = [*getattr(args,'native_static',[]),fields,gradient,*[p for side in values for p in side]]
    keys = [args.keys,digest(DESIGN/(THEORY+'.trace'))]

    def check(item,parents,package,extra=()):
        return compile_modules(args.cache/item[0],[item],[union(args.cache,parents)],
                               [package,*keys,*[m['key'] for _,m in parents],*extra],args,package)

    sides = []
    jets = []
    for suffix,boxes,tube in zip(('Inner','Outer'),values,tubes,strict=True):
        center,full = [p[1]['module'] for p in boxes]
        item,ar,error = side_source(stem+suffix,center,full,gradient[1]['module'],tube,common,rates)
        packages.append(check(item,[*getattr(args,'native_static',[]),fields,gradient,*boxes],SIDES))
        sides.append((item[0],ar,error))
        jets.append(full)
    item,drop,arc = pair_source(stem,sides,tubes,jets)
    packages.append(check(item,packages,PAIRS))
    item,harmonics = row_source(stem,a,b,sides,records)
    root,m = check(item,packages,ROWS,[digest(DESIGN/(h+'.trace')) for h in harmonics])
    report = {k:v for k,v in m.items() if k!='artifacts'}
    report.update(start=a,stop=b,packets=args.keys[0],centered_margin=str(drop),arclength_margin=str(arc),
                  radial_rate=str(rates[0]),vertical_rate=str(rates[1]),errors=[str(s[2]) for s in sides],
                  import_paths=[str(root),str(union(args.cache,packages))])
    save(args.output,report)
    print(item[0],m['key'],flush=True)
