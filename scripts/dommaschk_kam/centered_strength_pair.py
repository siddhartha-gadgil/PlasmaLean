"""Lean proof terms for reference values, both signed tubes, and their common-clock comparison."""
from fractions import Fraction as F

from bounce_mirror_pilot import HEIGHTS, SCALE
from emit_sparse_taylor_slab import model_literal
from verify_backward_physical_prefix import compile_modules, union
from verify_physical_trace_slabs import DESIGN, RECORD, digest, save
from verify_secondary_mirror_slopes import JET


def side_theorems(i, side):
    from verify_centered_strength import Arithmetic, FIELDS, PACKAGE, footer, header
    name=side['stem']+'Physical'
    jac=side['jet']
    center=side['center'][1]['module']
    gradient=side['gradient'][1]['module']
    fields=[p[1]['module'] for p in side['fields']]
    r,_,_=side['data']
    e=F(r.e,SCALE)
    k,l=side['rates']
    error=e*(k+l)
    deps=[JET+'.'+jac,PACKAGE+'.'+gradient,*(FIELDS+'.'+f for f in fields),
          'PlasmaLean.Design.DommaschkPreMirrorSigns']
    src=header(name,deps)
    a=Arithmetic()
    a.leaf('r',side['ins'][0],'(referenceR s)','hr')
    for n,symbol,m in zip(['D','N','Z'],['dD','dnR','dnZ'],side['values'],strict=True):
        a.leaf(n,m,f'(atPoint {symbol} (referenceR s) t (referenceZ s))','in'+n)
    a.op('rr','r','*','r');a.op('r4','rr','*','rr');a.op('r8','r4','*','r4');a.op('power','r8','*','r8')
    a.op('rd','r','*','D');a.op('rd2','rd','*','rd');a.op('n2','N','*','N');a.op('z2','Z','*','Z')
    a.op('num',a.op('sum','rd2','+','n2'),'+','z2')
    a.interval('r')
    src+=f'''
def referenceR (s : ℝ) : ℝ := dkR0 + QPoly.eval {jac}.trial.u.poly s
def referenceZ (s : ℝ) : ℝ := QPoly.eval {jac}.trial.z.poly s
def fwdRow := {jac}.fwdRow
def backRow := {jac}.backRow
def epsilon : ℚ := {e}
def error : ℚ := {error}
'''+ '\n'.join(a.defs)+f'''
def power : Model := {model_literal(a.values['power'])}
def numerator : Model := {model_literal(a.values['num'])}

theorem reference_values {{t : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64)) :
    let s := 128*t-{2*i+1}
    0 < referenceR s ∧ power.Mem s ((referenceR s)^16) ∧
      numerator.Mem s ((referenceR s)^16 * physicalSq t (referenceR s) (referenceZ s)) := by
  let s := 128*t-{2*i+1}
  have hs : |s| ≤ 1 := abs_le.mpr ⟨by dsimp [s]; linarith only [ht.1],
    by dsimp [s]; linarith only [ht.2]⟩
  let m := {model_literal(side['ins'][0])}
  have coeff : m.poly = QPoly.add [29/32] {jac}.trial.u.poly := by with_unfolding_all rfl
  have hr : m.Mem s (referenceR s) := by
    rw [Model.Mem,coeff,QPoly.eval_add]
    norm_num [referenceR,dkR0,QPoly.eval_cons,QPoly.eval_nil,m,ofDyadic]
  have hu : {center}.displacement.Mem s (referenceR s-dkR0) := by
    rw [Model.Mem, show {center}.displacement.poly = {jac}.trial.u.poly by with_unfolding_all rfl,
      show {center}.displacement.radius = 0 by with_unfolding_all rfl]
    unfold referenceR
    simp
  have hz : {center}.vertical.Mem s (referenceZ s) := by
    rw [Model.Mem, show {center}.vertical.poly = {jac}.trial.z.poly by with_unfolding_all rfl,
      show {center}.vertical.radius = 0 by with_unfolding_all rfl]
    unfold referenceZ
    simp
'''
    for n,f in zip(['D','N','Z'],fields,strict=True):
        src+=f'  have in{n} := {f}.sound hs hu hz ({center}.angles ht)\n'
    src+='\n'.join(a.body)+f'''
  have pos : 0 < referenceR s := by linarith only [boundr.1]
  refine ⟨pos, ?_, ?_⟩
  · have ident : valpower = (referenceR s)^16 := by
      dsimp only [{', '.join(a.locals)}]
      ring
    rw [← ident]
    exact inpower
  · rw [scaled_sq pos]
    have ident : valnum = (referenceR s * atPoint dD (referenceR s) t (referenceZ s))^2 +
        (atPoint dnR (referenceR s) t (referenceZ s))^2 + (atPoint dnZ (referenceR s) t (referenceZ s))^2 := by
      dsimp only [{', '.join(a.locals)}]
      ring
    rw [← ident]
    exact innum

private theorem coord_iff (s x : ℝ) : {jac}.trial.u.Mem s (x-dkR0) ↔ |x-referenceR s| ≤ (epsilon:ℝ) := by
  change |x-dkR0-QPoly.eval {jac}.trial.u.poly s| ≤ _ ↔ _
  rw [show x-dkR0-QPoly.eval {jac}.trial.u.poly s = x-referenceR s by unfold referenceR; ring]
  rw [show {jac}.trial.u.radius = epsilon by with_unfolding_all rfl]

private theorem z_iff (s y : ℝ) : {jac}.trial.z.Mem s y ↔ |y-referenceZ s| ≤ (epsilon:ℝ) := by
  change |y-referenceZ s| ≤ ({jac}.trial.z.radius:ℝ) ↔ _
  rw [show {jac}.trial.z.radius = epsilon by with_unfolding_all rfl]

theorem error_on {{t x y : ℝ}} (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hr : {jac}.trial.u.Mem (128*t-{2*i+1}) (x-dkR0))
    (hz : {jac}.trial.z.Mem (128*t-{2*i+1}) y) :
    let s := 128*t-{2*i+1}
    |physicalSq t x y - physicalSq t (referenceR s) (referenceZ s)| ≤ (error:ℝ) := by
  let s := 128*t-{2*i+1}
  have hs : |s| ≤ 1 := abs_le.mpr ⟨by dsimp [s]; linarith only [ht.1],
    by dsimp [s]; linarith only [ht.2]⟩
  have result := centered (h := ({HEIGHTS[0]}:ℝ)) ((coord_iff s x).mp hr)
    ((z_iff s y).mp hz)
    (k := ({k}:ℝ)) (l := ({l}:ℝ)) (fun r z ur uz =>
      {gradient}.gradients hs ({jac}.clock_inputs ht ((coord_iff s r).mpr ur) ((z_iff s z).mpr uz)))
  have eq : ((epsilon:ℚ):ℝ)*(({k}:ℝ)+({l}:ℝ)) = (error:ℝ) := by norm_num [epsilon,error]
  rw [eq] at result
  exact result
'''
    names=['reference_values','error_on']
    for direction,term,bool_,phase in [('fwd','fwdRow','false','t'),('back','backRow','true','(-t)')]:
        thm=direction+'_error'
        names.append(thm)
        src+=f'''
theorem {thm} {{prev : Certificates.PositionFrameSlabs.State}} {{x : Plane}} {{t : ℝ}}
    (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {term} ({i}/64)).tube t) :
    let s := 128*t-{2*i+1}
    |(strength {phase} x)^2-physicalSq t (referenceR s) (referenceZ s)| ≤ (error:ℝ) := by
  have identified : DommaschkPreMirrorSigns.Matches {bool_} {term} ({model_literal(r)}) {jac}.trial := by
    constructor
    · apply eq_of_beq; kernel_fact
    · apply eq_of_beq; kernel_fact
    · apply eq_of_beq; kernel_fact
    · kernel_fact
    · kernel_fact
    · kernel_fact
  obtain ⟨_,u,z⟩ := identified.mem hx
  have clk : coord ({i}/64) t = 128*t-{2*i+1} := by unfold coord; ring
  rw [clk] at u z
  have result := error_on ht u z
'''
        if direction=='fwd':
            src+='  exact result\n'
        else:
            src+=f'''  have input := {jac}.clock_inputs ht u z
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have pos := ({gradient}.gradients hs input).1
  have reflectEq := DommaschkMirrorTubeCrossing.strength_reflected pos t (-(x 1))
  simp only [neg_neg] at reflectEq
  change |‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint (x 0) (-t) (x 1))‖^2 - _| ≤ _
  rw [reflectEq]
  exact result
'''
    return (name,src+footer(name),names),a.values['power'],a.values['num'],error


def pair_theorems(i,sides,physical):
    from verify_centered_strength import Arithmetic, DROP, HEIGHT, SIDES, footer, header
    name=f'DommaschkCenteredStrengthPair{i:03}'
    ns=[p[0][1]['module'] for p in physical]
    g=Arithmetic()
    for j,(p,(_,mv,mp,_)) in enumerate(zip(ns,physical,strict=True)):
        t=f'(physicalSq t ({p}.referenceR s) ({p}.referenceZ s))'
        power=f'(({p}.referenceR s)^16)'
        g.leaf('p'+str(j),mv,power,'hp'+str(j))
        g.leaf('u'+str(j),mp,'('+power+'*'+t+')','hu'+str(j))
    shift=2*HEIGHT*DROP
    allowance=shift+physical[0][3]+physical[1][3]
    g.literal('allowance',allowance)
    g.op('pp','p0','*','p1')
    g.op('u0p','u0','*','p1');g.op('u1p','u1','*','p0')
    g.op('margin',g.op('dif','u0p','-','u1p'),'-',g.op('charge','allowance','*','pp'))
    lo,_=g.interval('margin')
    if lo<=0:
        raise ValueError(f'nonpositive centered strength margin on row {i}: {lo}')
    src=header(name,[SIDES+'.'+x for x in ns])
    src+='\n'.join(g.defs)+f'''
private theorem on_clock {{t f v : ℝ}} (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hi : |f-physicalSq t ({ns[0]}.referenceR (128*t-{2*i+1})) ({ns[0]}.referenceZ (128*t-{2*i+1}))| ≤ ({ns[0]}.error:ℝ))
    (ho : |v-physicalSq t ({ns[1]}.referenceR (128*t-{2*i+1})) ({ns[1]}.referenceZ (128*t-{2*i+1}))| ≤ ({ns[1]}.error:ℝ)) :
    2*(17/16:ℝ)*(1/18000) ≤ f-v := by
  let s := 128*t-{2*i+1}
  have hs : |s| ≤ 1 := abs_le.mpr ⟨by dsimp [s]; linarith only [ht.1],
    by dsimp [s]; linarith only [ht.2]⟩
'''
    for j,p in enumerate(ns):
        src+=f'  obtain ⟨pos{j},hp{j},hu{j}⟩ := {p}.reference_values ht\n'
    src+='\n'.join(g.body)+f'''
  apply DommaschkCenteredStrength.compare (pow_pos pos0 16) (pow_pos pos1 16) hi ho
  have h : 0 ≤ valmargin := by linarith only [boundmargin.1]
  convert h using 1
  dsimp only [{', '.join(g.locals)}, {ns[0]}.error,{ns[1]}.error]
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
  ring
'''
    thms=[]
    for d,phase in [('fwd','t'),('back','(-t)')]:
        n=d+'_squared_drop';thms.append(n)
        src+=f'''
theorem {n} {{p q : Certificates.PositionFrameSlabs.State}} {{x y : Plane}} {{t : ℝ}}
    (ht : t ∈ Set.Icc ({i}/64 : ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab p {ns[0]}.{d}Row ({i}/64)).tube t)
    (hy : y ∈ (physicalSlab q {ns[1]}.{d}Row ({i}/64)).tube t) :
    2*(17/16:ℝ)*(1/18000) ≤ (strength {phase} x)^2-(strength {phase} y)^2 :=
  on_clock ht ({ns[0]}.{d}_error ht hx) ({ns[1]}.{d}_error ht hy)
'''
    return (name,src+footer(name),thms),lo


def finish(i,sides,static,cache,env,version,output):
    from verify_centered_strength import PAIRS, SIDES
    parents=[*static,*[p for side in sides for p in side['packages']]]
    common=[version,digest(DESIGN/'DommaschkCenteredStrength.trace'),
            digest(DESIGN/'DommaschkPreMirrorSigns.trace'),digest(DESIGN/'DommaschkPairedActionProfiles.trace')]
    physical=[]
    for side in sides:
        item,p,u,e=side_theorems(i,side)
        mods=[*static,*side['packages']]
        out=compile_modules(cache/item[0],[item],[union(cache,mods)],
                            [SIDES,common,[m['key'] for _,m in mods]],env,SIDES)
        physical.append((out,p,u,e))
        parents.append(out)
    item,margin=pair_theorems(i,sides,physical)
    overlay=union(cache,parents)
    root,marker=compile_modules(cache/item[0],[item],[overlay],[PAIRS,common,[m['key'] for _,m in parents]],env,PAIRS)
    report={k:v for k,v in marker.items() if k!='artifacts'}
    report.update(index=i,inner='q0r470',outer='q0r478',centered_margin=str(margin),
                  errors=[str(r[3]) for r in physical],import_paths=list(map(str,[root,overlay])))
    report['endpoints'] = {
        label:dict(packet_sha256=digest(RECORD.with_name(f'bounce_frame_q0_u{label[3:]}.json.gz')),
                   spatial_jet=side['enclosure'][1]['key'],
                   radial_bound=str(side['rates'][0]), vertical_bound=str(side['rates'][1]),
                   gradient_key=side['gradient'][1]['key'], physical_module=proof[0][1]['module'],
                   physical_key=proof[0][1]['key'])
        for label,side,proof in zip(('q0r470','q0r478'),sides,physical,strict=True)}
    save(output,report)
    print(item[0],marker['key'],flush=True)
