"""Certify a negative physical mirror gap on one correlated group of phase-zero archive rows."""
import argparse
from fractions import Fraction
from math import ceil
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_mirror_pilot import HEIGHTS, Model, R0M, ZERO, horner
from emit_sparse_taylor_slab import ROOT, model_literal
from verify_backward_physical_prefix import compile_modules, union
from verify_grouped_mirror_exclusion import GAPS, group_literal, ordered, run_group, span_models
from verify_native_action_models import DATA_PACKAGE, FIELDS, MATCH, SP_FIELDS, WAVES
from verify_native_action_models import emit_horner_field, footer, header, static_data, verify_static
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load


INPUT = 'GroupedHarmonicInputCache'
FIELDS_PACKAGE = 'GroupedHarmonicFieldCache'
THEORY = 'DommaschkGroupedHarmonicGap'


def harmonics(c,s):
    one = Model.rational(1)
    return [one,s,c,(s*c).integer(2),(c*c).integer(2)-one,
            s.integer(3)-(s*s*s).integer(4),(c*c*c).integer(4)-c.integer(3)]


def negative_gap(r,models):
    d,nr,nz,shift = models
    return r*r*shift*(d.integer(2)-shift)+nr*nr+nz*nz


def field_margins(tube,channels):
    r,z,c,s = tube
    u = r-R0M
    angles = harmonics(c,s)
    values = []
    for field in channels:
        value = ZERO
        for w,rows in reversed(field):
            weights = [horner([m for _,m in row],u) for row in rows]
            value = horner(weights,z)*angles[w]+value
        values.append(value)
    return negative_gap(r,values).bound()[1]


def radius_cap(radius):
    return Fraction(ceil(radius.bound()[1]*256),256)


def valid(upper,radius,clearance,drop):
    if drop:
        h = HEIGHTS[0]
        return upper+radius_cap(radius)**16*(h*h-(h-drop)**2) < 0
    if clearance:
        lo,hi = radius.bound()
        return upper <= -Fraction(1,125000) and 0 <= lo <= hi <= 1
    return upper < 0


def select(enclose,a,b,channels,clearance,adaptive,drop=Fraction(0)):
    tube = enclose(a,b)
    upper = field_margins(tube,channels)
    if valid(upper,tube[0],clearance,drop):
        return [(a,b,tube,upper)]
    if not adaptive or b==a+1:
        raise ValueError(f'rows {a}..{b-1} need a sharper certificate; gap upper bound {upper}')
    mid = (a+b)//2
    return (select(enclose,a,mid,channels,clearance,True,drop)
            +select(enclose,mid,b,channels,clearance,True,drop))


def inputs(name,tube):
    r,z,c,s = tube
    angles = harmonics(c,s)
    src = header(name,['PlasmaLean.Design.'+THEORY])
    src += 'open DommaschkGroupedMirrorModels DommaschkGroupedHarmonicGap\n'
    src += f'def group : Group := {group_literal(tube)}\n'
    src += f'def displacement : Model := {model_literal(r-R0M)}\n'
    src += 'abbrev vertical := group.height\ndef phase : Wave → Model\n'
    for wave,angle in zip(WAVES,angles,strict=True):
        src += f'  | .{wave} => {model_literal(angle)}\n'
    src += f'''theorem angles {{w θ : ℝ}} (hw : |w| ≤ 1) (hc : group.cosine.Mem w (Real.cos θ))
    (hs : group.sine.Mem w (Real.sin θ)) (wave : Wave) : (phase wave).Mem w (wave.value θ) := by
  have equality : Matches (harmonic group.cosine group.sine wave) (phase wave) := by
    cases wave <;> constructor <;> apply eq_of_beq <;> kernel_fact
  rw [← equality.eq]
  exact harmonic_mem hw hc hs wave
'''
    return (name,src+footer(name),['angles']),(r,r-R0M,z,angles)


def result(name,inp,tube,fields,models,clearance,drop):
    providers = [m[1]['module'] for m in fields]
    r,*_ = tube
    g = negative_gap(r,models)
    lo,hi = g.bound()
    if not valid(hi,r,clearance,drop):
        raise ValueError(f'{name}: compensated upper bound {hi} misses the requested height')
    mid,width = (hi+lo)/2,(hi-lo)/2
    extras = ['PlasmaLean.Design.DommaschkGroupGapRadius'] if drop else []
    src = header(name,[INPUT+'.'+inp,'PlasmaLean.Design.DommaschkCoreClearance',*extras,
                       *[FIELDS_PACKAGE+'.'+p for p in providers]])
    src += f'''open DommaschkFirstMirrorLaunchSign DommaschkMirrorEndpointSign DommaschkGroupedMirrorModels
open DommaschkPreMirrorSigns DommaschkGroupedHarmonicGap
abbrev group := {inp}.group
def upper : ℚ := {hi}
private def evaluated : Model := {model_literal(g)}

theorem gap_upper {{w R z t : ℝ}} (hw : |w| ≤ 1) (hr : group.radial.Mem w R)
    (hz : group.height.Mem w z) (hc : group.cosine.Mem w (Real.cos (2*t)))
    (hs : group.sine.Mem w (Real.sin (2*t))) :
    gap R (height false) (DommaschkBounceField.atPoint dD R t z)
      (DommaschkBounceField.atPoint dnR R t z) (DommaschkBounceField.atPoint dnZ R t z) ≤ upper := by
  have hu := shifted_mem (u := {inp}.displacement) hr (eq_of_beq (by kernel_fact)) (by kernel_fact)
  have waves := {inp}.angles hw hc hs
'''
    for i,p in enumerate(providers):
        src += f'  have field{i} := {p}.sound hw hu hz waves\n'
    src += f'''  have gap_bound := estimate_mem (k := height false) hw hr field0 field1 field2 field3
  have same : Matches (estimate group.radial {' '.join(p+'.model' for p in providers)}) evaluated :=
    {MATCH}
  rw [same.eq] at gap_bound
  have bounded := enclose (c := ⟨[({mid})],({width})⟩) hw gap_bound (by kernel_fact)
  change gap R (height false)
    (evR (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) dD)
    (evR (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) dnR)
    (evR (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) dnZ) ≤ (upper : ℝ)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le, upper] at bounded ⊢
  linarith only [bounded.2]
'''
    if drop:
        cap = radius_cap(r)
        src += f'''theorem below : group.Below (↑(height false - ({drop})) : ℝ) := by
  intro w R z t hw hR hr hz hc hs
  apply physical_sign false hR (by norm_num [height])
  have box := enclose (c := ⟨[({cap/2})],({cap/2})⟩) hw hr (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at box
  apply DommaschkGroupGapRadius.at_lower (radius := ({cap})) hR.le (by linarith only [box.2])
    (by norm_num [height]) (gap_upper hw hr hz hc hs)
  norm_num [upper, height]
'''
    elif clearance:
        src += '''theorem below : group.Below DommaschkCoreClearance.height := by
  intro w R z t hw hR hr hz hc hs
  apply physical_sign false hR (by norm_num [DommaschkCoreClearance.height, height])
  have box := enclose (c := ⟨[1/2],1/2⟩) hw hr (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at box
  apply DommaschkCoreClearance.of_gap hR.le (by linarith only [box.2])
  exact (gap_upper hw hr hz hc hs).trans (by norm_num [upper])
'''
    else:
        src += '''theorem below : group.Below (height false) := by
  intro w R z t hw hR hr hz hc hs
  apply physical_sign false hR (by norm_num [height])
  exact (gap_upper hw hr hz hc hs).trans_lt (by norm_num [upper])
'''
    return (name,src+footer(name),['gap_upper','below']),hi


def native_gap(name,tube,args):
    inp,coordinates = inputs(name+'Inputs',tube)
    common = [args.keys,digest(DESIGN/(THEORY+'.trace'))]
    ir = compile_modules(args.cache/inp[0],[inp],[],common,args,INPUT)
    packages = [ir]
    values = []
    fields = []
    for k,p in enumerate(args.channels):
        static = args.static[k]
        field,value = emit_horner_field(name+FIELDS[k],SP_FIELDS[k],p,coordinates,
            static[1]['module'],inp[0],DATA_PACKAGE,INPUT)
        fields.append(compile_modules(args.cache/field[0],[field],[ir[0],static[0]],
            [common,ir[1]['key'],static[1]['key']],args,FIELDS_PACKAGE))
        values.append(value)
    packages.extend([*args.static,*fields])
    closed,upper = result(name,inp[0],tube,fields,values,args.clearance,args.drop)
    dependencies = [common,digest(DESIGN/'DommaschkCoreClearance.trace'),[r['key'] for _,r in packages]]
    if args.drop:
        dependencies.append(digest(DESIGN/'DommaschkGroupGapRadius.trace'))
    gr = compile_modules(args.cache/name,[closed],[union(args.cache,packages)],
        dependencies,args,GAPS)
    args.upper = upper
    return [*packages,gr]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--launch',type=int,required=True)
    p.add_argument('--start',type=int)
    p.add_argument('--stop',type=int,help='first excluded slab index')
    p.add_argument('--all',action='store_true',help='cover the complete incoming prefix adaptively')
    p.add_argument('--screen',action='store_true',help='only propose groups with exact external arithmetic')
    height = p.add_mutually_exclusive_group()
    height.add_argument('--clearance',action='store_true',help='use the existing hL − 1/270000 comparison')
    height.add_argument('--drop',type=Fraction,default=Fraction(0),help='prove |B| < hL − DROP using a local radius cap')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-harmonic-exclusion')
    p.add_argument('--static-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    label,path,traces,brackets = load(args.launch)
    stop = brackets[0][0]
    if args.all and (args.start is not None or args.stop is not None):
        p.error('choose either --all or an explicit --start and --stop')
    if args.all:
        args.start,args.stop = 0,stop
    if args.start is None or args.stop is None or not 0<=args.start<args.stop<=stop:
        p.error('choose --all or a nonempty group within the original incoming prefix')
    if not 0 <= args.drop < HEIGHTS[0]:
        p.error('the requested height drop must be nonnegative and strictly smaller than hL')
    args.channels = static_data()
    tasks = select(span_models(traces),args.start,args.stop,args.channels,args.clearance,args.all,args.drop)
    target = HEIGHTS[0] - (Fraction(1,270000) if args.clearance else args.drop)
    data = dict(endpoint=label,packet_sha256=digest(path),target=str(target))
    if args.screen:
        data.update(kind='preflight',groups=[dict(start=a,stop=b,upper=str(v)) for a,b,_,v in tasks])
        save(args.output,data)
        print(f'{label}: {len(tasks)} proposed signed groups on [{args.start},{args.stop})')
        return
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    args.keys = [data['packet_sha256'],lake('lean','--version')]
    args.cache = args.cache.resolve()
    static_args = SimpleNamespace(cache=args.static_cache,fields=range(4),lean=args.lean,
                                  lean_path=args.lean_path)
    args.static = verify_static(static_args,args.channels)
    threshold = 'DommaschkCoreClearance.height' if args.clearance else 'DommaschkFirstMirrorLaunchSign.height false'
    if args.drop:
        threshold = f'(↑(DommaschkFirstMirrorLaunchSign.height false - ({args.drop})) : ℝ)'
    results,packages = [],[]
    for a,b,tube,upper in tasks:
        group,ps = run_group((a,b,tube,[tube]),label+'Harmonic',traces,args,
                             provider=native_gap,threshold=threshold)
        if upper != args.upper:
            raise ValueError('checked field computation differs from the proposed upper estimate')
        base,marker = ps[-1]
        results.append(dict(**group,upper=str(upper),proof_root=str(base),axioms=marker['axioms'],
                            theorems=marker['theorems']))
        packages.extend(ps)
    data.update(groups=results,kind='verified')
    if args.all:
        data.update(ordered(label+'Harmonic',results,packages,args,threshold))
    else:
        data.update(results[0],import_paths=[str(base),str(union(args.cache,packages))])
    save(args.output,data)


if __name__ == '__main__':
    main()
