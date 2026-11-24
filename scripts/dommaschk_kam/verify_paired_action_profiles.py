"""Verify a direct whole-slab comparison of actual QA2R strengths and arclengths."""
import argparse
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import subprocess

from bounce_mirror_pilot import HEIGHTS, Model
from emit_position_slabs import step
from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules, union
import verify_native_action_models as native
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load


PACKAGE = 'PairedProfileCache'
THEORY = 'DommaschkPairedActionProfiles'


def square_root_bounds(lo, hi):
    grid = 10**7
    if not 0 <= lo <= hi:
        raise ValueError('expected a nonnegative squared range')
    l = isqrt((lo * grid**2).__floor__())
    u = isqrt((hi * grid**2).__floor__())
    if F(u**2, grid**2) < hi:
        u += 1
    return F(l, grid), F(u, grid)


def ranges(ins, fields):
    """Repeat the native program's parenthesization, retaining every model error."""
    r = ins[0]
    d, nr, nz, shifted = fields
    r2 = r*r
    r4 = r2*r2
    r8 = r4*r4
    p = r8*r8
    rd = r*d
    u = (rd*rd + nr*nr) + nz*nz
    n = -((((r2*shifted)*((d+d) - shifted) + nr*nr) + nz*nz)
          + p*Model.rational(HEIGHTS[0]**2 - HEIGHTS[1]**2))
    ds, ps, us, ns = (x.bound() for x in (d, p, u, n))
    if min(ds[0], ps[0], ns[0]) <= 0:
        raise ValueError('outside the positive compensated-numerator comparison')
    return (ds, ps, us, ns), (
        *square_root_bounds(HEIGHTS[1]**2 - ns[1]/ps[0], HEIGHTS[1]**2 - ns[0]/ps[1]),
        *square_root_bounds(us[0]/ds[1]**2, us[1]/ds[0]**2))


def provider(a, i, radius, data, static):
    label, packet, traces, _ = load(radius)
    ins = native.row_inputs(i, traces[1], traces[0])
    # The shared input also proves that the independently archived negative row fits the
    # reflected model. Only the maximum of the original two outgoing radii is used.
    old, src, audited = native.emit_input(i, 1, ins, paired=True)
    tag = native.signed_prefix(i, 1, True)
    stem = tag if radius == 470 else f'DommaschkNativeAction{label}Paired{i:03d}'
    name = old.replace(tag, stem)
    src = src.replace(old, name)
    if radius != 470:
        for direction, tr in zip(('Back', 'Fwd'), traces, strict=True):
            index = f'DommaschkPositionFrames{direction}.block{i//16}[{i%16}]'
            if src.count(index) != 1:
                raise ValueError('unexpected base frame lookup')
            src = src.replace(index, step(tr['steps'][i]))
    deps = [digest(DESIGN/(m+'.trace')) for m in (
        'DommaschkNativeActionModel', 'DommaschkPreMirrorSigns', f'DommaschkHarmonicBlock{i//8:02}',
        'DommaschkPositionFramesFwd')]
    cache = a.model_cache if radius == 470 else a.cache
    inputs = compile_modules(cache/name, [(name,src,audited)], [], [native.INPUT_PACKAGE,digest(packet),deps],
                             a,native.INPUT_PACKAGE)
    fields, values = [], []
    for k, (sta, channels) in enumerate(zip(static,data,strict=True)):
        mod = stem+native.FIELDS[k]
        leaf, val = native.emit_horner_field(mod, native.SP_FIELDS[k], channels, ins, sta[1]['module'],
                                             name, native.DATA_PACKAGE, native.INPUT_PACKAGE)
        fields.append(compile_modules(cache/mod, [leaf], [union(cache,[sta,inputs])],
                                      [native.FIELD_PACKAGE,sta[1]['key'],inputs[1]['key']],a,native.FIELD_PACKAGE))
        values.append(val)
    mod, source, thms = native.emit_physical(i,1,ins,name,fields,values,paired=True)
    if mod != tag:
        raise ValueError('unexpected native physical provider')
    # Only the namespace declaration is local to this module.
    source = source.replace('namespace PlasmaLean.Design.'+tag+'\n', 'namespace PlasmaLean.Design.'+stem+'\n')
    source = source.replace('end PlasmaLean.Design.'+tag+'\n', 'end PlasmaLean.Design.'+stem+'\n')
    leaves = [*static,inputs,*fields]
    physical = compile_modules(cache/stem, [(stem,source,thms)], [union(cache,leaves)],
                               [native.OUTPUT_PACKAGE,digest(DESIGN/'DommaschkNativeActionReflection.trace'),
                                *[r['key'] for _,r in leaves]],a,native.OUTPUT_PACKAGE)
    return [inputs,*fields,physical], ranges(ins,values), digest(packet)


def direct(i, providers, enclosures):
    name = f'DommaschkPairedActionProfile{i:03d}'
    src = native.header(name, ['PlasmaLean.Design.'+THEORY,
                               *[native.OUTPUT_PACKAGE+'.'+m for m in providers]])
    src += ('open Certificates.PositionFrameSlabs DommaschkPhysicalActionPanel DommaschkMirrorTubeCrossing\n'
            'open DommaschkPairedActionProfiles DommaschkFirstMirrorLaunchSign\n'
            'open Set DommaschkBounceField\n')
    audit = []
    for side, mod, (boxes, limits) in zip(('inner','outer'),providers,enclosures,strict=True):
        src += f'def {side} : Bounds := ⟨'+', '.join(str(v) for v in limits)+'⟩\n'
        for back, branch in [(False,'forward'),(True,'backward')]:
            phi = '(-t)' if back else 't'
            row = mod + ('.backRow' if back else '.row')
            thm = side+'_'+branch
            audit.append(thm)
            physical = 'backward_physical' if back else 'physical'
            src += f'''theorem {thm} {{prev : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}}
    (ht : t ∈ Icc ({i}/64 : ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {row} ({i}/64)).tube t) : {side}.At {phi} x := by
  obtain ⟨hr,hd,_,hp,hu,hn⟩ := {mod}.{physical} ht hx
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
'''
            for k, member, bounds in zip(('D','P','U','N'),('hd','hp','hu','hn'),boxes,strict=True):
                lo,hi = bounds
                src += (f'  have h{k} := DommaschkPairedActionProfiles.range '
                        f'(lo := {lo}) (hi := {hi}) hs {member} (by kernel_fact)\n')
            src += f'''  have dpos : 0 < atPoint dD (x 0) {phi} (x 1) := lt_of_lt_of_le (by norm_num) hD.1
  have eqw := weight_eq hr dpos
  have fpos : 0 ≤ strength {phi} x := norm_nonneg _
  have wpos : 0 ≤ weight {phi} x := by rw [eqw]; positivity
  have square : (atPoint dD (x 0) {phi} (x 1) * weight {phi} x)^2 =
      (x 0)^16 * (strength {phi} x)^2 := by rw [eqw]; field_simp [dpos.ne']
  rw [← square] at hU
  constructor
  · apply field_range fpos hP hN <;> norm_num [{side},height]
  · apply weight_range wpos hD hU <;> norm_num [{side}]
'''
            regular = thm+'_regular'
            audit.append(regular)
            dlo, dhi = boxes[0]
            src += f'''theorem {regular} {{prev : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}}
    (ht : t ∈ Icc ({i}/64 : ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {row} ({i}/64)).tube t) :
    0 < x 0 ∧ 0 < atPoint dD (x 0) {phi} (x 1) := by
  obtain ⟨hr,hd,_⟩ := {mod}.{physical} ht hx
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have dd := DommaschkPairedActionProfiles.range (lo := {dlo}) (hi := {dhi}) hs hd (by kernel_fact)
  exact ⟨hr, lt_of_lt_of_le (by norm_num) dd.1⟩
'''
    for back, branch in [(False,'forward'),(True,'backward')]:
        phi = '(-t)' if back else 't'
        row = 'backRow' if back else 'row'
        audit.append(branch)
        src += f'''theorem {branch} {{a b : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x y : Plane}}
    (ht : t ∈ Icc ({i}/64 : ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab a {providers[0]}.{row} ({i}/64)).tube t)
    (hy : y ∈ (physicalSlab b {providers[1]}.{row} ({i}/64)).tube t) : Compared {phi} x y := by
  apply compare_ranges (inner_{branch} ht hx) (outer_{branch} ht hy) <;> norm_num [inner,outer]
'''
    return name, src+native.footer(name), audit


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--row',type=int,default=0,choices=range(325),metavar='0..324')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-action-profiles')
    p.add_argument('--model-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--output',type=Path,required=True)
    a = p.parse_args()
    a.cache, a.model_cache = a.cache.resolve(), a.model_cache.resolve()
    def lake(*args):
        return subprocess.check_output(['lake','env',*args],cwd=ROOT,text=True).strip()
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    data = native.static_data()
    static = []
    for k, channels in enumerate(data):
        item = native.emit_static(k, channels)
        static.append(compile_modules(a.model_cache/item[0],[item],[],
                      [native.DATA_PACKAGE,digest(DESIGN/'DommaschkNativeActionModel.trace')],a,native.DATA_PACKAGE))
    pairs = [provider(a,a.row,rad,data,static) for rad in (470,478)]
    groups, bounds, packets = zip(*pairs,strict=True)
    names = [g[-1][1]['module'] for g in groups]
    item = direct(a.row,names,bounds)
    deps = [*static,*(leaf for group in groups for leaf in group)]
    overlay = union(a.cache,deps)
    root, r = compile_modules(a.cache/item[0],[item],[overlay],
                              [lake('lean','--version'),packets,digest(DESIGN/(THEORY+'.trace')),
                               *[leaf['key'] for _,leaf in deps]],a,PACKAGE)
    report = {k:r[k] for k in ('key','module','theorems','axioms','wall_seconds','peak_rss_kib')}
    report.update(row=a.row,packets=packets,providers=names,limits=[[str(x) for x in b[1]] for b in bounds],
                  import_paths=[str(root),str(overlay)])
    save(a.output,report)
    print(r['module'],r['key'],flush=True)


if __name__ == '__main__':
    main()
