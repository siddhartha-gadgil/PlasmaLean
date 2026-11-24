"""Evaluate the 3 values and 6 spatial derivatives on a shared harmonic group."""
from bounce_mirror_pilot import R0M, ZERO
from emit_sparse_taylor_slab import model_literal, models
from screen_endpoint_jacobian_sharing import native_jet
from screen_sparse_jacobians import field_jet
from verify_backward_physical_prefix import compile_modules, union
from verify_harmonic_group_exclusion import inputs
from verify_horner_endpoint_jacobian import DATA, SYMBOLS, TAGS
from verify_native_action_models import emit_horner_field, emit_static_field, footer, header, weighted_channels
from verify_physical_trace_slabs import DESIGN, ROOT, digest
from verify_secondary_mirror_slopes import JET


def prepare(args):
    polynomials = [terms for jet in field_jet() for terms in jet]
    channels = weighted_channels(polynomials,[m for fields in native_jet() for m in fields])
    packages = []
    for tag,symbol,group in zip(TAGS,SYMBOLS,channels,strict=True):
        item = emit_static_field('DommaschkHornerJetData'+tag,symbol,group)
        packages.append(compile_modules(ROOT/'.lake/endpoint-horner-jacobians'/item[0],[item],[],
            [DATA,args.keys[1],digest(DESIGN/'DommaschkNativeActionModel.trace')],args,DATA))
    args.native_static = packages
    args.native_links = union(args.cache,packages)
    args.native_data = list(zip(TAGS,SYMBOLS,polynomials,channels,packages,strict=True))


def harmonic_fields(name,tube,with_gradient,args):
    r,z,c,s = tube
    cols = (r-R0M,z,c,s)
    inp,coordinates = inputs(name+'Harmonics',tube)
    terms = [inp]
    data = args.native_data if with_gradient else args.native_data[::3]
    providers = []
    for tag,symbol,poly,channels,(_,static) in data:
        subname = name+'Harmonic'+tag
        item,model = emit_horner_field(subname,symbol,channels,coordinates,static['module'],inp[0],DATA,JET)
        terms.append(item)
        outward = sum(models(poly,cols),ZERO)
        if model.e+sum(abs(x-y) for x,y in zip(model.a,outward.a,strict=True)) > outward.e:
            raise ValueError(f'{subname} misses the outward polynomial by coefficient containment')
        label = {'D':'dD','R':'dnR','Z':'dnZ'}.get(tag,'grad'+tag)
        providers.append((subname,symbol,outward,label))
    src = header(name,[JET+'.'+n for n,_,_,_ in providers])
    src += f'''def trial : Inputs := ⟨{inp[0]}.displacement,{inp[0]}.vertical,{inp[0]}.group.cosine,{inp[0]}.group.sine⟩
'''
    names = []
    for n,symbol,m,label in providers:
        proof = label+'_checked.mem'
        names.append(proof)
        src += f'''def {label}0 : Model := {model_literal(m)}
theorem {proof} {{s u z θ : ℝ}} (hs : |s| ≤ 1)
    (m : trial.Mem s u z (Real.cos θ) (Real.sin θ)) :
    {label}0.Mem s (evR u z (Real.cos θ) (Real.sin θ) {symbol}) :=
  enclose hs ({n}.sound hs m.1 m.2.1 ({inp[0]}.angles hs m.2.2.1 m.2.2.2)) (by kernel_fact)
'''
    terms.append((name,src+footer(name),names))
    return compile_modules(args.cache/name,terms,[args.native_links],
        [args.keys,digest(DESIGN/'DommaschkGroupedHarmonicGap.trace'),
         *[p[1]['key'] for *_,p in data]],args,JET)
