"""Compare two normalized QA2R action models already used by the physical action packets."""
import argparse
from fractions import Fraction as F
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_mirror_pilot import HEIGHTS, Model, evaluate, polynomial_data
from bounce_phase_strength import ShiftedStrength
from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules, union
from verify_centered_strength import Arithmetic
import verify_native_action_models as native
from verify_paired_action_profiles import native_provider
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load


THEORY = 'DommaschkNativePairedProfiles'
PACKAGE = 'NativePairedProfileCache'
RATIO = F(3999,4000)
CEILING = F(17,16)
SHIFT = 2*CEILING*F(1,18000)


def native_columns(ins, fields):
    r, *_ = ins
    d,nr,nz,shifted = fields
    r2 = r*r
    r4 = r2*r2
    r8 = r4*r4
    r16 = r8*r8
    rd = r*d
    u = (rd*rd + nr*nr) + nz*nz
    n = -((((r2*shifted)*((d+d)-shifted) + nr*nr) + nz*nz)
          + r16*Model.rational(HEIGHTS[0]**2-HEIGHTS[1]**2))
    return (d,r16,u,n)


def arithmetic(sides):
    a = Arithmetic()
    for suffix,columns in zip(('I','O'),sides,strict=True):
        for key,m in zip(('d','p','u','n'),columns,strict=True):
            a.leaf(key+suffix,m,key+suffix,'in'+key+suffix)
    a.literal('k2',RATIO**2)
    a.literal('high',CEILING**2-HEIGHTS[1]**2)
    a.literal('shift',SHIFT)
    op = a.op
    for end in ('I','O'):
        op('dd'+end,'d'+end,'*','d'+end)
        op('cap'+end,'n'+end,'+',op('head'+end,'high','*','p'+end))
    op('arc',op('vO','uO','*','ddI'),'-',op('vI','k2','*',op('scaledI','uI','*','ddO')))
    op('drop',op('change',op('qO','nO','*','pI'),'-',op('qI','nI','*','pO')),
       '-',op('delta','shift','*',op('product','pI','*','pO')))
    for tag in ('dI','dO','capI','capO','arc','drop'):
        if a.interval(tag)[0] <= 0 and tag != 'drop':
            raise ValueError('uncertified native margin '+tag)
    return a


def screen():
    raw = polynomial_data()
    polynomials = [p[0] for p in raw]+[ShiftedStrength(raw).diff[0]]
    records = [load(k) for k in (470,478)]
    rows = []
    for i in range(325):
        pair = []
        for _,_,traces,_ in records:
            ins = native.row_inputs(i,traces[1],traces[0])
            r,_,z,angles = ins
            fields = [evaluate(p,(r,z),angles)[0] for p in polynomials]
            pair.append(native_columns(ins,fields))
        a = arithmetic(pair)
        rows.append({k:str(a.values[k].bound()[0]) for k in ('arc','drop','capI','capO')})
    direct = [i for i,r in enumerate(rows) if F(r['drop']) >= 0]
    return dict(status='external exact arithmetic',packets=[digest(p) for _,p,_,_ in records],
                rows=rows,direct=direct,centered=[i for i in range(325) if i not in direct])


def source(i, names, columns):
    a = arithmetic(columns)
    direct = a.values['drop'].bound()[0] >= 0
    name = f'DommaschkNativePairedProfile{i:03d}'
    out = native.header(name,['PlasmaLean.Design.'+THEORY,*(native.OUTPUT_PACKAGE+'.'+m for m in names)])
    out += ('open Certificates.PositionFrameSlabs DommaschkPairedActionProfiles DommaschkPairedArcRatio\n'
            'open DommaschkNativeActionGeometry DommaschkNativePairedProfiles DommaschkFirstMirrorLaunchSign\n'
            'open DommaschkMirrorTubeCrossing DommaschkBounceField\n')
    out += '\n'.join(a.defs)
    out += '\nprivate theorem margins {s dI dO pI pO uI uO nI nO fI fO : ℝ} (hs : |s| ≤ 1)\n'
    for e, m in zip(('I','O'),names,strict=True):
        for k,model in [('d','den'),('p','r16'),('u','u'),('n','num')]:
            out += f'    (in{k}{e} : {m}.{model}.Mem s {k}{e})\n'
        out += (f'    (p{e}pos : 0 < p{e}) (gap{e} : n{e} = '
                f'p{e} * (((height true : ℚ) : ℝ)^2 - f{e}^2))\n')
    out += ('    : 0 < dI ∧ 0 < dO ∧ fI ≤ 17/16 ∧ fO ≤ 17/16 ∧ '
            '0 ≤ uO*(dI*dI) - ratio^2*(uI*(dO*dO))')
    if direct:
        out += ' ∧ 2*(17/16:ℝ)*(1/18000) ≤ fI^2-fO^2'
    out += ' := by\n'+'\n'.join(a.body)
    finals = ['dI','dO','capI','capO','arc']+(['drop'] if direct else [])
    out += '\n  refine ⟨'+', '.join('?_ ' for _ in finals)+'⟩\n'
    for tag in finals:
        if tag[0] == 'd' and tag != 'drop':
            out += f'  · linarith only [bound{tag}.1]\n'
            continue
        if tag.startswith('cap'):
            k = tag[-1]
            out += f'  · apply native_ceiling (h := ((height true:ℚ):ℝ)) p{k}pos\n'
        elif tag == 'drop':
            out += '  · apply native_field (h := ((height true:ℚ):ℝ)) pIpos pOpos\n'
        else:
            out += '  ·\n'
        out += (f'    convert (by linarith only [bound{tag}.1] : 0 ≤ val{tag}) using 1\n'
                f'    dsimp only [{", ".join(a.locals)}]\n'
                '    norm_num [height, ratio, gapI, gapO] <;> ring\n')
    audit = []
    for neg,tag,physical in [(False,'forward','physical'),(True,'backward','backward_physical')]:
        phi = '(-t)' if neg else 't'
        row = 'backRow' if neg else 'row'
        short = tag+'_bounds'
        audit.append(short)
        args = (f'{{a b : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x y : Plane}}\n'
                f'    (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))\n'
                f'    (hx : x ∈ (physicalSlab a {names[0]}.{row} ({i}/64)).tube t)\n'
                f'    (hy : y ∈ (physicalSlab b {names[1]}.{row} ({i}/64)).tube t)')
        out += (f'theorem {short} {args} : strength {phi} x ≤ 17/16 ∧ strength {phi} y ≤ 17/16 ∧ '
                f'ratio * weight {phi} x ≤ weight {phi} y')
        if direct:
            out += f' ∧ 2*(17/16:ℝ)*(1/18000) ≤ (strength {phi} x)^2-(strength {phi} y)^2'
        out += ' := by\n'
        for end,model,mem in zip(('I','O'),names,('hx','hy'),strict=True):
            out += f'  obtain ⟨r{end},d{end},_,p{end},u{end},n{end}⟩ := {model}.{physical} ht {mem}\n'
        out += f'''  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith only [ht.1],by linarith only [ht.2]⟩
  obtain ⟨di,doo,ci,co,arc{",drop" if direct else ""}⟩ := margins hs dI pI uI nI (pow_pos rI _) rfl dO pO uO nO (pow_pos rO _) rfl
  have wi := native_weight_identity (φ := {phi}) (x := x) rI di
  have wo := native_weight_identity (φ := {phi}) (x := y) rO doo
  exact ⟨ci,co,native_ratio di doo wo.1 wi.2 wo.2 arc{",drop" if direct else ""}⟩
'''
        if direct:
            audit.append(tag)
            out += f'''theorem {tag} {args} : Compared {phi} x y := by
  obtain ⟨ci,co,w,dr⟩ := {short} ht hx hy
  exact compared_of_squared ci co dr w
'''
    return (name,out+native.footer(name),audit), direct


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--screen',action='store_true')
    mode.add_argument('--row',type=int,choices=range(325),metavar='0..324')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/native-paired-profiles')
    p.add_argument('--output',type=Path,required=True)
    a = p.parse_args()
    if a.screen:
        save(a.output,screen())
        return
    def lake(*args):
        return subprocess.check_output(['lake','env',*args],cwd=ROOT,text=True).strip()
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    raw = native.static_data()
    model_cache = ROOT/'.lake/native-action-checks'
    shared = SimpleNamespace(**{**vars(a),'cache':ROOT/'.lake/paired-action-profiles',
                                 'model_cache':model_cache})
    static = native.verify_static(SimpleNamespace(**{**vars(shared),'cache':model_cache,'fields':range(4)}),raw)
    providers = [native_provider(shared,a.row,r,raw,static) for r in (470,478)]
    names = [pieces[-1][1]['module'] for pieces,_,_,_ in providers]
    columns = [native_columns(ins,fields) for _,ins,fields,_ in providers]
    packets = [p[-1] for p in providers]
    item,direct = source(a.row,names,columns)
    deps = [*static,*(proof for pieces,_,_,_ in providers for proof in pieces)]
    overlay = union(a.cache.resolve(),deps)
    keys = [record['key'] for _,record in deps]
    root,r = compile_modules(a.cache.resolve()/item[0],[item],[overlay],
        [lake('lean','--version'),keys,packets,digest(DESIGN/(THEORY+'.trace'))],a,PACKAGE)
    result = {k:r[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')}
    result.update(row=a.row,direct=direct,packets=packets,providers=names,model_keys=keys,
                  import_paths=[str(root),str(overlay)])
    save(a.output,result)
    print(item[0],r['key'],'direct' if direct else 'arclength and ceilings',flush=True)


if __name__=='__main__':
    main()
