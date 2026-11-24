"""Put several signed phase-zero submirror passages on one pair of embedded QA2R tori."""
import argparse
import json
from pathlib import Path
import subprocess

from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_submirror_birth import PACKAGE
from verify_signed_mirror_passage import merge_import_roots


def declaration(rows):
    name = 'DommaschkCommonSubmirror' + ''.join(f'{label}N{n:03}' for label,n,_ in rows)
    imports = '\n'.join(f'public import {PACKAGE}.{module}' for _,_,module in rows)
    passages = ' ∧\n      '.join(f'{module}.BelowFromBirth uC zC uA zA φ' for _,_,module in rows)
    conclusions = ',\n    '.join(
        f'{module}.from_entry_below (actual .{label.lower()} (by\n'
        f'      simpa [MirrorEndpoint.width, MirrorEndpoint.opposite, azimuth] using small))'
        for label,_,module in rows)
    text = f'''module
{imports}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorLaunch DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
set_option linter.style.longLine false

/-- Choose both embedded KAM tori before the shared physical birth angle and radius labels. -/
theorem from_common_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 →
      {passages} := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,nested,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),fun φ small => ?_⟩
  have actual (e : MirrorEndpoint) (h : |φ - azimuth e.opposite| ≤ e.width) :
      SectionEntry e uC zC uA zA φ :=
    transfer_to_start (by simpa using cC) (by simpa using cA) e h
  exact ⟨{conclusions}⟩

end PlasmaLean.Design.{name}
'''
    return name,text,['from_common_tori']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--births',type=Path,nargs='+',required=True)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/common-submirror-births')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    data = sorted((json.loads(p.read_text()) for p in args.births),key=lambda r:r['endpoint'])
    labels = [r['endpoint'] for r in data]
    if (len(labels)<2 or len(set(labels))!=len(labels)
            or set(labels)-{'Q0R470','Q0R478','Q0R523','Q0R531'}):
        parser.error('require at least two distinct phase-zero radius labels')
    rows,keys,roots = [],[],[]
    for record in data:
        label,n = record['endpoint'],record['signed_length']
        paths = list(map(Path,record['import_paths']))
        name = f'Dommaschk{label}SubmirrorBirth{n:03}'
        if record['module'] != name:
            parser.error(f'wrong physical passage for {label}')
        marker = admitted(paths[0],name,record['key'])
        if f'PlasmaLean.Design.{name}.from_entry_below' not in marker['theorems']:
            parser.error(f'missing section-entry theorem for {label}')
        rows.append((label,n,name))
        keys.append(marker['key'])
        roots.extend(paths)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    overlay = merge_import_roots(args.cache,roots,keys)
    decl = declaration(rows)
    root,result = compile_modules(args.cache/decl[0],[decl],[overlay],
        [lake('lean','--version'),keys,digest(DESIGN/'DommaschkFrameLaunch.trace')],args,
        'CommonSubmirrorBirthCache')
    receipt = {k:result[k] for k in ('key','module','axioms','theorems')}
    receipt.update(signed_lengths=dict((label,n) for label,n,_ in rows),parents=keys,
                   import_paths=[str(root),str(overlay)])
    save(args.output,receipt)
    print(decl[0],result['key'])


if __name__ == '__main__':
    main()
