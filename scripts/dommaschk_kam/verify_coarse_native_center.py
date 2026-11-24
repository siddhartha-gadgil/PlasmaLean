"""Transfer an entire native Q0R478 central cover to the coarse lower-action archive."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_secondary_cover import birth
from verify_coarse_secondary_lower import packet_inputs
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_secondary_action_cover import BAND_MODULE,THEORY,header
from verify_signed_mirror_passage import merge_import_roots


PACKAGE='CoarseNativeCenterCache'


def source(k, old, pack):
    name=f'DommaschkCoarseNativeCenter{k:03}'
    table=pack['module']
    imports=['PlasmaLean.Certificates.WeakenLowerActionCover',
             old['package']+'.'+old['module'],pack['package']+'.'+table]
    src=header(name,imports)
    src+=f'''
abbrev start : ℝ := ({327-k}:ℝ)/64-327/64
abbrev blocks := ({table}.slabs.drop {327-k}).take {2*k}
def Covered (y : ℝ → Plane) : Prop :=
  Covers false (density y) (field y) DommaschkSecondaryActionMass.height start blocks
'''
    # Each certificate term reduces at most eight pairs of 48-cell blocks. The list equalities
    # below reuse the original block objects (including each block's independent root check).
    names=[]
    for j in range(0,2*k,8):
        count=min(8,2*k-j)
        part=f'piece{j//8}'
        c=f'c{j//8}'
        f=f'f{j//8}'
        names.append((c,f,part))
        src+=f'''private abbrev {c} := ({table}.slabs.drop {327-k+j}).take {count}
private abbrev {f} := (DommaschkActionQ0R478.slabs.drop {327-k+j}).take {count}
private theorem {part} : blocksLowerLE {c} {f} = true := by with_unfolding_all rfl
'''
    cs=' ++ '.join(c for c,_,_ in names)
    fs=' ++ '.join(f for _,f,_ in names)
    proof=names[-1][2]
    for _,_,piece in reversed(names[:-1]):
        proof=f'blocksLowerLE_append {piece} ({proof})'
    src+=f'''
theorem columns : blocksLowerLE blocks {old['module']}.blocks = true := by
  rw [show blocks = {cs} by with_unfolding_all rfl,
      show {old['module']}.blocks = {fs} by with_unfolding_all rfl]
  exact {proof}

theorem cover {{y : ℝ → Plane}} (track : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows {k} y) :
    Covered y := covers_of_blocksLowerLE columns ({old['module']}.cover track)
end PlasmaLean.Design.{name}
'''
    return name,src,['cover']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for f in ['packet','native-cover','output']:
        p.add_argument('--'+f,required=True,type=Path)
    p.add_argument('--signed',type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-native-center')
    a=p.parse_args()
    env(a)
    pack,packet_root,_,blocks,_,_=packet_inputs(a.packet)
    old=json.loads(a.native_cover.read_text())
    k=old['pairs']
    if (not 1<=k<=325 or old['packet_sha256']!=pack['packet_sha256'] or
            old['module']!=f'DommaschkLowerCoverQ0R478L{327-k:03}R{327+k:03}'):
        p.error('expected a genuine centered native physical cover at the same launch')
    roots=list(map(Path,old['import_paths']))
    admitted(roots[0],old['module'],old['key'])
    keys=[a.version,pack['key'],old['key'],digest(DESIGN.parent/'Certificates/WeakenLowerActionCover.trace')]
    overlay=merge_import_roots(a.cache/'native',[*roots,packet_root],keys)
    decl=source(k,old,pack)
    base,rec=compile_modules(a.cache/decl[0],[decl],[overlay],keys,a,PACKAGE)
    out={k:rec[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
    out.update(package=PACKAGE,pairs=k,physical_cells=96*k,native=old['key'],coarse_packet=pack['key'],
               packet_sha256=pack['packet_sha256'],import_paths=list(map(str,[base,overlay])))
    if a.signed:
        pf=json.loads(a.signed.read_text())
        n=pf['length_each_direction']
        pm=f'DommaschkSignedPrefixQ0R478{n:03}'
        if pf['module']!=pm or pf['packet_sha256']!=pack['packet_sha256'] or n<=k:
            p.error('expected an actual signed trajectory beyond the central interval')
        paths=[Path(pf['proof_root']),Path(pf['import_path'])]
        admitted(paths[0],pm,pf['key'])
        deps=[*keys,rec['key'],pf['key'],digest(DESIGN/(THEORY+'.trace'))]
        joined=merge_import_roots(a.cache/'birth',[base,overlay,*paths],deps)
        item=birth(n,k,pm,rec['module'],PACKAGE,blocks)
        root,br=compile_modules(a.cache/item[0],[item],[joined],deps,a,'CoarseCenterBirthCache')
        out['birth']={k:br[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
        out['birth']['import_paths']=list(map(str,[root,joined]))
    save(a.output,out)
    print(rec['module'],rec['key'],flush=True)


if __name__=='__main__':
    main()
