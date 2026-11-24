"""Glue consecutive 16-panel blocks and apply their exact mass on one actual signed birth."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

from screen_secondary_action_archive import archive
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_physical_action import PACKAGE as CELL_PACKAGE
from verify_coarse_secondary_lower import packet_inputs
import verify_coarse_secondary_well as coarse_well
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
import verify_secondary_action_cover as native
import verify_secondary_first_well_action as native_well
from verify_signed_mirror_passage import merge_import_roots


def subst_once(src, old, new):
    if src.count(old)!=1:
        raise ValueError(f'expected a single quadrature parameter in the proof: {old}')
    return src.replace(old,new)


def tree_piece(l,r,pack,children,leaves):
    name=f'DommaschkCoarseLowerCoverQ0R478L{l:03}R{r:03}'
    table=pack['module']
    packet_import=pack['package']+'.'+table
    band=native.BAND_MODULE
    if children:
        # The list-append argument in N138 depends only on the lengths and common clock.
        old,src,thms=native.node(l,r,children)
        src=src.replace(old,name)
        src=subst_once(src,'module\n','module\npublic import '+packet_import+'\n')
        src=subst_once(src,'DommaschkActionQ0R478.slabs.drop',table+'.slabs.drop')
        _,first,width=children[0]
        if width==1:
            src=subst_once(src,'    change start + (1:ℝ)/64 = _',
                f'    rw [show {first}.blocks.length = 1 by with_unfolding_all rfl,Nat.cast_one]')
        return name,src,thms
    imports=['PlasmaLean.Design.'+native.THEORY,native.BAND+'.'+band,packet_import]
    imports.extend(f'{CELL_PACKAGE}.{m}' for m in leaves)
    src=native.header(name,imports)
    k=max(native.ref(l)[0],native.ref(r-1)[0])+1
    literals=', '.join(f'{m}.block' for m in leaves)
    goals=', '.join(['?_']*(r-l)+['trivial'])
    src+=f'''
abbrev blocks := ({table}.slabs.drop {l}).take {r-l}
abbrev start : ℝ := ({l}:ℝ)/64 - 327/64
def Covered (y : ℝ → Plane) : Prop :=
  Covers false (density y) (field y) DommaschkSecondaryActionMass.height start blocks

theorem cover {{y : ℝ → Plane}} (track : Tracks {band}.fwdRows {band}.backRows {k} y) : Covered y := by
  unfold Covered
  have original : blocks = [{literals}] := by with_unfolding_all rfl
  rw [original]
  refine ⟨{goals}⟩
'''
    for j,m in zip(range(l,r),leaves,strict=True):
        i,_,branch,part=native.ref(j)
        src+=f'''  · have hi : {i} < {band}.{branch}Rows.length := by change {i}<327; norm_num
    obtain ⟨prev,tube⟩ := track.{part} {i} (by norm_num) hi
    have link : {band}.{branch}Rows[{i}] = {m}.row := by with_unfolding_all rfl
    rw [link] at tube
    have h := {m}.cells (prev := prev) (y := y) (by
      simpa only [Bool.false_eq_true,↓reduceIte,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,
        show ({i}:ℝ)+1={i+1} by norm_num] using tube)
    change Cells false (fun t => DommaschkPhysicalActionPanel.arcDensity (y t 0) t (y t 1))
      (fun t => DommaschkMirrorTubeCrossing.strength t (y t)) _ _ 48 {m}.block.packed
    simp only [{m}.phase,zero_add] at h
    convert h using 1 <;> norm_num [start]
'''
    return name,src+f'end PlasmaLean.Design.{name}\n',['cover']


def birth(n,k,pm,cover,cpack,blocks):
    old,src,decs=native.bind(n,k,pm,cover,cpack)
    name=old.replace('BirthCover','CoarseBirthCover')
    src=src.replace(old,name)
    fine=sum(m for _,m in archive()[327-k:327+k])
    m=sum(m for _,m in blocks[327-k:327+k])
    den=3072*2**40
    before,after=Fraction(fine,den),Fraction(m,den)
    src=subst_once(src,f'abbrev mass : ℝ := {before.numerator}/{before.denominator}',
                   f'abbrev mass : ℝ := {after.numerator}/{after.denominator}')
    src=subst_once(src,f'total {cover}.blocks = {fine}',f'total {cover}.blocks = {m}')
    return name,src,decs


def final_birth(n,pm,cover,cpack):
    old,src,decs=native_well.birth(n,pm,cover)
    src=src.replace(native_well.PACKAGE+'.'+native_well.NAME,coarse_well.PACKAGE+'.'+coarse_well.NAME)
    src=src.replace(native_well.NAME,coarse_well.NAME)
    src=subst_once(src,native.package(5,649)+'.'+cover,cpack+'.'+cover)
    src=subst_once(src,'(-322/64:ℝ)','(-325/64:ℝ)')
    return old.replace(native_well.NAME,coarse_well.NAME),src,decs


def check(a):
    center=None
    if a.native_center:
        center=json.loads(a.native_center.read_text())
        width=center['pairs']
        if not 0<width<=a.pairs or center['module']!=f'DommaschkCoarseNativeCenter{width:03}':
            raise ValueError('the native center must fit inside the requested coarse cover')
    if a.wait:
        while not all((a.row_cache/'rows'/f'{i:03}.json').is_file()
                      for i in range(center['pairs'] if center else 0,a.pairs)):
            time.sleep(30)
    env(a)
    pack,packet_root,_,blocks,count,_=packet_inputs(a.packet)
    band=json.loads(a.band.read_text())
    if band['module']!=native.BAND_MODULE or band['packet_sha256']!=pack['packet_sha256']:
        raise ValueError('expected the actual 327-row mirror branch of the same signed witness')
    band_roots=list(map(Path,band['import_paths']))
    admitted(band_roots[0],band['module'],band['key'])
    common=[a.version,pack['key'],band['key'],digest(DESIGN/(native.THEORY+'.trace'))]
    anchor=merge_import_roots(a.cache/'anchor',[packet_root,*band_roots],common)
    if center:
        if center['coarse_packet']!=pack['key'] or center['packet_sha256']!=pack['packet_sha256']:
            raise ValueError('native physical center belongs to a different coarse packet')
        center_paths=list(map(Path,center['import_paths']))
        admitted(center_paths[0],center['module'],center['key'])
        left,right=327-center['pairs'],327+center['pairs']
    def tree(l,r):
        if center and (l,r)==(left,right):
            return center,center_paths
        mid=native.split(l,r)
        if center and l<left<r:
            mid=left
        elif center and l<right<r:
            mid=right
        children=None
        leaves=[]
        parents=[]
        if mid is None:
            for j in range(l,r):
                i,_,_,_=native.ref(j)
                sign=1 if j>=327 else -1
                rows=json.loads((a.row_cache/'rows'/f'{i:03}.json').read_text())
                entry,=[row for row in rows if row['direction']==sign]
                if (entry['coarse_packet'], entry['index'], entry['chronological_block'])!=(pack['key'],i,j):
                    raise ValueError(f'different signed physical row at chronological block {j}')
                paths=list(map(Path,entry['import_paths']))
                admitted(paths[0],entry['module'],entry['key'])
                parents.append((entry,paths))
                leaves.append(entry['module'])
        else:
            parents=[tree(l,mid),tree(mid,r)]
            children=[(rec['package'],rec['module'],w) for (rec,_),w in zip(parents,[mid-l,r-mid],strict=True)]
        keys=[*common,*[rec['key'] for rec,_ in parents]]
        pkg=f'CoarseLowerCover{r-l:03}Cache'
        overlay=merge_import_roots(a.cache/'tree',[p for _,paths in parents for p in paths],keys)
        decl=tree_piece(l,r,pack,children,leaves)
        base,rec=compile_modules(a.cache/decl[0],[decl],[overlay,anchor],keys,a,pkg)
        return {**rec,'package':pkg},[base,overlay]
    k=a.pairs
    rec,roots=tree(327-k,327+k)
    out={k:rec[k] for k in ['module','package','key','axioms','theorems']}
    out.update(pairs=k,physical_cells=96*k,packet_sha256=pack['packet_sha256'],coarse_packet=pack['key'],
               import_paths=list(map(str,[*roots,anchor])))
    save(a.output,out)
    if a.signed:
        while a.wait and not a.signed.exists():
            time.sleep(30)
        prefix=json.loads(a.signed.read_text())
        n=prefix['length_each_direction']
        pm=f'DommaschkSignedPrefixQ0R478{n:03}'
        if prefix['packet_sha256']!=pack['packet_sha256'] or pm!=prefix['module'] or n<=k:
            raise ValueError('the signed prefix must extend beyond the core on the same witness')
        signed=list(map(Path,[prefix['proof_root'],prefix['import_path']]))
        admitted(signed[0],pm,prefix['key'])
        keys=[*common,rec['key'],prefix['key']]
        paths=[*roots,anchor,*signed]
        overlay=merge_import_roots(a.cache/'birth',paths,keys)
        decl=birth(n,k,pm,rec['module'],rec['package'],blocks)
        base,br=compile_modules(a.cache/decl[0],[decl],[overlay],keys,a,'CoarseLowerBirthCache')
        out['birth']={k:br[k] for k in ['module','key','axioms','theorems']}
        out['birth'].update(signed_length=n,import_paths=list(map(str,[base,overlay])))
        if a.well:
            wr=json.loads(a.well.read_text())
            if k!=count or n<=327 or wr['module']!=coarse_well.NAME or wr['packet_sha256']!=pack['packet_sha256']:
                raise ValueError('the first-well proof requires the entire physical lower core and both first contacts')
            wpaths=list(map(Path,wr['import_paths']))
            admitted(wpaths[0],wr['module'],wr['key'])
            deps=[*keys,wr['key']]
            merged=merge_import_roots(a.cache/'well',[*paths,*wpaths],deps)
            decl=final_birth(n,pm,rec['module'],rec['package'])
            wbase,record=compile_modules(a.cache/decl[0],[decl],[merged],deps,a,'CoarseLowerFirstBirthCache')
            out['first_well']={k:record[k] for k in ['module','key','axioms','theorems']}
            out['first_well']['import_paths']=list(map(str,[wbase,merged]))
    save(a.output,out)
    print(out['module'],out['key'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for field in ['packet','band','output']:
        p.add_argument('--'+field,type=Path,required=True)
    p.add_argument('--signed',type=Path)
    p.add_argument('--well',type=Path)
    p.add_argument('--native-center',type=Path,help='reuse an authenticated bulk fine-to-coarse center')
    p.add_argument('--wait',action='store_true',help='await each physical input and keep the verified cover on disk')
    p.add_argument('--pairs',type=int,required=True)
    p.add_argument('--row-cache',type=Path,default=ROOT/'.lake/coarse-secondary-lower')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-secondary-cover')
    a=p.parse_args()
    if not 1<=a.pairs<=325 or (a.well and not a.signed):
        p.error('choose 1 to 325 outward row pairs and supply a signed trajectory for the first-well application')
    check(a)
