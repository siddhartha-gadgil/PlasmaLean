"""Attach the 325-pair lower action implication to the certified second upper mirror well."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_coarse_secondary_core import NAME as CORE, PACKAGE as CORE_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_secondary_action_cover import BAND_MODULE
from verify_signed_mirror_passage import merge_import_roots


NAME='DommaschkQ0R478CoarseLowerFirstWell'
PACKAGE='CoarseSecondaryWellCache'
TEMPLATE=Path(__file__).parent/'templates/secondary_lower_well.lean.tpl'


def source():
    # Reuse the entire signed timing argument from the checked native application.
    # Only the interior quadrature theorem and its length change.
    src=TEMPLATE.read_text()
    if src.count('open DommaschkSecondaryActionCore DommaschkSecondaryActionMass')!=1:
        raise ValueError('the native template no longer imports the expected core')
    src=src.replace('module\n','module\npublic import '+CORE_PACKAGE+'.'+CORE+'\n',1)
    src=src.replace('open DommaschkSecondaryActionCore DommaschkSecondaryActionMass',
                    'open '+CORE+' DommaschkSecondaryActionMass')
    src=src.replace('DommaschkQ0R478LowerFirstWell',NAME).replace('322','325').replace('644','650')
    return NAME,src,['forward_regular','backward_regular','on_path','from_passage']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--core',type=Path,required=True)
    p.add_argument('--band',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-secondary-well')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    env(a)
    core,band=[json.loads(path.read_text()) for path in [a.core,a.band]]
    timing=band['timing']
    if (core['module'],core['pairs'],band['module'],timing['module'])!=(
            CORE,325,BAND_MODULE,'DommaschkQ0R478MirrorTimeSeparation'):
        p.error('expected the 325-pair coarse core and the second launch upper-mirror branch')
    roots=[]
    keys=[a.version,digest(DESIGN/'DommaschkLowerActionPath.trace')]
    for r in [core,band,timing]:
        paths=list(map(Path,r['import_paths']))
        admitted(paths[0],r['module'],r['key'])
        roots.extend(paths)
        keys.append(r['key'])
    merged=merge_import_roots(a.cache,roots,keys)
    base,r=compile_modules(a.cache/NAME,[source()],[merged],keys,a,PACKAGE)
    out={k:r[k] for k in ['module','key','axioms','theorems']}
    out.update(pairs=325,core=core['key'],timing=timing['key'],bound=core['mass'],
               packet_sha256=band['packet_sha256'],grounded=False,import_paths=list(map(str,[base,merged])))
    save(a.output,out)
    print(NAME,r['key'],flush=True)


if __name__=='__main__':
    main()
