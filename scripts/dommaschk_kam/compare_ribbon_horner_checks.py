"""Compare two accepted original ribbon groups, including every stored physical field accumulator."""
import argparse
import json
from pathlib import Path
import re

from verify_grouped_central_defects import FIELDS
from verify_grouped_central_defects import INTEGER_MARKER
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,RECORD,digest,save
from verify_ribbon_central_group import authenticate
from ribbon_central_data import WITNESS_SHA


def read(path,integer):
    rows=json.loads(path.read_text())
    pairs={}
    for r in rows:
        pairs.setdefault(r['index'],[]).append(r)
    memo={}
    for i,pair in pairs.items():
        authenticate(pair,pair[0]['tile'],i,memo)
    first=rows[0]
    root,overlay=map(Path,first['import_paths'])
    a,b=first['central_group']
    stem=f'DommaschkRibbon{first["tile"]}Central{a:03}To{b:03}'
    parent=(overlay/FIELDS/(stem+'Z.olean')).resolve().parent.parent
    field=admitted(parent,stem+'Z',first['field_key'])
    row=admitted(root,first['import_module'],first['key'])
    values={}
    for tag in ('D','R','Z'):
        source=(parent/FIELDS/(stem+tag+'.lean')).read_text()
        backend='DommaschkDyadicHorner.Run' if integer else 'DommaschkVariableHorner.Run'
        if backend not in source:
            raise ValueError(f'expected {backend} on actual field {tag}')
        values[tag]=re.findall(r'^(?:private )?def (\w+) : Model := (ofDyadic [^\n]+)$',source,re.MULTILINE)
        if not values[tag] or values[tag][-1][0]!='model':
            raise ValueError(f'missing physical field output for {tag}')
    inp=(parent/FIELDS/(stem+'Inputs.lean')).read_bytes()
    physical=(root/first['package']/(first['import_module']+'.lean')).read_bytes()
    return field,row,values,inp,physical


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--original',type=Path,required=True)
    p.add_argument('--integer',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--activate-ribbon',type=Path,help='select the verified integer proof for future ribbon handoffs')
    p.add_argument('--activate-endpoints',type=Path,nargs='+',
                   help='select the same integer theorem on these original grouped endpoint campaign directories')
    args=p.parse_args()
    f0,r0,vs0,inp0,src0=read(args.original,False)
    f1,r1,vs1,inp1,src1=read(args.integer,True)
    if inp0!=inp1 or vs0!=vs1 or src0!=src1 or r0['theorems']!=r1['theorems'] or r0['axioms']!=r1['axioms']:
        raise ValueError('the certified coefficients, radii, original signed budgets or theorem names differ')
    if f0['key']==f1['key']:
        raise ValueError('both receipts use the same field proof')
    def stats(f,r):
        return dict(field_key=f['key'],field_seconds=f['wall_seconds'],row_key=r['key'],row_seconds=r['wall_seconds'],
                    peak_rss_kib=max(f['peak_rss_kib'],r['peak_rss_kib']))
    out=dict(field_models={t:len(v) for t,v in vs0.items()},signed_theorems=r0['theorems'],axioms=r0['axioms'],
        original=stats(f0,r0),integer=stats(f1,r1),field_speedup=f0['wall_seconds']/f1['wall_seconds'],
        full_speedup=(f0['wall_seconds']+r0['wall_seconds'])/(f1['wall_seconds']+r1['wall_seconds']))
    save(args.output,out)
    destinations=[]
    if args.activate_ribbon:
        destinations.append((args.activate_ribbon,WITNESS_SHA))
    for root in args.activate_endpoints or []:
        info=json.loads((root/'status.json').read_text())
        if root.name not in ('q0r523','q0r531','q1r456','q1r464','q1r509','q1r517') or info['endpoint']!=root.name:
            raise ValueError(f'unknown endpoint continuation at {root}')
        packet=RECORD.with_name('bounce_frame_'+root.name[:2]+'_u'+root.name[3:]+'.json.gz')
        checksum=digest(packet)
        if checksum!=info['packet_sha256']:
            raise ValueError(f'original endpoint packet mismatch at {root}')
        destinations.append((root,checksum))
    if destinations and (out['field_speedup']<=1 or out['full_speedup']<=1):
        p.error('both the physical field and full signed group must improve before changing a campaign')
    for root,checksum in destinations:
        root.mkdir(parents=True,exist_ok=True)
        save(root/INTEGER_MARKER,dict(packet_sha256=checksum,theory_sha256=digest(DESIGN/'DommaschkDyadicHorner.trace'),
            backend='checked-dyadic-multiply-add',original_key=f0['key'],integer_key=f1['key']))
    print('identical concrete models:',out['field_models'],'field speedup',out['field_speedup'],flush=True)


if __name__=='__main__':
    main()
