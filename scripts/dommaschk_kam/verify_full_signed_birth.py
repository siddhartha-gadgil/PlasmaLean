"""Certify the same actual birth, indexed error and first mirrors on the full signed QA2R archive."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, HERE, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


NAME = 'DommaschkFullSignedBirth'
TEMPLATE = HERE/'templates/full_signed_birth.lean.tpl'
CONTACT_MODULES = {
    'SignedMirrorCache': ['DommaschkSignedMirrorBrackets'],
    'SignedSlopeCache': ['DommaschkSignedSlope316', 'DommaschkSignedSlope324'],
    'SubmirrorPrefixCache': ['DommaschkSubmirror316Of325', 'DommaschkUpperSubmirror324Of325'],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paired', required=True, type=Path, help='the 391-pair physical trajectory')
    parser.add_argument('--contacts', required=True, type=Path, help='the N-95 transverse contacts at length 325')
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/full-signed-birth')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pair, contact = (json.loads(path.read_text()) for path in (args.paired, args.contacts))
    packet = digest(RECORD)
    if (pair['slabs_per_direction'] != 391 or pair['maximum_radius_numerator'] != 4022059640817442909
            or pair['coordinate_denominator'] != 2**80):
        parser.error('expected the full 391-row pilot in each direction with its original radius')
    parent_roots = []
    for receipt, name in ((pair, 'DommaschkPairedPrefix391'), (contact, 'DommaschkTransverseMirrorBirth325')):
        if receipt['module'] != name or receipt['packet_sha256'] != packet:
            parser.error(f'required {name} for the phase-zero radius-0.470 witness')
        roots = list(map(Path, receipt['import_paths']))
        admitted(roots[0], name, receipt['key'])
        parent_roots.extend(roots)
    keys = []
    library = Path(contact['import_paths'][1])
    for package, names in CONTACT_MODULES.items():
        for name in names:
            base = (library/package/f'{name}.olean').resolve(strict=True).parent.parent
            keys.append(admitted(base, name, base.name)['key'])

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    args.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    identity = [lake('lean', '--version'), packet, digest(DESIGN/'DommaschkSignedBirthApproach.trace'),
                pair['key'], contact['key'], *keys]
    overlay = merge_import_roots(args.cache, parent_roots, identity)
    declarations = [(NAME, TEMPLATE.read_text(), ['length_rowsFor', 'indexed_error', 'contacts', 'through_birth'])]
    root, accepted = compile_modules(args.cache/NAME, declarations, [overlay], identity, args, 'FullSignedBirthCache')
    result = {key:value for key,value in accepted.items() if key != 'artifacts'}
    result.update(packet_sha256=packet, paired_key=pair['key'], contacts_key=contact['key'],
                  slabs_per_direction=391, maximum_radius_numerator=pair['maximum_radius_numerator'],
                  coordinate_denominator=2**80, import_paths=list(map(str, [root, overlay])))
    save(args.output, result)
    print(NAME, result['key'], flush=True)


if __name__ == '__main__':
    main()
