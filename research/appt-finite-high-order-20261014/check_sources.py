#!/usr/bin/env python3
"""Check literal manuscript/review/input correspondence; no Lean is run."""
from argparse import ArgumentParser
from pathlib import Path
import hashlib
import json
import re


def main():
    ap = ArgumentParser()
    ap.add_argument('--root', type=Path)
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    folder = Path(__file__).resolve().parent
    root = args.root or folder.parents[1]
    manifest = json.loads((folder/'SOURCE_HASHES.json').read_text(encoding='utf-8'))
    bad = []
    for rel, expected in manifest['files'].items():
        p = folder/rel
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != expected:
            bad.append('packet/'+rel)
    for rel, expected in manifest['inherited_inputs'].items():
        p = root/rel
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != expected:
            bad.append(rel)
    review = json.loads((folder/'MANUSCRIPT_REVIEW.json').read_text(encoding='utf-8'))
    for item in review['sources']:
        p = root/item['path']
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != item['sha256']:
            bad.append('review/'+item['path'])
    links = 0
    for name in manifest['files']:
        if not name.endswith('.md'):
            continue
        p = folder/name
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', p.read_text(encoding='utf-8')):
            if target.startswith(('https:', 'http:', 'mailto:', '#')):
                continue
            if not (p.parent/target.split('#', 1)[0]).is_file():
                bad.append('link/'+name+' -> '+target)
            links += 1
    if bad:
        raise RuntimeError('Literal source mismatch: '+', '.join(bad))
    record = {'status': 'PASS', 'kind': 'literal source correspondence, not a mathematical proof',
              'packet_files': len(manifest['files']),
              'inherited_input_files': len(manifest['inherited_inputs']),
              'independently_reviewed_manuscript_files': len(review['sources']),
              'independently_read_lines': review['total_manuscript_lines_read'],
              'local_links_checked': links,
              'manifest_sha256': hashlib.sha256((folder/'SOURCE_HASHES.json').read_bytes()).hexdigest(),
              'new_lean_execution': False, 'expanded_lean_audit': False}
    if args.out:
        args.out.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
