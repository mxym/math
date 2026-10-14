#!/usr/bin/env python3
"""Literal bytes, documented read ranges and local links; no Lean execution."""
from argparse import ArgumentParser
from pathlib import Path, PurePosixPath
import hashlib
import json
import re


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser=ArgumentParser(); parser.add_argument('--root',type=Path); parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    folder=Path(__file__).resolve().parent
    root=args.root or folder.parents[1]
    manifest=json.loads((folder/'SOURCE_HASHES.json').read_text(encoding='utf-8'))
    bad=[]
    for rel,expected in manifest['files'].items():
        p=folder/rel
        if not p.is_file() or digest(p)!=expected:
            bad.append('packet/'+rel)
    for rel,expected in manifest['inherited_inputs'].items():
        p=root/rel
        if not p.is_file() or digest(p)!=expected:
            bad.append(rel)
    review=json.loads((folder/'MANUSCRIPT_REVIEW.json').read_text(encoding='utf-8'))
    original_root=PurePosixPath(review['source_tree'])
    count=0
    for item in review['source_files']+review['inherited_inputs_actual_reading']:
        rel=str(PurePosixPath(item['path']).relative_to(original_root))
        p=root/rel
        if not p.is_file() or digest(p)!=item['sha256_literal']:
            bad.append('review/'+rel)
        if item in review['source_files']:
            line_count=len(p.read_bytes().splitlines())
            if line_count!=item['line_count'] or item['fresh_read_ranges_inclusive']!=[[1,line_count]]:
                bad.append('complete-read/'+rel)
            count+=line_count
    if count!=review['complete_new_line_count'] or count!=249:
        bad.append('complete new read count')
    links=0
    for name in manifest['files']:
        if name.endswith('.md'):
            p=folder/name
            for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',p.read_text(encoding='utf-8')):
                if target.startswith(('https:','http:','mailto:','#')):
                    continue
                if not (p.parent/target.split('#',1)[0]).is_file():
                    bad.append('link/'+name+' -> '+target)
                links+=1
    if bad:
        raise RuntimeError('Source correspondence failure: '+', '.join(bad))
    record={'status':'PASS','kind':'literal bytes, declared read scope and links; not a mathematical proof',
            'packet_files':len(manifest['files']),'inherited_input_files':len(manifest['inherited_inputs']),
            'reviewed_new_files':len(review['source_files']),'complete_new_read_lines':count,
            'local_links_checked':links,'manifest_sha256':digest(folder/'SOURCE_HASHES.json'),
            'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))


if __name__=='__main__':
    main()
