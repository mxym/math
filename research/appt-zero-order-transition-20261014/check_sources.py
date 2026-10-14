#!/usr/bin/env python3
"""Literal bytes, documented read ranges and local links; no Lean execution."""
from argparse import ArgumentParser
from pathlib import Path, PurePosixPath
import hashlib
import json
import re


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def prose_links(markdown):
    # Indented equations and fenced command blocks are not Markdown links.
    lines=[]; fenced=False
    for line in markdown.splitlines():
        if line.lstrip().startswith(('```','~~~')):
            fenced=not fenced
        elif not fenced and not line.startswith(('    ','\t')):
            lines.append(line)
    return re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)', '\n'.join(lines))


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
    review=json.loads((folder/'REVIEW.json').read_text(encoding='utf-8'))
    original_root=PurePosixPath(review['source_tree'])
    count=0
    for item in review['source_files']+review['inherited_inputs_actual_reading']:
        rel=str(PurePosixPath(item['path']).relative_to(original_root))
        p=root/rel
        if not p.is_file() or digest(p)!=item['sha256_literal']:
            bad.append('review/'+rel)
        if item in review['source_files']:
            line_count=len(p.read_bytes().splitlines())
            if line_count!=item['physical_line_count'] or item['actual_read_ranges_inclusive']!=[[1,line_count]] or not item['complete_ordinary_read']:
                bad.append('complete-read/'+rel)
            count+=line_count
        elif p.is_file():
            line_count=len(p.read_bytes().splitlines())
            ranges=item['actual_read_ranges_inclusive']
            if line_count!=item['physical_line_count'] or not ranges or any(
                len(r)!=2 or not (1<=r[0]<=r[1]<=line_count) for r in ranges):
                bad.append('inherited-read-range/'+rel)
    if count!=review['complete_initial_new_line_count'] or count!=488 or review['final_delta'] is not None:
        bad.append('complete new read count')
    supporting_lines=0
    for item in review.get('fresh_supporting_source_reading',[]):
        if 'path' not in item:
            continue
        rel=str(PurePosixPath(item['path']).relative_to(original_root)); p=root/rel
        if not p.is_file() or digest(p)!=item['sha256_literal']:
            bad.append('supporting-source/'+rel)
        else:
            n=len(p.read_bytes().splitlines())
            if n!=item['physical_line_count'] or item['actual_read_ranges_inclusive']!=[[1,n]]:
                bad.append('supporting-read/'+rel)
            supporting_lines+=n
    links=0
    for name in manifest['files']:
        if name.endswith('.md'):
            p=folder/name
            for target in prose_links(p.read_text(encoding='utf-8')):
                if target.startswith(('https:','http:','mailto:','#')):
                    continue
                destination=p.parent/target.split('#',1)[0]
                planned=args.out is not None and destination.resolve()==args.out.resolve()
                if not destination.is_file() and not planned:
                    bad.append('link/'+name+' -> '+target)
                links+=1
    if bad:
        raise RuntimeError('Source correspondence failure: '+', '.join(bad))
    record={'status':'PASS','kind':'literal bytes, declared read scope and links; not a mathematical proof',
            'packet_files':len(manifest['files']),'inherited_input_files':len(manifest['inherited_inputs']),
            'reviewed_new_files':len(review['source_files']),'complete_new_read_lines':count,
            'local_links_checked':links,'manifest_sha256':digest(folder/'SOURCE_HASHES.json'),
            'separately_read_local_attribution_lines':supporting_lines,
            'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))


if __name__=='__main__':
    main()
