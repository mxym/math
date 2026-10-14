#!/usr/bin/env python3
"""Literal source and honest read-scope correspondence; no mathematical audit."""
from argparse import ArgumentParser
from pathlib import Path, PurePosixPath
import hashlib
import json
import re


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def require(v,msg):
    if not v: raise RuntimeError(msg)


def ranges_valid(ranges,n):
    return bool(ranges) and all(len(r)==2 and 1<=r[0]<=r[1]<=n for r in ranges) and all(
        ranges[i-1][1]<ranges[i][0] for i in range(1,len(ranges)))


def prose_links(s):
    lines=[]; fenced=False
    for line in s.splitlines():
        if line.lstrip().startswith(('```','~~~')): fenced=not fenced
        elif not fenced and not line.startswith(('    ','\t')): lines.append(line)
    return re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)','\n'.join(lines))


def main():
    parser=ArgumentParser(); parser.add_argument('--root',type=Path); parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    folder=Path(__file__).resolve().parent; root=args.root or folder.parents[1]
    manifest=json.loads((folder/'SOURCE_HASHES.json').read_text(encoding='utf-8'))
    for rel,h in manifest['files'].items():
        require((folder/rel).is_file() and sha(folder/rel)==h,'Packet literal mismatch '+rel)
    for rel,h in manifest['inherited_inputs'].items():
        require((root/rel).is_file() and sha(root/rel)==h,'Inherited literal mismatch '+rel)
    review=json.loads((folder/'REVIEW.json').read_text(encoding='utf-8'))
    original_root=PurePosixPath(review['source_tree'])
    count=support=0
    for item in review['source_files']+review['inherited_inputs_actual_reading']+review['fresh_supporting_source_reading']:
        if 'path' not in item: continue
        rel=str(PurePosixPath(item['path']).relative_to(original_root)); p=root/rel
        require(p.is_file() and sha(p)==item['sha256_literal'],'Reviewed literal mismatch '+rel)
        n=len(p.read_bytes().splitlines()); ranges=item['actual_read_ranges_inclusive']
        require(n==item['physical_line_count'] and ranges_valid(ranges,n),'Reading range mismatch '+rel)
        if item in review['source_files']:
            require(item['complete_ordinary_read'] and ranges==[[1,n]],'Incomplete new source '+rel)
            count+=n
        elif item in review['fresh_supporting_source_reading']:
            support+=sum(b-a+1 for a,b in ranges)
        elif item.get('complete_ordinary_read'):
            require(ranges==[[1,n]],'Overstated inherited full read '+rel)
    delta=review['final_delta']
    require(count==review['complete_initial_new_line_count']==405,'Initial math read count')
    require(delta['complete_final_delta_read'] and len(delta['changes'])==2, 'Final corrections read missing')
    require(delta['actual_final_delta_read_ranges_inclusive']==[[125,125],[158,158]],'Final changed-line ranges')
    payload=(folder/'PAPER.md').read_bytes(); lines=payload.splitlines(keepends=True)
    require(len(lines)==387,'Unexpected final line count')
    old=payload
    for change in reversed(delta['changes']):
        line=change['changed_line']
        require(line in (125,158) and lines[line-1].rstrip(b'\r\n')==change['after'].encode(),'Unexpected final correction')
        require(change['complete_final_delta_read'] and change['actual_final_delta_read_ranges_inclusive']==[[line,line]],'Final correction not actually read')
        require(old.count(change['after'].encode())==1,'Ambiguous correction reconstruction')
        old=old.replace(change['after'].encode(),change['before'].encode())
    require(hashlib.sha256(old).hexdigest()==delta['initial_sha256_literal'],'Other mathematical bytes changed')
    require(hashlib.sha256(payload).hexdigest()==delta['final_sha256_literal'],'Final math SHA differs')
    declared=json.loads((folder/'AUTHOR_RANGE_DELTA.json').read_text(encoding='utf-8'))
    formatting=json.loads((folder/'AUTHOR_FORMAT_DELTA.json').read_text(encoding='utf-8'))
    require(declared['initial_sha256']==delta['initial_sha256_literal'] and declared['final_sha256']==delta['intermediate_after_range_sha256_literal'], 'Range-correction binding differs')
    require(formatting['before_format_sha256']==declared['final_sha256'] and formatting['final_sha256']==delta['final_sha256_literal'], 'Format-correction binding differs')
    require(support==review['fresh_supporting_line_counts_excluded_from_new_mathematics']['total']==318,'Supporting read count')
    require(not review['findings']['blocking_mathematical_gaps'],'Unresolved mathematical reviewer blocker')
    require(not review['diagnostic_script_support']['author_reports_read'],'Author reports falsely treated as reviewer-read')
    reports=[json.loads((folder/n).read_text(encoding='utf-8')) for n in
             ('DIAGNOSTIC.windows.json','DIAGNOSTIC.windows-O.json','DIAGNOSTIC.wsl.json')]
    require(reports[0]==reports[1]==reports[2],'Finite diagnostic execution modes disagree')
    require(reports[0]['script_sha256']==sha(folder/'check_all.py'),'Diagnostic script correspondence differs')
    links=0
    for rel in manifest['files']:
        if not rel.endswith('.md'): continue
        p=folder/rel
        for target in prose_links(p.read_text(encoding='utf-8')):
            if target.startswith(('http:','https:','mailto:','#')): continue
            dest=p.parent/target.split('#',1)[0]
            require(dest.is_file() or (args.out is not None and dest.resolve()==args.out.resolve()),'Local link missing '+target)
            links+=1
    record={'status':'PASS','kind':'Literal source, initial read plus actual final delta, inherited ranges and links; not an infinite theorem proof',
            'packet_files':len(manifest['files']),'inherited_input_files':len(manifest['inherited_inputs']),
            'complete_initial_new_math_read_lines':count,'final_changed_lines_read':2,
            'mathematical_input_range_changed_lines':1,'formatting_only_changed_lines':1,
            'second_complete_final_reread_claimed':False,'unchanged_math_lines_byte_bound':True,
            'separately_read_local_supporting_lines':support,'local_links_checked':links,
            'manifest_sha256':sha(folder/'SOURCE_HASHES.json'),
            'diagnostic_implementations':1,'new_Lean_execution':False,'new_audit_roots':0}
    if args.out: args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))


if __name__=='__main__': main()
