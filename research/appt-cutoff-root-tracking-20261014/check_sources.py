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
    review=json.loads((folder/'MANUSCRIPT_REVIEW.json').read_text(encoding='utf-8'))
    original_root=PurePosixPath(review['source_tree'])
    count=0
    for item in review['source_files']+review['inherited_inputs_actual_reading']:
        rel=str(PurePosixPath(item['path']).relative_to(original_root))
        p=root/rel
        expected=item.get('final_sha256_literal',item.get('sha256_literal'))
        if not p.is_file() or digest(p)!=expected:
            bad.append('review/'+rel)
        if item in review['source_files']:
            line_count=len(p.read_bytes().splitlines())
            ranges=item.get('fresh_read_ranges_inclusive',item.get('actual_full_initial_read_ranges_inclusive'))
            if line_count!=item['line_count'] or ranges!=[[1,line_count]]:
                bad.append('complete-read/'+rel)
            count+=line_count
    if count!=review['complete_initial_new_line_count'] or count!=304:
        bad.append('complete new read count')
    # The actual complete304-line base reading was followed by four
    # precisely delimited final clarification reads, not a new full pass.
    paper=folder/'PAPER.md'
    delta={
        137:('Uniformly on I_D, finite-count factors equal1+O_(ell,C)(logD/D), and',
             'Uniformly on I_D, finite-count factors equal1+O_ell(logD/D), and'),
        139:('    P_D=(3^alpha/D)[1+O_(ell,C,S)(logD/D+D/3^alpha)].',
             '    P_D=(3^alpha/D)[1+O_(ell,S)(logD/D+D/3^alpha)].'),
        141:('Any fixed r in(0,1) has r^alpha=O_(ell,S,r)(D^(kappa logr)L^(-kappa logr))',
             'Any fixed r in(0,1) has r^alpha=O_(ell,S)(D^(kappa logr)L^(-kappa logr))'),
        176:("The first fraction is at most1, since theta*<=1. The displayed (logP_D)'",
             'The first fraction is at most1, since theta*<=1. The second derivative')
    }
    base_lines=paper.read_bytes().splitlines(keepends=True)
    for number,(final,initial) in delta.items():
        line=base_lines[number-1]
        if line.rstrip(b'\r\n')!=final.encode('utf-8'):
            bad.append('final clarification line/'+str(number))
        ending=line[len(line.rstrip(b'\r\n')):]
        base_lines[number-1]=initial.encode('utf-8')+ending
    base_sha=hashlib.sha256(b''.join(base_lines)).hexdigest()
    if base_sha!='80360fb7bb7d74e51c04d3b8a71d949d70f0e97a7ca6a0113a0a7a58c340fa42':
        bad.append('initial complete read reconstruction')
    paper_read=review['source_files'][0]
    if paper_read['initial_full_read_sha256_literal']!=base_sha or not paper_read['all_final_bytes_covered_by_initial_plus_exact_delta']:
        bad.append('initial-plus-delta reading basis')
    declared=review['final_delta']
    if declared['lines']!=sorted(delta) or declared['modified_line_count']!=4:
        bad.append('declared final delta scope')
    contexts=paper_read['actual_final_delta_context_read_ranges_inclusive']
    for item in declared['changes']:
        n=item['line']
        if n not in delta or (item['final'],item['initial'])!=delta[n] or not any(lo<=n<=hi for lo,hi in contexts):
            bad.append('declared final delta/'+str(n))
    links=0
    for name in manifest['files']:
        if name.endswith('.md'):
            p=folder/name
            for target in prose_links(p.read_text(encoding='utf-8')):
                if target.startswith(('https:','http:','mailto:','#')):
                    continue
                destination=p.parent/target.split('#',1)[0]
                planned_output=args.out is not None and destination.resolve()==args.out.resolve()
                if not destination.is_file() and not planned_output:
                    bad.append('link/'+name+' -> '+target)
                links+=1
    if bad:
        raise RuntimeError('Source correspondence failure: '+', '.join(bad))
    record={'status':'PASS','kind':'literal bytes, declared read scope and links; not a mathematical proof',
            'packet_files':len(manifest['files']),'inherited_input_files':len(manifest['inherited_inputs']),
            'reviewed_new_files':len(review['source_files']),'complete_final_coverage_lines':count,
            'local_links_checked':links,'manifest_sha256':digest(folder/'SOURCE_HASHES.json'),
            'base_complete_new_read_lines':304,'final_clarification_lines_read':sorted(delta),
            'reconstructed_base_paper_sha256':base_sha,
            'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))


if __name__=='__main__':
    main()
