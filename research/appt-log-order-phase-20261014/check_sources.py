#!/usr/bin/env python3
"""Literal manuscript/review/input/link correspondence; no Lean execution."""
from argparse import ArgumentParser
from pathlib import Path, PurePosixPath
import hashlib
import json
import re


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=ArgumentParser(); ap.add_argument('--root',type=Path); ap.add_argument('--out',type=Path)
    args=ap.parse_args()
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
    for item in review['source_files']+review['inherited_inputs_actual_read']:
        rel=str(PurePosixPath(item['path']).relative_to(original_root))
        if not (root/rel).is_file() or digest(root/rel)!=item['sha256_literal']:
            bad.append('review/'+rel)
    # The final clarification must be precisely the two-line author delta.
    current=(folder/'LOG_POWER_ENVELOPE.md').read_text(encoding='utf-8')
    newer='For D≥18, (15/16)(D−1)<D−2. For D=17, the first strict bound in L8 gives\nG_J<15=D−2 directly. The remaining cases D=15,16 have, respectively,\n'
    older='For D≥18, (15/16)(D−1)<D−2. The two smaller cases not covered by that step\nare D=15,16; their G_J<D−2 statements are, respectively,\n'
    if current.count(newer)!=1:
        bad.append('review delta location')
    else:
        reconstructed=current.replace(newer,older,1).encode('utf-8')
        if hashlib.sha256(reconstructed).hexdigest()!=review['complete_read_plus_final_delta']['initial_LOG_POWER_ENVELOPE_sha256']:
            bad.append('review initial byte reconstruction')
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
    record={'status':'PASS','kind':'literal bytes and read-scope correspondence, not a mathematical proof',
            'packet_files':len(manifest['files']),'inherited_input_files':len(manifest['inherited_inputs']),
            'reviewed_new_files':len(review['source_files']),
            'initial_full_read_lines':review['new_manuscript_total_lines_read'],
            'final_two_line_delta_reconstructed':True,'local_links_checked':links,
            'manifest_sha256':digest(folder/'SOURCE_HASHES.json'),
            'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))


if __name__=='__main__':
    main()
