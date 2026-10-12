#!/usr/bin/env python3
"""Offline, read-only replay of the focused 002v4 checker repair."""
import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

BASE=Path(__file__).resolve().parent
ENTRY='preprints/002-quadratic-order-moats/v4'

def need(ok,message):
    if not ok:raise RuntimeError(message)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def run(command,repo):
    p=subprocess.run(command,cwd=repo,capture_output=True)
    need(p.returncode==0,'replay failed: '+p.stderr.decode())
    return p.stdout

def paired(script,arguments,repo):
    normal=run(['python3','-B',str(script),*arguments],repo)
    optimized=run(['python3','-O','-B',str(script),*arguments],repo)
    need(normal==optimized,'normal/optimized output mismatch: '+script.name)
    return normal

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=BASE.parents[1])
    p.add_argument('--output',type=Path)
    args=p.parse_args();repo=args.repo.resolve()
    pins=json.loads((BASE/'SOURCE_PINS.json').read_text())
    for path,want in pins['current_source_sha256'].items():need(sha(repo/path)==want,'current source pin mismatch: '+path)
    for path,want in pins['original_checker_sha256'].items():need(sha(BASE/'original-checkers'/path)==want,'original checker mismatch: '+path)
    delivery=json.loads((BASE/'PACKAGE_MANIFEST.json').read_text())
    for row in delivery['files']:
        file=BASE/row['path'];need(file.is_file() and not file.is_symlink(),'missing regular evidence file: '+row['path'])
        need(file.stat().st_size==row['bytes'] and sha(file)==row['sha256'],'evidence payload mismatch: '+row['path'])
    manifest_entries=0
    for entry in (ENTRY,'preprints/006-modulus-nonlinear-similarity/v2'):
        m=json.loads((repo/entry/'MANIFEST.json').read_text())
        for path,want in m['files'].items():
            b=(repo/entry/path).read_bytes()
            got=hashlib.sha256(b).hexdigest() if isinstance(want,str) else hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            need(got==(want if isinstance(want,str) else want['git_blob_sha']),'manuscript manifest mismatch: '+path);manifest_entries+=1
        for path,want in m.get('inherited_v3_dependencies',{}).items():need(sha(repo/path)==want,'inherited dependency mismatch: '+path);manifest_entries+=1
    need(manifest_entries==26,'unexpected manifest entry count')
    expected={
        'check_period_optimality.py':'01d68934cc21a6e266575ed984013fd80ecb33431d041bd570bcb7593130c42b',
        'check_endpoint_rigidity.py':'2eea7de6e765287d16beea5337a7cf0c328923263c706b42f1ad0faf030b4d45',
        'check_sqrt2_period.py':'dc37fcd45e38fcb4d32891b4a6b72fb13a784a4cc73c00ef62af4c5f2dca12bd'}
    for name,want in expected.items():
        answer=paired(repo/ENTRY/'code'/name,[],repo)
        need(hashlib.sha256(answer).hexdigest()==want,'valid replay output changed: '+name)
    controls=paired(BASE/'adversarial_controls.py',[str(repo),'--original-tree',str(BASE/'original-checkers')],repo)
    need(controls==(BASE/'evidence/controls.normal.json').read_bytes(),'corruption evidence mismatch')
    independent=paired(BASE/'independent_replay.py',[str(repo)],repo)
    need(independent==(BASE/'evidence/independent.normal.json').read_bytes(),'independent graph/rational evidence mismatch')
    for path,want in pins['current_source_sha256'].items():need(sha(repo/path)==want,'read-only source changed: '+path)
    for row in delivery['files']:need(sha(BASE/row['path'])==row['sha256'],'read-only evidence changed: '+row['path'])
    result={'status':'PASS','source_pins':len(pins['current_source_sha256']),'original_checker_pins':len(pins['original_checker_sha256']),'manifest_entries':manifest_entries,'corruption_controls':19,'all_fixed_controls_rejected':True,'normal_optimized_byte_identical':True,'valid_replay_outputs_unchanged':True,'independent_negative_graphs':271,'independent_failure_steps':28489,'independent_positive_graphs':3,'mathematical_claims_and_scope_unchanged':True}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
