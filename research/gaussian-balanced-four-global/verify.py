#!/usr/bin/env python3
"""Package integrity and exact/partial-formal provenance, not Gaussian proof checking."""
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE=Path(__file__).resolve().parent


def need(ok,message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    manifest=json.loads((HERE/'MANIFEST.json').read_text())
    expected=manifest['files']
    actual={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file()
            and p.name not in {'MANIFEST.json','SHA256SUMS'}
            and '__pycache__' not in p.parts and '.lake' not in p.parts}
    need(actual==set(expected),'Bound file set changed')
    for name,hash_ in expected.items():
        path=HERE/name
        need(not path.is_symlink() and digest(path)==hash_,'Hash mismatch: '+name)
    sums=''.join(hash_+'  '+name+'\n' for name,hash_ in sorted(expected.items()))
    need((HERE/'SHA256SUMS').read_text()==sums,'Checksum list changed')
    env=os.environ.copy()
    normal=subprocess.run([sys.executable,str(HERE/'check_exact.py')],capture_output=True,check=True,env=env).stdout
    optimized=subprocess.run([sys.executable,'-O',str(HERE/'check_exact.py')],capture_output=True,check=True,env=env).stdout
    need(normal==optimized==(HERE/'results/exact.json').read_bytes(),'Exact diagnostics not replayed identically')
    exact=json.loads(normal)
    need(exact['status']=='PASS' and exact['analytic_endpoint_checked'] is False,'Diagnostic scope changed')
    lean=json.loads((HERE/'results/lean.json').read_text())
    need(lean['status']=='PASS' and lean['positive_theorems']==8
         and lean['empty_kernel_declarations']==7286
         and lean['negative_controls_rejected']==1
         and lean['analytic_endpoint_formalized'] is False,'Partial Lean scope changed')
    need(set(lean['allowed_axioms'])=={'propext','Classical.choice','Quot.sound'},'Lean axioms changed')
    for name,hash_ in lean['sources'].items():
        need(digest(HERE/'formal'/name)==hash_,'Lean source changed: '+name)
    for name,hash_ in lean['logs'].items():
        need(digest(HERE/'results'/name)==hash_,'Lean log changed: '+name)
    positive=(HERE/'results/Algebra.log').read_text()
    need(len(re.findall(r"'BalancedFourGlobal\.[^']+' depends on axioms:",positive))==8,'Axiom export count')
    need('EMPTY_KERNEL_REPLAY_PASS 7286 declarations; 8 roots; trust level zero'
         in (HERE/'results/Replay.log').read_text(),'Replay marker missing')
    need('linarith failed to find a contradiction' in (HERE/'results/FalseBound.log').read_text(),
         'False control failure missing')
    hpaper=digest(HERE/'paper.md')
    for name in ['ANALYSIS_FINAL.md','COMBINATORICS_FINAL.md']:
        need(hpaper in (HERE/'review'/name).read_text(),'Final review hash missing: '+name)
    info=subprocess.run(['pdfinfo',str(HERE/'paper.pdf')],capture_output=True,check=True).stdout.decode()
    match=re.search(r'^Pages:\s+(\d+)$',info,re.M)
    need(match and int(match[1])==11,'Unexpected PDF page count')
    extracted=subprocess.run(['pdftotext','-layout',str(HERE/'paper.pdf'),'-'],capture_output=True,check=True).stdout
    need(extracted==(HERE/'results/paper.txt').read_bytes(),'PDF extracted text differs')
    print(json.dumps({'status':'PASS','bound_files':len(expected),'pdf_pages':11,
          'matrix_cases':exact['matrix_cases'],'local_identity_cases':exact['local_identity_cases'],
          'normal_optimized_exact_equal':True,'partial_lean_roots':8,'empty_kernel_declarations':7286,
          'scope':'package integrity, finite exact diagnostics, and recorded partial Lean provenance',
          'analytic_endpoint_machine_checked':False},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
