#!/usr/bin/env python3
"""Source-isolated reproduction; exact checks are not a general formal proof."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot():
    expected=json.loads((ROOT/'SHA256SUMS.json').read_text())
    for name,digest in expected.items():
        if sha(ROOT/name)!=digest:raise RuntimeError('Source hash mismatch: '+name)
    return expected

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',required=True,type=Path)
    p.add_argument('--numerical',action='store_true')
    args=p.parse_args();out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=False)
    report={'status':'RUNNING','started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
            'python':sys.version,'scope':'Exact finite certificates and optional synthetic numerics; not Lean or field validation'}
    try:
        before=snapshot();report['source_sha256']=before
        work=out/'fresh';work.mkdir()
        for name in before:
            target=work/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,target)
        commands=[];report['commands']=commands
        def run(arguments,log):
            with (out/log).open('w') as stream:
                r=subprocess.run([sys.executable]+arguments,cwd=work,stdout=stream,stderr=subprocess.STDOUT,timeout=600)
            commands.append({'arguments':arguments,'returncode':r.returncode,'log':log})
            if r.returncode:raise RuntimeError('Failed: '+log)
        for module in ['exact.py','independent.py']:
            run([module],module+'.json');run(['-O',module],module+'.optimized.json')
            if (out/(module+'.json')).read_bytes()!=(out/(module+'.optimized.json')).read_bytes():
                raise RuntimeError('Python optimization changed checks')
        a=json.loads((out/'exact.py.json').read_text());b=json.loads((out/'independent.py.json').read_text())
        if a['status']!='PASS' or b['status']!='PASS' or len(a['negative_controls_rejected'])!=7:
            raise RuntimeError('Missing successful checks')
        for key in ['controllability_determinant','observability_determinant']:
            if a[key]!=b[key]:raise RuntimeError('Independent certificate disagreement')
        report['exact']=a;report['independent']=b;report['optimized_outputs_identical']=True
        if args.numerical:
            for module in ['simulate.py','design.py','finite_time.py']:
                run([module,'--output-dir',str(out/'numerical')],module+'.log')
            report['numerical']={name:json.loads((out/'numerical'/name).read_text())
                                 for name in ['synthetic.json','design.json','finite_time.json']}
        if before!=snapshot():raise RuntimeError('Sources changed during verification')
        report['status']='PASS';report['source_hashes_unchanged']=True
        report['result_sha256']={str(x.relative_to(out)):sha(x) for x in sorted(out.rglob('*'))
                                 if x.is_file() and not x.is_relative_to(work)}
    except Exception as error:
        report['status']='FAIL';report['error']=str(error)
    report['finished_utc']=dt.datetime.now(dt.timezone.utc).isoformat()
    (out/'verification.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:report[k] for k in ['status','scope','started_utc','finished_utc']},indent=2))
    if report['status']!='PASS': print(report.get('error',''));return 1
    return 0
if __name__=='__main__':raise SystemExit(main())
