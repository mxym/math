#!/usr/bin/env python3
"""Run the real checker, then reject deliberately altered copies of its source.
The positive and negative controls work with Python assertion checks disabled.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
MUTATIONS=[
    ('wrong Fourier conjugation', 'self.phase(-i)', 'self.phase(i)', 'idempotent Bell projector'),
    ('wrong partial-transpose square factor', 'F.scale(Q(1,a*a),F.one)', 'F.scale(Q(1,a),F.one)', 'Bell partial-transpose square identity'),
    ('altered Bernstein cross coefficient', '(1,1):Q(20,3)', '(1,1):Q(19,3)', 'Bernstein exponent certificate'),
    ('wrong multinomial numerator', 'value=factorial(sum(counts))', 'value=factorial(sum(counts)+1)', 'exact type size bounds'),
    ('wrong collision-entropy coefficient', 'H2=padd(pscale(-2,ell),z)', 'H2=padd(pscale(-3,ell),z)', 'collision endpoint matching'),
]

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path)
    args=ap.parse_args();source=(ROOT/'check.py').read_text();records=[]
    for flag in ([],['-O']):
        result=subprocess.run([sys.executable,*flag,str(ROOT/'check.py')],capture_output=True,text=True,timeout=60)
        if result.returncode!=0:raise RuntimeError('Positive checker failed: '+result.stderr)
        parsed=json.loads(result.stdout)
        if parsed['status']!='PASS':raise RuntimeError('Positive checker did not pass')
        records.append({'name':'positive checker '+('optimized' if flag else 'normal'),'exit_code':0,'passed':True,'stdout_sha256':hashlib.sha256(result.stdout.encode()).hexdigest()})
    with tempfile.TemporaryDirectory(prefix='collective-negativity-mutations-') as temporary:
        path=Path(temporary)/'check.py'
        for label,before,after,reason in MUTATIONS:
            if source.count(before)!=1:raise RuntimeError('Mutation is not unique: '+label)
            path.write_text(source.replace(before,after))
            result=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=60)
            wanted='CheckFailed: '+reason
            good=result.returncode==1 and wanted in result.stderr
            records.append({'name':label,'exit_code':result.returncode,'passed':good,'expected_failure':wanted,'stdout':result.stdout,'stderr':result.stderr})
            if not good:raise RuntimeError('Mutation was not correctly rejected: '+label+'\n'+result.stderr)
    report={'status':'PASS','scope':'Tests of exact ancillary checker source; not proof validation of the full analytic theorem','checks':records,'checker_sha256':hashlib.sha256(source.encode()).hexdigest()}
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
