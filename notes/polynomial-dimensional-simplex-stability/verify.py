#!/usr/bin/env python3
"""Replay unchanged finite checks safely with assertions enabled in isolated subprocesses."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
SCRIPTS=['check_weighted_anchors.py','check_constants.py','check_independent_refinement_audit.py']


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--extracted', action='store_true')
    args=parser.parse_args()
    # The package checker uses a local helper and explicit exceptions, never assert.
    command=[sys.executable,'-E',str(ROOT/'check_package.py')]+(['--extracted'] if args.extracted else [])
    subprocess.run(command, check=True)
    subprocess.run([sys.executable,'-I','-c','import sys; sys.exit(0 if __debug__ and sys.flags.optimize == 0 else 1)'],check=True)
    results=[]
    with tempfile.TemporaryDirectory(prefix='polynomial-stability-replay-') as temp:
        tmp=Path(temp)
        for name in SCRIPTS:
            shutil.copyfile(ROOT/name,tmp/name)
            # No -O flag is inherited; -I ignores PYTHONOPTIMIZE and isolates imports.
            process=subprocess.run([sys.executable,'-I',str(tmp/name)],cwd=tmp,check=True,text=True,capture_output=True)
            log=process.stdout
            expected=ROOT/'verification'/name.replace('.py','.log')
            if expected.exists() and log!=expected.read_text():
                raise RuntimeError('Recorded output differs for '+name)
            row={'script':name,'status':'PASS','assertions':'enabled in isolated unoptimized child','stdout_sha256':hashlib.sha256(log.encode()).hexdigest()}
            if name=='check_constants.py':
                actual=json.loads((tmp/'constant_checks.json').read_text())
                recorded=json.loads((ROOT/'verification/constant_checks.json').read_text())
                if actual!=recorded: raise RuntimeError('Floating constant output differs; review platform rounding before accepting.')
                row['constant_cases']=actual['cases']
            results.append(row)
            print(log,end='')
    report={'schema':'polynomial-stability-regression-replay-v1','status':'PASS','checks':results,'scope':'Exact rational finite laws/witnesses and facets; floating log constant/gate diagnostics. Analytic proofs establish universal claims.'}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results/verification.json').write_text(json.dumps(report,indent=2)+'\n')
    subprocess.run(command,check=True)
    print('PASS: all three unchanged regressions; frozen source bytes remained intact.')

if __name__=='__main__': main()
