#!/usr/bin/env python3
"""Replay all finite checks without mutating the proof or archived evidence."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
SCRIPTS=['check_weighted_anchors.py','check_constants.py','check_independent_refinement_audit.py','check_quadratic_constants.py','check_independent_quadratic_audit.py']


def need(ok,message):
    if not ok: raise RuntimeError(message)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--extracted',action='store_true')
    args=parser.parse_args()
    command=[sys.executable,'-E',str(ROOT/'check_package.py')]+(['--extracted'] if args.extracted else [])
    subprocess.run(command,check=True)
    subprocess.run([sys.executable,'-I','-c','import sys; sys.exit(0 if __debug__ and sys.flags.optimize == 0 else 1)'],check=True)
    results=[]
    with tempfile.TemporaryDirectory(prefix='quadratic-stability-replay-') as temp:
        tmp=Path(temp)
        manifest=json.loads((ROOT/'MANIFEST.json').read_text())
        for row in manifest['files']:
            destination=tmp/row['path'];destination.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/row['path'],destination)
        for name in SCRIPTS:
            # -I ignores PYTHONOPTIMIZE; no -O is passed to the child.
            process=subprocess.run([sys.executable,'-I',str(tmp/name)],cwd=tmp,check=True,text=True,capture_output=True)
            log=process.stdout
            expected=ROOT/'verification'/name.replace('.py','.log')
            if expected.exists():need(log==expected.read_text(),'Recorded stdout differs: '+name)
            if name=='check_constants.py':
                need(json.loads((tmp/'constant_checks.json').read_text())==json.loads((ROOT/'verification/constant_checks.json').read_text()),'Prior floating constant evidence differs; review platform rounding.')
            if name=='check_quadratic_constants.py':
                need(json.loads(log)==json.loads((ROOT/'verification/quadratic_constant_checks.json').read_text()),'Quadratic floating constant evidence differs; review platform rounding.')
            if name=='check_independent_quadratic_audit.py':
                need(json.loads((tmp/'independent_exact_checks.json').read_text())==json.loads((ROOT/'verification/independent_exact_checks.json').read_text()),'Exact quadratic evidence differs.')
            results.append(dict(script=name,status='PASS',assertions='enabled in isolated unoptimized child',stdout_sha256=hashlib.sha256(log.encode()).hexdigest()))
            print('PASS: '+name,flush=True)
    report=dict(schema='quadratic-stability-replay-v1',status='PASS',checks=results,scope='Finite arithmetic/normalization checks supplement the written analytic proof; they do not establish the universal theorem.')
    output=ROOT/'results'
    need(not output.is_symlink(),'Results directory must not be a symlink')
    output.mkdir(exist_ok=True)
    destination=output/'verification.json'
    need(not destination.is_symlink(),'Results output must not be a symlink')
    destination.write_text(json.dumps(report,indent=2)+'\n')
    subprocess.run(command,check=True)
    print('PASS: all five regressions; source and recorded evidence bytes unchanged.')

if __name__=='__main__':main()
