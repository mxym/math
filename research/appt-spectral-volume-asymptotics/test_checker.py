#!/usr/bin/env python3
"""Run the real checker and require deliberate source mutations to fail precisely."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
original = (ROOT/'check.py').read_text()
mutations = [
    ('changed factorial numerator', 'm**(m*m-1)*math.factorial(D-1)',
     'm**(m*m)*math.factorial(D-1)', 'tangent volume factorial identity'),
    ('changed leading coefficient', 'm**(2*m*m-2)*alpha**(2*R+1)',
     'm**(2*m*m-1)*alpha**(2*R+1)', 'qubit leading constant'),
    ('changed density second moment', 'poly_scale(2,one),poly_scale(-1,poly_mul(poly_mul(alpha,beta),poly_mul(L,L)))',
     'poly_scale(3,one),poly_scale(-1,poly_mul(poly_mul(alpha,beta),poly_mul(L,L)))',
     'limiting density exact second moment')]
records=[]
with tempfile.TemporaryDirectory(prefix='appt-volume-checker-tests-') as directory:
    path=Path(directory)/'check.py'
    for optimized in (False, True):
        path.write_text(original)
        command=[sys.executable]+(['-O'] if optimized else [])+[str(path)]
        run=subprocess.run(command,capture_output=True,text=True,timeout=45)
        if run.returncode != 0 or 'EXACT_ANCILLARY_CHECKS_PASS' not in run.stdout:
            raise RuntimeError('Valid checker failed: '+run.stderr)
        records.append({'case':'original optimized' if optimized else 'original',
                        'exit_code':run.returncode,'passed':True,'stdout':run.stdout})
    for name,before,after,diagnostic in mutations:
        if original.count(before) != 1:
            raise RuntimeError('Mutation target is not unique: '+name)
        path.write_text(original.replace(before,after,1))
        run=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=45)
        if run.returncode != 1 or ('ValueError: '+diagnostic) not in run.stderr:
            raise RuntimeError('Invalid checker mutation not correctly rejected: '+name+'\n'+run.stderr)
        records.append({'case':name,'exit_code':run.returncode,'passed':True,
                        'rejection':diagnostic,'stderr':run.stderr})
report={'status':'PASS','scope':'Original checker plus precise rejection of three source mutations; not a proof of the continuum theorem',
        'source_sha256':hashlib.sha256(original.encode()).hexdigest(),'checks':records}
if len(sys.argv)>1:
    Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print('CHECKER_MUTATION_TESTS_PASS',len(records))
