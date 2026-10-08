#!/usr/bin/env python3
"""Negative controls: optimized launcher must reject a false proof obligation."""
from fractions import Fraction
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[2]
LAUNCHER=Path(__file__).with_name('strict_checker.py')


def reject(path):
    for flags in ([],['-O']):
        p=subprocess.run([sys.executable,'-I',*flags,'-B',str(LAUNCHER),str(path)],
                         capture_output=True,text=True)
        if p.returncode==0 or 'AssertionError' not in p.stderr:
            raise RuntimeError('False obligation was not rejected: '+str(path))


def main():
    with tempfile.TemporaryDirectory(prefix='math-replay-negative-') as temp:
        work=Path(temp)
        fixture=work/'false_obligation.py'
        fixture.write_text('assert False, "required negative control"\n')
        reject(fixture)
        helper=work/'false_helper.py'
        helper.write_text('assert False, "imported proof obligation"\n')
        fixture.write_text('import false_helper\n')
        reject(fixture)
        code=work/'code';code.mkdir()
        certs=work/'certificates';certs.mkdir()
        checker=code/'check_three_subset_certificates.py'
        shutil.copyfile(ROOT/'notes/sharp-robust-permanent/code'/checker.name,checker)
        source=ROOT/'notes/sharp-robust-permanent/certificates/three_subset_n6_23.json'
        data=json.loads(source.read_text())
        cert=data['degrees'][0]
        cert['optimal_coefficient']=str(Fraction(cert['optimal_coefficient'])+1)
        (certs/source.name).write_text(json.dumps(data))
        reject(checker)
    print('PASS: entrypoint/imported false assertions and corrupted three-subset objective rejected')
    print('PASS: both normal and optimized launchers retain proof obligations')


if __name__=='__main__':
    main()
