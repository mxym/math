#!/usr/bin/env python3
"""Independent exact-arithmetic positive and mutated-certificate controls."""
import json,tempfile
from fractions import Fraction
from pathlib import Path
from certificate_polynomials import certificate_context
ROOT=Path(__file__).resolve().parent.parent
source=ROOT/'certificates/qutrit_D24_fast_certificate.json'
positive=certificate_context(ROOT,ROOT/'certificates',24,False,40)
assert positive['polys'][0], 'Mutation must act on a nonzero polynomial'
data=json.loads(source.read_text())
data['terms'][0]['coefficient']=str(Fraction(data['terms'][0]['coefficient'])+1)
with tempfile.TemporaryDirectory(prefix='appt-certificate-negative-') as directory:
    path=Path(directory);(path/source.name).write_text(json.dumps(data))
    try:
        certificate_context(ROOT,path,24,False,40)
    except ValueError as error:
        if str(error)!='EXACT IDENTITY FAILURE':raise
    else:raise RuntimeError('Mutated coefficient was accepted')
print('EXACT_CERTIFICATE_POSITIVE_CONTROL_PASS')
print('EXACT_CERTIFICATE_MUTATION_REJECTED')
