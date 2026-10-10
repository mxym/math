#!/usr/bin/env python3
"""Replay the paper's exact certificates without Lean, optimization, or floating point.
This checker supplements, rather than replaces, the immutable Lean proof.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import argparse, hashlib, json, tempfile, time
from certificate_polynomials import certificate_context
ROOT=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    hashes=json.loads((ROOT/'CERTIFICATE_HASHES.json').read_text())
    for name,h in hashes.items():
        actual=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
        if actual!=h:raise RuntimeError('Certificate source hash mismatch: '+name)
    checks=[]
    for dimension,uniform in [(9,False),(12,False),(15,False),(18,False),(21,False),(24,False),(9,True)]:
        start=time.monotonic()
        c=certificate_context(ROOT,ROOT,dimension,uniform,40)
        item={'case':'Uniform' if uniform else 'D'+str(dimension),'passed':True,
              'terms':len(c['terms']),'target_monomials':len(c['target']),
              'seconds':round(time.monotonic()-start,4)}
        checks.append(item);print(json.dumps(item),flush=True)
    # A valid D24 certificate was just accepted. Alter one nonzero weighted term.
    original=json.loads((ROOT/'qutrit_D24_fast_certificate.json').read_text())
    original['terms'][0]['coefficient']=str(Fraction(original['terms'][0]['coefficient'])+1)
    with tempfile.TemporaryDirectory(prefix='appt-preprint-negative-') as temporary:
        d=Path(temporary)
        (d/'qutrit_D24_fast_certificate.json').write_text(json.dumps(original))
        try:certificate_context(ROOT,d,24,False,40)
        except ValueError as exc:
            if str(exc)!='EXACT IDENTITY FAILURE':raise
        else:raise RuntimeError('Altered certificate incorrectly accepted')
    checks.append({'case':'corrupted-D24-coefficient','passed':True,'expected_rejection':True})
    # Exact finite phase-average coefficient check for all qutrit Schmidt ranks.
    for rank in (1,2,3):
        for i,j,k,l in product(range(rank),repeat=4):
            exponent=[0]*rank
            for t,sign in [(i,1),(j,-1),(k,-1),(l,1)]:exponent[t]+=sign
            average=int(all(t%3==0 for t in exponent))
            expected=int(i==j and k==l)+int(i==k and j==l and i!=j)
            if average!=expected:raise RuntimeError('Phase-average identity failure')
    checks.append({'case':'qutrit-phase-average','passed':True,'ranks':[1,2,3]})
    report={'status':'PASS','scope':'Seven exact certificate identities, an altered-coefficient rejection, and the phase-average coefficient identity; not a new Lean run',
            'certificate_hashes':hashes,'checks':checks}
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print('PREPRINT_EXACT_CHECKS_PASS',flush=True)
if __name__=='__main__':main()
