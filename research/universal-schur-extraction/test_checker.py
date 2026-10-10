#!/usr/bin/env python3
"""Positive and actual corrupted-program tests; not analytic-proof certification."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
MUTATIONS=[
 ('hook denominator shift','factorial(lam[i]+D-1-i)','factorial(lam[i]+D-i)','integral Weyl and hook dimensions'),
 ('incorrect Schur character index','at(lam[i]-i+j)','at(lam[i]+i-j)','independent Weyl character dimension'),
 ('missing universal-state normalization','F(1,2*up),plus','F(1,up),plus','normalized universal state'),
 ('truncate the unknown representation factor','selected={i*v+j for i in range(u) for j in range(vp)}','selected={i*v+j for i in range(min(u,vp)) for j in range(v)}','multiplicity-factor retained mass'),
 ('cut off the multiplicity factor by one','vp=min(v,N0//u);rp=u*vp','vp=min(v,max(0,N0//u-1));rp=u*vp','complete extraction of every good block'),
 ('omit leftover Kraus coordinates','out[i]=(size+i,0)','pass','all leftover Kraus branches present'),
 ('keep false cross-code coherences','if ki==kj and li==lj:','if ki==kj:','all coherent code dyads extracted correctly'),
 ('wrong target overlap power','F(d,K),\'squared target overlap convention\'','F(d*d,K*K),\'squared target overlap convention\'','squared target overlap convention'),
 ('wrong escort sign','poly_scale(-1,z))\n    require(poly_mul(a,D)==right','z)\n    require(poly_mul(a,D)==right','escort relative-entropy identity'),
]

def run(command, label, expected=None):
    p=subprocess.run(command,capture_output=True,text=True,timeout=40)
    if expected is None:
        try: data=json.loads(p.stdout)
        except json.JSONDecodeError: data={}
        good=p.returncode==0 and data.get('status')=='PASS'
    else:
        good=p.returncode==1 and ('CheckFailed: '+expected) in p.stderr
    if not good:
        raise RuntimeError('Control did not meet its required diagnostic: '+label+'\n'+p.stdout[-1500:]+'\n'+p.stderr[-3000:])
    return {'name':label,'exit_code':p.returncode,'passed':good,'expected_diagnostic':expected,
            'stdout':p.stdout,'stderr':p.stderr}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    source=(ROOT/'check.py').read_text();records=[]
    records.append(run([sys.executable,str(ROOT/'check.py')],'unchanged checker'))
    records.append(run([sys.executable,'-O',str(ROOT/'check.py')],'unchanged checker with assertions disabled'))
    with tempfile.TemporaryDirectory(prefix='schur-extraction-mutants-') as temp:
        p=Path(temp)/'check.py'
        for label,old,new,diagnostic in MUTATIONS:
            if source.count(old)!=1:raise RuntimeError('Mutation anchor is not unique: '+label)
            p.write_text(source.replace(old,new))
            records.append(run([sys.executable,'-O',str(p)],label,diagnostic))
    report={'status':'PASS','scope':'Exact checker corruption controls, not a Lean or analytic-proof certificate',
            'checker_sha256':hashlib.sha256((ROOT/'check.py').read_bytes()).hexdigest(),'checks':records}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
