#!/usr/bin/env python3
"""Run the real checker normally, with -O, and after targeted source mutations.
Only the specified mathematical diagnostic counts as successful rejection.
"""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    original=(ROOT/'check.py').read_text();rows=[]
    with tempfile.TemporaryDirectory(prefix='ppt-extraction-mutations-') as temp:
        base=Path(temp);shutil.copy2(ROOT/'bell_checks.py',base/'bell_checks.py')
        script=base/'check.py'
        def check(name,text,negative=None,optimized=False):
            script.write_text(text)
            command=[sys.executable]+(['-O'] if optimized else [])+[str(script)]
            result=subprocess.run(command,text=True,capture_output=True,timeout=40)
            if negative is None:
                try: good=result.returncode==0 and json.loads(result.stdout)['status']=='PASS'
                except (ValueError,KeyError):good=False
            else:
                good=result.returncode==1 and ('CheckFailed: '+negative) in result.stderr
            rows.append({'name':name,'exit_code':result.returncode,'expected_rejection':negative,'passed':good,
                         'stdout':result.stdout if negative else 'Positive JSON report parsed successfully',
                         'stderr':result.stderr})
            if not good:raise RuntimeError('Unexpected checker result: '+name+'\n'+result.stderr)
        check('unaltered checker',original)
        check('unaltered checker with assertions disabled',original,optimized=True)
        changes=[
          ('wrong antisymmetric denominator','K*(K-1)','K*(K+1)','Rains Choi partial-transpose identity'),
          ('omitted input transpose','ii=(i//b)*b+j%b; jj=(j//b)*b+i%b','ii=i; jj=j','Rains Choi partial-transpose identity'),
          ('missing target square','Q(N,K*K)','Q(N,K)','sharp identity effect budget'),
          ('missing leftover Kraus weight','A[0][z]=Q(1);out.append(A)','A[0][z]=Q(0);out.append(A)','local Kraus completeness'),
          ('wrong minimum Bell dimension','d=max(1,min(a//2,K//2,isqrt(N//(4*r))))','d=max(2,min(a//2,K//2,isqrt(N//(4*r))))','deterministic packing capacity'),
          ('wrong root-fidelity convention','==Q(d,T)','==Q(d*d,T*T)','embedded target overlap'),
          ('wrong escort sign','rel=pa(pm(pa(alpha,ps(-1,one)),ell),ps(-1,z))','rel=pa(pm(pa(alpha,ps(-1,one)),ell),ps(1,z))','interior escort matching'),
        ]
        for name,old,new,diagnostic in changes:
            if old not in original:raise RuntimeError('Mutation target missing: '+name)
            check(name,original.replace(old,new),diagnostic,optimized=True)
    report={'status':'PASS','scope':'Ancillary source-mutation tests, not analytic proof checking','checks':rows,
            'checker_sha256':hashlib.sha256((ROOT/'check.py').read_bytes()).hexdigest()}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
