#!/usr/bin/env python3
"""Exact ancillary identities for SHARP_ASYMPTOTIC.md, not proof of its limits."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path
from random import Random

class CheckFailure(RuntimeError):
    pass

def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)

def ceil_sqrt(n: int) -> int:
    t=math.isqrt(n)
    return t+int(t*t!=n)

def run_checks() -> dict:
    rng=Random(263839); degrees_count=0; physical_count=0; box_count=0; uniform_count=0
    for m in range(3,31):
        R=m*(m-1)//2
        for trial in range(20):
            ds=sorted([F(rng.randrange(1,100),17) for _ in range(R)],reverse=True)
            w=ds[-1]; eta=[v-w for v in ds]; degrees=[F(0)]*m; t=0
            for i in range(m):
                for j in range(i+1,m):
                    degrees[i]+=eta[t]; degrees[j]+=eta[t]; t+=1
            tail=sum((v*v for v in eta[m-1:]),F(0))
            moment=sum((v*v for v in degrees),F(0))/m
            require(tail<=moment,"sorted triangular degree-square bound")
            shifted=sum(((v+(m-1)*w)**2 for v in degrees),F(0))/m
            expected=moment+4*F(m-1,m)*w*sum(eta,F(0))+(m-1)**2*w*w
            require(shifted==expected,"exact complete-background cross term")
            degrees_count+=1
    for m in range(4,20):
        for n in (m,2*m,3*m,4*m,8*m):
            D=m*n; R=m*(m-1)//2; S=m*(m+1)//2
            C=max(F(8),4+F(D,(m-1)**2))
            for k in (1,D//2,D-1):
                raw=[6*m-19]+[2*m-3]*(k-1)+[2*m-5]*(D-k); Z=sum(raw)
                lam=[F(v,Z) for v in raw]; b=lam[D-S]
                ds=[lam[i]-lam[-1-i] for i in range(R)]; w=ds[-1]
                eta=[v-w for v in ds]; A=sum(eta,F(0))
                V=sum((v*v for v in lam),F(0))-F(1,D)
                rhs=8*b*b+(F(D,4)-(m-1)**2)*w*w+(1-4*F(m-1,m))*w*A
                require(V<=rhs,"full triangular purity bound on APPT family")
                require(V<=C*b*b,"all-aspect finite APPT bound")
                physical_count+=1
    for m in range(2,31):
        ratio=F(m+1,m-1); kap=F(m*m,m*m-1); c=F(2,m-1)
        for n in (m,m+1,2*m,5*m):
            D=m*n; target=F(D)/(c+2)
            k=-(-target.numerator//target.denominator); theta=F(k,D)
            value=(1+(2*c+c*c)*theta)/(1+c*theta)**2
            gap=c*c*(1-(c+2)*theta)**2/(4*(c+1)*(1+c*theta)**2)
            require(kap-value==gap,"fixed-local-dimension exact projection gap")
            for z in (F(1,7),F(1,3),F(2,3),F(1),F(5,4)):
                require(kap-((ratio+1)*z-ratio*z*z)==ratio*(z-(ratio+1)/(2*ratio))**2,
                        "bulk-ratio moment square")
            values=[1+(ratio-1)*F(i,10) for i in range(11)]
            require(len(values)*sum((v*v for v in values),F(0))<=kap*sum(values,F(0))**2,
                    "finite bulk interval second-moment bound")
            box_count+=1
    for m in range(6,150):
        for n in (m,2*m,4*m,m*m,m**4):
            D=m*n; j=D-m*(m+1)//2+1
            C=max(F(8),4+F(D,(m-1)**2)); K=max(F(8),4+F(n,m))
            Ktilde=max(F(8),4+F(D,m*m-1))
            eps2=F(24,m*m)+F(3,(m-1)**2)
            require(C/j<=eps2<1,"uniform normalization coefficient bound")
            require(C<=F(m*m,(m-1)**2)*K,"uniform sharp upper comparison")
            require(K<=Ktilde<=F(m*m,m*m-1)*K,"joint and fixed dimension equivalence")
            h=ceil_sqrt(m); c=F(2,m+h); a=2-F(4*(m-2),(m+h)*(h+3))
            k=((m-1)*n+1)//2; y=k-1; theta=F(y,D)
            numerator=a*a*(1-F(1,D))+D*c*c*theta*(1-theta)-2*a*theta*c
            denom=(1+a/D+theta*c)**2
            Am=a*a*(1-F(1,m*m))-a*c
            Bm=m*m*c*c*(F(1,4)-(F(1,2*m)+F(1,m*m))**2)
            Qm=(1+a/F(m*m)+c/2)**2
            require(numerator/denom>=(Am+Bm*F(n,m))/Qm,"uniform broad-plateau lower estimate")
            uniform_count+=1
    failures=[]
    alternatives=[
        ("remove sorted assignment",lambda:require(F(1)<=F(2,4),
            "last-edge-only unsorted example violates triangular bound")),
        ("remove half of background cross term",lambda:require(
            F(50,4)==F(2,4)+9+2*F(3,4),"complete-background cross term changed")),
        ("replace fixed-m factor by one",lambda:require(
            F(4,3)<=1,"qubit projection purity exceeds the incorrect factor")),
    ]
    for name,action in alternatives:
        try:
            action()
        except CheckFailure as error:
            failures.append({"name":name,"rejected":True,"diagnostic":str(error)})
        else:
            raise CheckFailure("Incorrect alternative was accepted: "+name)
    return {"status":"PASS",
        "scope":"Exact finite supporting identities; not a finite proof of the analytic limit, Lean verification or independent peer review",
        "sorted_degree_lists":degrees_count,"known_APPT_state_bounds":physical_count,
        "fixed_local_dimension_cases":box_count,"uniform_aspect_comparisons":uniform_count,
        "deliberate_mathematical_failures":failures}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path)
    args=parser.parse_args(); report=run_checks(); root=Path(__file__).resolve().parent
    report['source_hashes']={name:hashlib.sha256((root/name).read_bytes()).hexdigest()
        for name in ['check_triangular.py','SHARP_ASYMPTOTIC.md','MULTISCALE.md']}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(text)
    print(text,end='')

if __name__=='__main__': main()
