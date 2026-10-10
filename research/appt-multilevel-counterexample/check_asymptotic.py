#!/usr/bin/env python3
"""Exact checks supporting ASYMPTOTIC.md; limits are proved analytically there."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import argparse, hashlib, json
from check import var, const, add, scale, mul, power, require

ROOT=Path(__file__).resolve().parent

def state(m,n):
    D=m*n;h=isqrt(m)
    if h*h<m:h+=1
    c=F(2,m+h);q=2-(m-3)*c
    a=2-F(2*(m-2))*c*c/q
    k=((m-1)*n+1)//2
    require(F(m*(m-1),2)<=k<=D-F(m*(m+1),2),'exact membership rank interval')
    require(q>0 and a>=c>=0 and (2-a)*q==2*(m-2)*c*c,'all-unitary PSD parameter test')
    T=a+(k-1)*c;S=a*a+(k-1)*c*c
    pur=(D+2*T+S)/(D+T)**2
    radius=D*D*(pur-F(1,D))
    require(radius==(S-T*T/D)/(1+T/D)**2,'centered purity identity')
    require(radius<=4+F(D,(m-1)**2),'finite upper bound for the classified subclass')
    p1=F(D+8,(D+2)**2)
    p2=F(D*(m-1)**2+4*m*k,(D*(m-1)+2*k)**2)
    return {'m':m,'n':n,'rank':k,'a':str(a),'c':str(c),'scaled_centered_purity':str(radius),
            'scaled_gap_above_conjecture':str(D*D*(pur-max(p1,p2)))}

def run():
    m,h=var(0),var(1);M=add(m,h);L=add(h,const(3))
    left=add(scale(4,mul(M,L)),scale(-8,add(m,const(-2))),scale(-4,L))
    right=scale(4,mul(add(h,const(1)),add(M,const(1))))
    require(left==right,'dimension-uniform nonnegative-spike factor identity')
    # An independent symbolic check of S-T^2/D used for the upper bound.
    D,a,c,y=var(0),var(1),var(2),var(3)
    T=add(a,mul(y,c));S=add(power(a,2),mul(y,power(c,2)))
    left=add(mul(D,S),scale(-1,power(T,2)))
    right=add(mul(add(D,const(-1)),power(a,2)),
              mul(mul(y,add(D,scale(-1,y))),power(c,2)),
              scale(-2,mul(mul(a,y),c)))
    require(left==right,'dimension-uniform centered variance decomposition')
    small=0
    for m0 in range(4,81):
        for mult in (1,2,4,8):state(m0,mult*m0);small+=1
    examples=[state(m0,mult*m0) for mult in (1,2,4,8) for m0 in (64,256,1024,4096)]
    for row in examples:
        if row['m']==4096:require(F(row['scaled_gap_above_conjecture'])>0,'explicit late joint-growth violation')
    return {'status':'PASS','scope':'Exact parameter and centered-purity identities; not finite proof of any asymptotic limit',
            'symbolic_identities':2,'small_parameter_regressions':small,'exact_examples':examples,
            'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'ASYMPTOTIC.md',ROOT/'check.py',Path(__file__).resolve()]}}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')
