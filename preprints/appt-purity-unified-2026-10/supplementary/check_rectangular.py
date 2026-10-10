#!/usr/bin/env python3
"""Exact supporting checks for EXACT_RECTANGULAR.md, not an analytic or Lean proof."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
from random import Random
from check import (CheckFailed, require, const, var, add, scale, mul, power,
                   madd, mmul, trace, pt, mv)

ROOT = Path(__file__).resolve().parent

def diff(p, coordinate):
    result = {}
    for e,c in p.items():
        if e[coordinate]:
            ee=list(e);ee[coordinate]-=1
            result[tuple(ee)]=c*e[coordinate]
    return result

def sub(p,q): return add(p,scale(-1,q))

def symbols():
    m,D,L,i,s=[var(j) for j in range(5)]
    u=sub(power(m,2),const(1)); B=sub(sub(power(m,4),power(m,2)),scale(2,m))
    numerator=sub(mul(power(m,2),power(add(D,m),2)),
                  mul(mul(u,D),add(D,power(m,2),scale(2,m))))
    require(numerator==add(power(D,2),scale(-1,mul(B,D)),power(m,4)),
            'exact continuous candidate comparison')
    f=lambda d:add(power(d,2),scale(-1,mul(B,d)),power(m,4))
    require(f(power(m,2))==scale(-1,mul(mul(power(m,3),sub(m,const(2))),power(add(m,const(1)),2))),
            'lower comparison endpoint')
    require(f(sub(B,m))==scale(-1,mul(power(m,2),sub(sub(sub(power(m,3),power(m,2)),m),const(3)))),
            'upper comparison endpoint')
    y=add(m,const(3))
    require(sub(sub(sub(power(y,3),power(y,2)),y),const(3))==add(power(m,3),scale(8,power(m,2)),scale(20,m),const(12)),
            'positive shifted cutoff polynomial')
    N=add(L,scale(3,s),power(s,2)); d=add(L,scale(2,s))
    require(sub(mul(diff(N,4),d),scale(2,mul(N,diff(d,4))))==sub(mul(sub(scale(2,L),const(6)),s),L),
            'early-vertex derivative numerator')
    # Here m is an independent symbol denoting the graph count R, not local dimension.
    r=m; N=add(mul(power(r,2),L),mul(add(power(r,2),scale(2,mul(r,i))),s),mul(i,power(s,2)))
    d=add(mul(r,L),mul(add(r,i),s))
    expected=mul(r,sub(mul(sub(sub(sub(scale(2,mul(L,i)),power(r,2)),scale(3,mul(r,i))),scale(2,power(i,2))),s),mul(L,power(r,2))))
    require(sub(mul(diff(N,4),d),scale(2,mul(N,diff(d,4))))==expected,
            'middle-vertex derivative numerator')
    H=D
    require(mul(m,sub(mul(add(H,const(2)),power(sub(H,const(1)),2)),mul(sub(H,const(2)),power(add(H,const(1)),2))))==scale(4,m),
            'strict ceil versus floor identity')
    return 7

def data(m,n):
    D=m*n;R=m*(m-1)//2;S=m*(m+1)//2;L=D-m;t=((m-1)*n+1)//2
    return D,R,S,L,t

def qt(m,n,k=None):
    D,_,_,_,t=data(m,n); k=t if k is None else k
    return F(D*(m-1)**2+4*m*k,(D*(m-1)+2*k)**2)

def qsp(m,n):
    D=m*n
    return F(D+m*(m+2),(D+m)**2)

def vertices(m,n):
    D,R,S,L,t=data(m,n)
    for j in range(L,D+1):
        yield ('u',j), F(1,j)
    for i in range(1,L):
        hi=min(i,R)-max(0,i-(D-S))
        for j in range(L+1,D+1):
            s=j-L;den=hi*j+s*i
            alpha=F(hi+s,den);beta=F(hi,den)
            require(i*alpha+(j-i)*beta==1,'edge-vertex trace')
            require(hi*(alpha-beta)-s*beta==0,'edge-vertex physical linear constraint')
            value=i*alpha**2+(j-i)*beta**2
            theta=F(s*i,den)
            independent=theta**2/i+(1-theta**2)/j
            require(value==independent,'independent simplex-edge purity')
            yield ('edge',i,j),value

def enumerate_vertices():
    pairs={(m,n) for m in range(3,8) for n in range(m,3*m+1)}
    pairs.update((m,m**3-m-2+e) for m in range(3,8) for e in (-1,0,1))
    count=0;unique=0
    for m,n in sorted(pairs):
        best=max(qsp(m,n),qt(m,n));maximizers=[]
        for name,value in vertices(m,n):
            require(value<=best,'every cut-simplex vertex bounded')
            if value==best:maximizers.append(name)
            count+=1
        require(maximizers,'outer bound attained')
        if n>=m**3-m-2:
            D,_,_,_,t=data(m,n)
            require(maximizers==[('edge',t,D)],'unique tall-region maximizing vertex')
            unique+=1
    return {'dimension_pairs':len(pairs),'all_vertices':count,'unique_tall_region_cases':unique}

def thresholds():
    count=0;parity=0;examples=[]
    for m in range(3,151):
        n0=m**3-m-2
        for n in sorted({m,m+1,n0-2,n0-1,n0,n0+1,n0+2,2*n0}):
            D,_,_,_,t=data(m,n);u=m*m-1;C=F(m*m,u*D)
            target=qt(m,n)
            require((target>qsp(m,n))==(n>=n0),'exact method cutoff')
            require(qsp(m,n)>=F(1,D-m),'uniform vertices dominated')
            if (m-1)*n%2:
                H=u*n
                require(target==F(m*(H+2),(H+1)**2),'odd-parity exact value')
                require(C-target==F(m,H*(H+1)**2),'odd-parity rounding deficit')
                require(qt(m,n,t)-qt(m,n,t-1)==F(4*m,(H*H-1)**2),'ceil wins integer tie')
                parity+=1
            else:require(target==C,'even-parity exact value')
            count+=1
        if m in (3,4,5,10):
            examples.append({'m':m,'proved_cutoff':n0,'n':n0,'t':data(m,n0)[4],
                             'purity':str(qt(m,n0)),'gap_over_other_outer_branch':str(qt(m,n0)-qsp(m,n0))})
    return {'parameter_pairs':count,'odd_parity_checks':parity,'exact_examples':examples}

def physical_orbits():
    count=0
    for m,n in ((3,3),(3,5),(4,4),(4,7),(5,5),(5,8)):
        D,R,S,L,t=data(m,n)
        # Project onto all antisymmetric vectors, then pad with zero witness slots.
        P={}
        for a in range(m):
            for b in range(a+1,m):
                u=a*n+b;v=b*n+a
                P[u,u]=F(1,2);P[v,v]=F(1,2);P[u,v]=P[v,u]=F(-1,2)
        extras=[a*n+b for a in range(m) for b in range(m,n)]
        require(0<=t-R<=len(extras),'available zero-witness slots')
        for z in extras[:t-R]:P[z,z]=F(1)
        I={(a,a):F(1) for a in range(D)}
        A=madd((m-1,I),(2,P));Z=D*(m-1)+2*t
        psi={a*n+a:F(1) for a in range(m)}
        require(mmul(P,P)==P and trace(P)==t,'exact projection and multiplicity')
        require(trace(A)==Z and trace(mmul(A,A))/Z**2==qt(m,n),'physical target purity')
        require(not any(mv(pt(A,n),psi).values()),'uniform Schmidt vector is an exact kernel vector')
        count+=1
    return count

def negative_controls():
    # A necessary test alone must not certify the low-dimensional branch.
    m=4;n=4;D=m*n
    s=[F(m+1,D+m)]+[F(1,D+m)]*(D-1);R=m*(m-1)//2;S=m*(m+1)//2
    require(sum(s[:R])==sum(s[-S:]),'spurious spectrum passes the uniform test')
    require(F(1)-F(m,2)<0,'rank-two physical witness rejects spurious outer maximizer')
    m=4;n=59;t=data(m,n)[4]
    require(qt(m,n,t)>qt(m,n,t-1),'wrong floor rule is rejected')
    require(qt(m,n)<F(m,(m*m-1)*n),'continuous maximum is not the odd-parity answer')
    require(qsp(4,57)>qt(4,57),'moving the sufficient method cutoff down by one fails')
    return ['necessary-only membership does not imply APPT','floor rather than ceiling',
            'continuous value in the half-integer case','method cutoff moved down by one']

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    result={'status':'PASS','scope':'Exact finite and symbolic ancillary checks; not Lean, independent CI, or proof by finite enumeration',
            'symbolic_identities':symbols(),'vertex_enumeration':enumerate_vertices(),
            'thresholds_and_parities':thresholds(),'physical_boundary_orbits':physical_orbits(),
            'deliberate_failures':negative_controls()}
    result['source_hashes']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                             for name in ('EXACT_RECTANGULAR.md','check_rectangular.py','check.py')}
    text=json.dumps(result,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
