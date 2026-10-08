#!/usr/bin/env python3
"""Sharp S_n five-subset atom/TV constants: pure-rational n=15,...,40 replay.

The JSON input contains literal cycle-count support bases and exact target
fractions. This script invokes no optimizer, no floating point, no external
packages and trusts no SciPy output. For each degree it reconstructs rational
primal and dual witnesses independently and checks every feasible reduced
conjugacy type via the all-rank exact transfer formula.
"""
import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

from transfer import moment, short_types


def solve(A, b):
    m=len(b)
    assert len(A)==m and all(len(row)==m for row in A)
    p=[[F(v) for v in A[i]]+[F(b[i])] for i in range(m)]
    for j in range(m):
        pivot=next((i for i in range(j,m) if p[i][j]!=0),None)
        assert pivot is not None,"singular support basis"
        p[j],p[pivot]=p[pivot],p[j]
        z=p[j][j]
        p[j]=[v/z for v in p[j]]
        for i in range(m):
            if i!=j:
                z=p[i][j]
                p[i]=[p[i][t]-z*p[j][t] for t in range(m+1)]
    x=[p[i][-1] for i in range(m)]
    assert all(sum(F(a)*v for a,v in zip(A[i],x))==F(b[i])
               for i in range(m))
    return x


def conjugacy_size(n,t):
    rem=n-sum((j+1)*v for j,v in enumerate(t))
    assert rem==0 or rem>=6
    den=rem if rem else 1
    for j,c in enumerate(t,1):
        den*=j**c*factorial(c)
    size,mod=divmod(factorial(n),den)
    assert mod==0 and size>0
    return size


def check(r):
    n=r["n"];k=5
    assert set(r)=={"n","C","P","Q"} and isinstance(n,int)
    assert 15<=n<=40
    identity=(n,0,0,0,0)
    pos=[identity]+[tuple(v) for v in r["P"]]
    neg=[tuple(v) for v in r["Q"]]
    assert len(pos)==4 and len(neg)==3
    support=pos+neg
    assert len(set(support))==7
    assert all(len(v)==k and all(isinstance(q,int) and q>=0 for q in v)
               for v in support)
    assert all((n-sum((i+1)*v[i] for i in range(k)))==0 or
               (n-sum((i+1)*v[i] for i in range(k)))>=k+1
               for v in support)

    moments=[moment(n,k,v) for v in support]
    B=[[1,0,*f[:k]] for f in moments[:4]]+[
        [0,1,*(-x for x in f[:k])] for f in moments[4:]]
    target=[1,1]+[0]*k
    weights=solve(list(map(list,zip(*B))),target)
    dual=solve(B,[1]+[0]*6)
    assert all(w>0 for w in weights)
    assert sum(weights[:4])==sum(weights[4:])==1
    for j in range(k+1):
        assert sum(weights[i]*moments[i][j] for i in range(4))==\
               sum(weights[i+4]*moments[i+4][j] for i in range(3))
    expected=F(r["C"])
    hi,lo=dual[0],-dual[1]
    assert 0<expected<1 and expected==weights[0]==hi-lo
    def evaluation(c):
        m=moment(n,k,c)
        return F(int(c==identity))-sum(dual[j+2]*m[j] for j in range(k))
    assert all(evaluation(c)==hi for c in pos)
    assert all(evaluation(c)==lo for c in neg)
    count=0
    for c in short_types(n,k):
        val=evaluation(c)
        assert lo<=val<=hi,(n,c,val,lo,hi)
        count+=1

    # Exact realization on S_n: central class weights and positive perturbation
    # of the uniform group measure. The positive support includes only identity.
    sizes=[conjugacy_size(n,t) for t in support]
    delta=min(F(sizes[i],2*factorial(n)*weights[i]) for i in range(4,7))
    assert delta>0
    for i in range(4,7):
        assert F(1,factorial(n))-delta*weights[i]/sizes[i]>0
    assert delta*weights[0]==delta*expected
    return count,expected


def main():
    inp=Path(__file__).resolve().parent/'certificates'/'k5_n15_40.json'
    data=json.loads(inp.read_text(encoding='utf8'))
    assert data["scope"]=="15 <= n <= 40"
    records=data["records"]
    assert len(records)==26
    assert [r["n"] for r in records]==list(range(15,41))
    checks=0
    for r in records:
        count,c=check(r)
        checks+=count
        print("PASS k=5 n=%d states=%d sharp=%s"%(r["n"],count,c),flush=True)
    print("ALL 26 RANK-SIX EXACT CERTIFICATES PASSED; STATES=%d"%checks)

if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
