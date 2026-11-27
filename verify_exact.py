#!/usr/bin/env python3
"""Deterministic table construction with exact conditional expectations."""
from fractions import Fraction as F
from itertools import combinations
from math import comb


def tails(q,L,U):
    sums=[]
    for r in range(q+1):
        pref=[0]
        for j in range(r+1):pref.append(pref[-1]+comb(r,j))
        sums.append(tuple(pref[max(0,min(r+1,L-d))]
                         +pref[-1]-pref[max(0,min(r+1,U+1-d))]
                         for d in range(q-r+1)))
    return sums


def construct(n,q,L,U):
    tab=tails(q,L,U)
    rows=[[0]*q]
    for _ in range(1,n):
        prev=[[row[w^i] for i in range(q)] for row in rows for w in range(q)]
        ds=[0]*len(prev)
        initial=len(prev)*tab[q][0]
        assert initial<2**q
        cur=initial
        cand=[]
        for i in range(q):
            next0=[d+a[i] for d,a in zip(ds,prev)]
            next1=[d+(1-a[i]) for d,a in zip(ds,prev)]
            rem=q-i-1
            c0=sum(tab[rem][d] for d in next0)
            c1=sum(tab[rem][d] for d in next1)
            assert c0+c1==cur
            if c0<=c1:
                cand.append(0);ds=next0;cur=c0
            else:
                cand.append(1);ds=next1;cur=c1
        assert cur==0
        rows.append(cand)
    checks=0
    for a,b in combinations(rows,2):
        for w in range(q):
            assert L<=sum(a[i]!=b[i^w] for i in range(q))<=U
            checks+=1
    return checks


def arithmetic():
    checks, caps=0,0
    for n in (3,4,10,100,1000,2**32):
        for eta in (F(1,4),F(1,9),F(1,100),F(3,1000)):
            x=2*n/eta
            lg=0
            while 2**lg<x:lg+=1
            threshold=16*lg/eta**2
            q=1
            while q<threshold:q*=2
            assert threshold<=q<2*threshold and 2*n*q<6*x**3
            assert (2*n*q)<x**32
            L=-((-q*(F(1,2)-eta))//1)
            U=q*(F(1,2)+eta)//1
            assert L==q-U and 0<L<=U<q
            p=F(L,U)*F(q*q//U,-((-q*q)//L))
            assert 0<p<=1
            assert p>=((1-2*eta)/(1+2*eta))**2*F(q-1,q+1)>=1-9*eta
            caps+=1
    for a in range(2,10):
        q=2**a
        for m in range(q//4,3*q//4+1):
            count=[0]*m
            for w in range(q):count[w%m]+=1
            assert max(count)<=4 and min(count)>=1
            assert set(count)<={q//m,(q+m-1)//m}
            assert sum(count)==q
            checks+=1
    print(f"exact PASS: {checks} one-word residue counts and {caps} uniform privacy/rounding parameter cases")


if __name__=="__main__":
    cases=((7,64,16,48),(18,64,16,48),(9,256,96,160))
    total=sum(construct(*args) for args in cases)
    print(f"exact PASS: {total} shifted table constraints after verified conditional-expectation decisions")
    arithmetic()
