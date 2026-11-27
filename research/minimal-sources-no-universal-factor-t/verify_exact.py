#!/usr/bin/env python3
"""Finite-field ranks, affine fibers, and exact budget controls."""
from collections import Counter,defaultdict
from itertools import combinations,product
from random import Random


class Field:
    def __init__(self,s,poly):
        self.n=1<<s
        self.s=s
        def m(a,b):
            out=0
            while b:
                if b&1: out^=a
                a<<=1
                if a&self.n:a^=poly
                b>>=1
            return out
        self.mult=[[m(a,b) for b in range(self.n)] for a in range(self.n)]
        self.inv=[None]+[self.mult[a].index(1) for a in range(1,self.n)]
    def powers(self,a,limit):
        l=[1]
        for _ in range(limit):l.append(self.mult[l[-1]][a])
        return l
    def eval(self,P,a):
        x=0
        for z in reversed(P):
            x=self.mult[x][a]^z
        return x
    def rank(self,rows):
        piv={}
        for row in rows:
            r=list(row)
            for j,v in enumerate(r):
                if not v:continue
                if j in piv:
                    r=[a^self.mult[v][b] for a,b in zip(r,piv[j])]
                else:
                    piv[j]=[self.mult[w][self.inv[v]] for w in r]
                    break
        return len(piv)


def b_rank(vs):
    piv={}
    for v in vs:
        while v:
            j=v.bit_length()-1
            if j not in piv:
                piv[j]=v
                break
            v^=piv[j]
    return len(piv)


def ranks():
    rng=Random(100267)
    checks=0;shorts=0
    for s,poly,n in ((3,11,6),(4,19,10),(5,37,18),(6,67,30)):
        K=Field(s,poly)
        for t in range(1,min(7,n//2)):
            pts=list(range(1,n+1))
            ncoef=3*t+1
            hi_proj=[tuple(int(j==i) for j in range(ncoef))
                     for i in range(t,3*t+1)]
            cols=[]
            for a in pts[:-1]:
                p=K.powers(a,2*t-1)
                cols.append(sum(p[2*j+1]<<(s*j) for j in range(t)))
            for k in range(t+1):
                Cs=list(combinations(pts,k)) if n<=10 else [
                    tuple(rng.sample(pts,k)) for _ in range(25)]
                for C in Cs:
                    A=[];B=[];inp=[]
                    for a in C:
                        p=K.powers(a,2*t)
                        A.append(p[1:t+1]+p[:1]+[0]*(2*t))
                        B.append([0]*t+p)
                        inp.append(p[1:t+1])
                    assert K.rank(inp)==k
                    assert K.rank(A+B)==2*k
                    assert K.rank(hi_proj+A+B)-2*k==2*t+1-k
                    checks+=1
                    for h in {min(k,2*t),min(n-1,2*t)}:
                        J=rng.sample(cols,h)
                        assert b_rank(J)==h
                        shorts+=1
    print(f"exact PASS: {checks} double-sharing projection ranks and {shorts} BCH projection ranks")


def fibers():
    t=1;K=Field(2,7)
    seen=0
    for C in ((),(1,),(2,),(3,)):
        d=defaultdict(Counter)
        for c,l,h1,h2 in product(range(K.n),repeat=4):
            H=(c,h1,h2)
            lab=tuple(K.eval(P,a) for P in ((c,l),H) for a in C)
            d[lab][H]+=1
        assert len(d)==K.n**(2*len(C))
        for v,count in d.items():
            assert len(count)==K.n**(2*t+1-len(C))
            assert set(count.values())=={K.n**(t-len(C))}
            for H in count:
                assert tuple(K.eval(H,a) for a in C)==v[len(C):]
            seen+=len(count)
    print(f"exact PASS: {seen} brute-force high-fiber atoms with fixed separate low/high packets, including nonzero constants")


def constraints():
    checks=0
    for t in range(3,101):
        for n in (2*t+2,2*t*t,4*t*t):
            s=n.bit_length()
            assert (1<<(s-1))<=n<(1<<s)
            assert (3*t*t+3*t)*s==2*t*s+t*(3*t+1)*s
            assert 1<=t-2<=n-4
            assert n-2>t
            checks+=1
    print(f"exact PASS: {checks} budget, honest parity slot, and lower-bound parameter cases")


if __name__=="__main__":
    ranks()
    fibers()
    constraints()
