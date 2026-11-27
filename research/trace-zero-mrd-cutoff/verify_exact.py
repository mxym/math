#!/usr/bin/env python3
"""Exact determinant/slope and Hasse–Weil arithmetic cross-checks."""
from collections import Counter
from itertools import combinations


class Field:
    # Polynomial basis encoded in base p, coefficient order low to high.
    def __init__(self,p,modulus):
        self.p=p
        self.n=len(modulus)
        self.size=p**self.n
        self.mod=modulus
        self.weights=[p**i for i in range(self.n)]
        self.words=[tuple(x//i%p for i in self.weights) for x in range(self.size)]
        if p == 2:
            self.mask=self.size|sum(a*w for a,w in zip(modulus,self.weights))
        assert all(self.pow(x,self.size-1)==1 for x in range(1,self.size))

    def combine(self,a,b,sign=1):
        if self.p==2:
            return a^b
        return sum((i+sign*j)%self.p*w for i,j,w in zip(self.words[a],self.words[b],self.weights))

    def mul(self,a,b):
        if self.p==2:
            t=0
            while b:
                if b&1:
                    t^=a
                a<<=1
                if a&self.size:
                    a^=self.mask
                b>>=1
            return t
        acc=[0]*(2*self.n-1)
        for i,x in enumerate(self.words[a]):
            for j,y in enumerate(self.words[b]):
                acc[i+j]+=x*y
        for k in range(len(acc)-1,self.n-1,-1):
            c=acc[k]%self.p
            for i,v in enumerate(self.mod):
                acc[k-self.n+i]-=c*v
        return sum(acc[i]%self.p*w for i,w in enumerate(self.weights))

    def pow(self,x,k):
        a=1
        while k:
            if k&1:
                a=self.mul(a,x)
            x=self.mul(x,x)
            k>>=1
        return a

    def trace(self,x,q,m):
        z=0
        for _ in range(m):
            z=self.combine(z,x)
            x=self.pow(x,q)
        return z


def bits(poly,n):
    return tuple((poly>>i)&1 for i in range(n))


def verify(F,q,m,expect=None):
    Q=F.size
    assert Q==q**m
    base={x for x in range(Q) if F.pow(x,q)==x}
    assert len(base)==q
    h=[x for x in range(Q) if F.trace(x,q,m)==0]
    assert len(h)==q**(m-1)
    xp={x:F.pow(x,q) for x in h}
    inv={x:F.pow(x,Q-2) for x in h if x}
    vals=Counter()
    pairs=0
    for x in h:
        for y in h:
            a=F.combine(F.mul(xp[x],y),F.mul(x,xp[y]),-1)
            if x and y:
                assert (a==0)==(F.mul(x,inv[y]) in base)
            else:
                assert not a
            vals[a]+=1
            pairs+=1
    assert sum(vals.values())==len(h)**2
    nonzero={a for a in vals if a}
    criterion={F.pow(a,q-1) for a in nonzero}
    assert all(F.pow(v,(Q-1)//(q-1))==1 for v in criterion)
    # Each nonzero value counts a free ordered SL_2(q) orbit per plane.
    for a in nonzero:
        assert vals[a]%(q*(q*q-1))==0
        assert all(vals[F.mul(a,c)]==vals[a] for c in base if c)

    scattered=[]
    for delta in range(Q):
        seen={}
        accept=True
        for x in h:
            if not x:
                continue
            fx=F.combine(xp[x],F.mul(delta,F.pow(x,q**(m-1))))
            s=F.mul(fx,inv[x])
            if s in seen and F.mul(x,inv[seen[s]]) not in base:
                accept=False
                break
            seen[s]=x
        assert accept==(F.pow(delta,q) not in criterion)
        if delta and accept and F.pow(delta,(Q-1)//(q-1))==1:
            scattered.append(delta)
    if expect is not None:
        assert len(nonzero)==expect[0] and len(scattered)==expect[1]
    if q==2 and m==5:
        roots={x for x in range(Q)
               if F.pow(x,5)^F.pow(x,4)^F.pow(x,3)^F.pow(x,2)^1==0}
        assert len(roots)==5 and set(scattered)=={1}|roots
        assert all(F.pow(x,5)^x^1 for x in range(Q))
    if q==2 and m==7:
        assert scattered==[1]

    G=q*(q+1)*(q*q-2)+2
    assert G==q*q*(q*(q-1)-2)+2*q*(q-1)*(q+1)+2
    for a in range(1,Q):
        # The bound is squared to avoid inexact roots at odd extension degrees.
        discrepancy=q*q*vals[a]+q*(q+1)-(Q+1)
        assert discrepancy**2<=G*G*Q
    return pairs,Q-1


if __name__=="__main__":
    paircount=targetcount=0
    for p,q,m,mod,e in [
        (2,2,5,bits(0x25,5),(25,6)),
        (2,2,6,bits(0x43,6),(63,0)),
        (2,2,7,bits(0x83,7),(126,1)),
        (2,2,8,bits(0x11b,8),(255,0)),
        (3,3,3,(1,2,0),None),
        (2,4,3,bits(0x43,6),None),
        (5,5,2,(2,0),None),
    ]:
        a,b=verify(Field(p,mod),q,m,e)
        paircount+=a
        targetcount+=b
    for q in range(2,300):
        m=8 if q==2 else 9
        Q=q**m
        G=q*(q+1)*(q*q-2)+2
        lhs=Q+1-q*(q+1)
        assert lhs>0 and lhs**2>G*G*Q
    print(f"exact PASS: {paircount} ordered trace-pair checks and {targetcount} prescribed nonzero determinants")
    print("exact PASS: binary scattered counts at m=5,6,7,8 are 6,0,1,0; exceptional polynomials verified")
    print("exact PASS: determinant/slope equivalence tested in odd characteristic and a nonprime base field")
    print("exact PASS: 298 integral boundary checks of the analytic positivity inequality")
