#!/usr/bin/env python3
"""Exact finite-field rank / graph checks for the declared-clean trace note."""
from collections import Counter
from fractions import Fraction
from itertools import product
from functools import lru_cache
from math import prod


class Field:
    def __init__(self, p, modulus):
        self.p, self.f = p, len(modulus)
        self.order = p**self.f
        self.elements = range(self.order)
        self.digits = [tuple(x//p**j % p for j in range(self.f))
                       for x in self.elements]
        self.add = [[sum((a+b)%p*p**j for j,(a,b) in enumerate(zip(x,y)))
                     for y in self.digits] for x in self.digits]
        def mul(x, y):
            raw=[0]*(2*self.f-1)
            for i,a in enumerate(x):
                for j,b in enumerate(y):
                    raw[i+j] += a*b
            for h in range(2*self.f-2,self.f-1,-1):
                for j,c in enumerate(modulus):
                    raw[h-self.f+j] -= raw[h]*c
            return sum(raw[j]%p*p**j for j in range(self.f))
        self.mul = [[mul(x,y) for y in self.digits] for x in self.digits]
        assert all(1 in self.mul[a] for a in range(1,self.order))
        self.neg = [self.add[a].index(0) for a in self.elements]

    def pow(self,x,k):
        y=1
        while k:
            if k&1:
                y=self.mul[x][y]
            x=self.mul[x][x]
            k//=2
        return y

    def trace(self,x):
        y=0
        for j in range(self.f):
            y=self.add[y][self.pow(x,self.p**j)]
        assert y<self.p
        return y

    def subfield(self,d):
        out=tuple(x for x in self.elements if self.pow(x,self.p**d)==x)
        assert len(out)==self.p**d
        return out

    def stab(self,W):
        W=set(W)
        return {a for a in self.elements if all(self.mul[a][w] in W for w in W)}

    def subspaces(self):
        start=(0,)
        out={start}
        stack=[start]
        while stack:
            W=stack.pop()
            for a in self.elements:
                if a not in W:
                    T=tuple(sorted({self.add[w][self.mul[b][a]]
                                    for w in W for b in range(self.p)}))
                    if T not in out:
                        out.add(T)
                        stack.append(T)
        return sorted(out-{start})


def spanrank(rows,p):
    piv={}
    for v in rows:
        x=list(v)
        for i in range(len(x)):
            a=x[i]
            if not a:
                continue
            if i in piv:
                x=[(u-a*w)%p for u,w in zip(x,piv[i])]
            else:
                ai=pow(a,-1,p)
                piv[i]=tuple(u*ai%p for u in x)
                break
    return len(piv)


def dim(power,p):
    d=0
    while power>1:
        assert power%p==0
        power//=p
        d+=1
    return d


def independent(d,r,p):
    return prod(p**d-p**j for j in range(r))


def g_binom(d,r,p):
    return 0 if d<r else independent(d,r,p)//independent(r,r,p)


def matrix_law(M,N,p):
    out={}
    for d in range(max(0,N-M),N+1):
        r=N-d
        out[d]=Fraction(independent(M,r,p)*independent(N,r,p),
                        p**(M*N)*independent(r,r,p))
    assert sum(out.values())==1
    return out


def graph_checks(K):
    count=0
    spaces=K.subspaces()
    for W in spaces:
        stab=K.stab(W)
        assert K.p**dim(len(stab),K.p)==len(stab)
        for b,k in ((1,1),(1,2),(2,1),(2,2)):
            for entries in product(K.elements,repeat=b*k):
                pairs=tuple(tuple(entries[j*b+h] for h in range(b))
                            for j in range(k))
                kept=0
                for xs in product(W,repeat=b):
                    ys=[]
                    for row in pairs:
                        y=0
                        for x,a in zip(xs,row):
                            y=K.add[y][K.mul[x][a]]
                        ys.append(y)
                    kept+=all(y in W for y in ys)
                assert (kept==len(W)**b)==all(a in stab for a in entries)
                assert dim(kept,K.p)<=b*dim(len(W),K.p)
                count+=1
    return count


def law(K,n,masks):
    vec=tuple(product(K.elements,repeat=n))
    @lru_cache(None)
    def rows(a,W):
        return tuple(tuple(z for x in a for z in K.digits[K.mul[w][x]])
                     for w in W if w)
    counts=Counter()
    for aa in product(vec,repeat=len(masks)):
        rowsA=tuple(row for a,W in zip(aa,masks) for row in rows(a,W))
        counts[K.f*n-spanrank(rowsA,K.p)]+=1
    return {d:Fraction(x,len(vec)**len(masks)) for d,x in counts.items()}


def schedule_checks(K,n,schedules):
    p=K.p
    N=K.f*n
    count=0
    for masks in schedules:
        P=law(K,n,masks)
        ks=tuple(dim(len(W),p) for W in masks)
        m,M,J=len(ks),sum(ks),max(ks)
        U=matrix_law(M,N,p)
        stabs=tuple(K.stab(W) for W in masks)
        g=min(sum(a not in S for S in stabs) for a in range(p,K.order))
        primes=[l for l in range(2,K.f+1)
                if K.f%l==0 and all(l%j for j in range(2,l))]
        assert g==min(sum(dim(len(S),p)%l!=0 for S in stabs) for l in primes)
        for r in range(1,N+1):
            extra=sum(independent(d,r,p)*v for d,v in P.items())-sum(
                      independent(d,r,p)*v for d,v in U.items())
            bound=Fraction(p)**((N-M)*r-g)*sum(
                      (m*p**(r*J+abs(M-N)))**b for b in range(1,r))
            assert 0<=extra<=bound
            count+=1
        if M==N and all(K.f%k==0 and W==K.subfield(k)
                        for W,k in zip(masks,ks)):
            widths=sorted(ks,reverse=True)
            if all(a%b==0 for a,b in zip(widths,widths[1:])):
                residual=N
                expected=Fraction(1)
                for k in widths:
                    expected*=1-Fraction(1,p**residual)
                    residual-=k
                assert P.get(0,Fraction(0))==expected
                count+=1
    return count


def direct_trace_checks(K):
    p=K.p
    spaces=K.subspaces()
    count=0
    for W1,W2 in product(spaces,repeat=2):
        for a1,a2 in product(K.elements,repeat=2):
            literal=sum(all(K.trace(K.mul[w][K.mul[a][x]])==0
                            for a,W in ((a1,W1),(a2,W2)) for w in W)
                        for x in K.elements)
            rank=spanrank([K.digits[K.mul[a][w]]
                           for a,W in ((a1,W1),(a2,W2)) for w in W],p)
            assert literal==p**(K.f-rank)
            count+=1
    return count


def inversion_checks():
    count=0
    for p in (2,3,5):
        for d in range(13):
            for u in range(13):
                val=sum((-1)**(r-u)*p**((r-u)*(r-u-1)//2)*
                        g_binom(d,r,p)*g_binom(r,u,p) for r in range(u,d+1))
                assert val==(u==d)
                count+=1
    return count


def tower_checks():
    count=0
    for p,f in product((2,3,5),range(2,7)):
        for n in range(1,12):
            for u in range(n+1):
                w=prod(1-Fraction(1,p**(f*j)) for j in range(u+1,n+1))*prod(
                       1-Fraction(1,p**j) for j in range(1,f*u+1))
                base=prod(1-Fraction(1,p**(f*j)) for j in range(1,n+1))
                odd=prod(1-Fraction(1,p**j) for j in range(1,f*u+1) if j%f)
                assert w==base*odd
                count+=1
    return count


def main():
    a=Field(2,(1,1))
    b=Field(2,(1,1,0))
    c=Field(3,(1,0))
    e=Field(2,(1,1,0,0))
    z=Field(2,(1,1,0,0,0,0))
    graph=sum(graph_checks(K) for K in (a,b,c))
    traces=sum(direct_trace_checks(K) for K in (a,b,c))
    checks=0
    for K in (a,b,c,e):
        F,Ks=K.subfield(1),tuple(K.elements)
        W=tuple(sorted({K.add[x][K.mul[y][K.p]]
                        for x in F for y in F}))
        cases=[(Ks,),(F,)*K.f,(W,F),(W,)*2,(F,Ks,F)]
        if K.f%2==0:
            cases.append((K.subfield(2),)*2)
        checks+=schedule_checks(K,1,cases)
        if K is a:
            checks+=schedule_checks(K,2,[(Ks,Ks),(Ks,F,F),(F,F,F,F),(Ks,F)])
    checks+=schedule_checks(z,1,[(z.subfield(2),z.subfield(3)),
                                 (z.subfield(3),z.subfield(3)),
                                 (z.subfield(2),z.subfield(2))])
    print("PASS: graph / trace / rank moments / inversion / tower:",
          graph,traces,checks,inversion_checks(),tower_checks())


if __name__=="__main__":
    main()
