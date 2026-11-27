#!/usr/bin/env python3
"""Exact checks of finite-field uniform-support hash load identities."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod


class Field:
    def __init__(self,q,add,mul):
        self.q,self.el=q,range(q)
        self.a=[[add(i,j) for j in self.el] for i in self.el]
        self.m=[[mul(i,j) for j in self.el] for i in self.el]
        self.neg=tuple(next(y for y in self.el if self.a[x][y]==0) for x in self.el)
        self.inv=(None,)+tuple(next(y for y in self.el if self.m[x][y]==1) for x in range(1,q))

    def add(self,a,b):
        return self.a[a][b]

    def mul(self,a,b):
        return self.m[a][b]

    def total(self,xs):
        out=0
        for x in xs:
            out=self.add(out,x)
        return out

    def rank(self,A):
        A=list(map(list,A))
        r=0
        for j in range(len(A[0]) if A else 0):
            p=next((i for i in range(r,len(A)) if A[i][j]),None)
            if p is None:
                continue
            A[r],A[p]=A[p],A[r]
            inv=self.inv[A[r][j]]
            for i in range(r+1,len(A)):
                x=self.mul(self.neg[A[i][j]],inv)
                if x:
                    A[i]=[self.add(a,self.mul(x,b)) for a,b in zip(A[i],A[r])]
            r+=1
        return r


def prime(p):
    return Field(p,lambda x,y:(x+y)%p,lambda x,y:x*y%p)


def f9():
    def add(x,y):
        return (x%3+y%3)%3 + 3*((x//3+y//3)%3)
    def mul(x,y):
        a,b,c,d=x%3,x//3,y%3,y//3
        return (a*c-b*d)%3 + 3*((a*d+b*c)%3)
    return Field(9,add,mul)


def f16():
    def mul(x,y):
        z=0
        for _ in range(4):
            if y&1:
                z^=x
            y>>=1
            x<<=1
            if x&16:
                x^=19
        return z
    return Field(16,lambda x,y:x^y,mul)


def is_coset(K,S):
    x=min(S)
    H={K.add(y,K.neg[x]) for y in S}
    return all(K.add(a,b) in H for a,b in product(H,repeat=2))


def coefficient_stabilizer(K,H):
    return {a for a in K.el if all(K.mul(a,x) in H for x in H)}


def check_cosets():
    K=f9()
    count=0
    for mask in range(1,1<<K.q):
        S={a for a in K.el if mask>>a&1}
        # The characteristic is 3, so 2+2=1 holds in the prime subfield.
        closed=all(K.add(K.mul(2,a),K.mul(2,b)) in S for a,b in product(S,repeat=2))
        assert closed==is_coset(K,S)
        count+=1
    K=f16()
    a=2
    Fs4={x for x in K.el if K.mul(K.mul(x,x),K.mul(x,x))==x}
    H={0,1,a,1^a}
    S={0,1,a,K.mul(a,a)}
    assert len(Fs4)==4 and len(H)==len(S)==4 and not is_coset(K,S)
    assert coefficient_stabilizer(K,Fs4)==Fs4
    assert coefficient_stabilizer(K,H)=={0,1}
    for B in (Fs4,H):
        stab=coefficient_stabilizer(K,B)
        for c,d in product(K.el,repeat=2):
            assert (all(K.add(K.mul(c,x),K.mul(d,y)) in B for x,y in product(B,repeat=2))
                    ==(c in stab and d in stab))
            count+=1
    print(f"PASS {count} exact closure and stabilizer checks")
    return K,Fs4,H,S


def falling(n,k):
    return prod(n-i for i in range(k))


def tagged_moments(K,S):
    V=tuple(product(S,repeat=2))
    Y=tuple(K.el)
    all_loads=[]
    for a in product(Y,repeat=2):
        h=Counter(K.total(K.mul(s,t) for s,t in zip(a,x)) for x in V)
        all_loads.append(h)
    count=0
    for r,t in ((1,1),(2,1),(1,2),(3,0)):
        assert r+t<=3
        moment_left=sum(
            F(sum(falling(h[u],r)*falling(h[v],t) for u,v in product(Y,repeat=2)),K.q**2)
            for h in all_loads)/len(all_loads)
        moment_right=F(0)
        for V1 in product(V,repeat=r):
            if len(set(V1))!=len(V1):
                continue
            for V2 in product(V,repeat=t):
                if len(set(V2))!=len(V2):
                    continue
                mat=[(*x,1,0) for x in V1]+[(*x,0,1) for x in V2]
                rho=K.rank(mat)
                moment_right+=F(1,K.q**rho)
        assert moment_left==moment_right
        count+=1
    print(f"PASS {count} exact tagged load moments over field of size {K.q}, |S|={len(S)}")


@lru_cache(None)
def gb(d,j,q):
    if j<0 or j>d:
        return 0
    num=prod(q**(d-i)-1 for i in range(j))
    den=prod(q**(j-i)-1 for i in range(j))
    assert num%den==0
    return num//den


def nullity_probability(a,b,d,q):
    r=a-d
    if not 0<=r<=min(a,b):
        return F(0)
    return F(1,q**(a*b))*prod(F((q**a-q**i)*(q**b-q**i),q**r-q**i) for i in range(r))


def check_rank_laws():
    inv_count=0
    for q in (2,3,4,5):
        for d in range(13):
            for u in range(d+3):
                rhs=sum((-1)**(j-u)*q**((j-u)*(j-u-1)//2)*gb(d,j,q)*gb(j,u,q)
                        for j in range(u,d+1))
                assert rhs==int(d==u)
                inv_count+=1
    print(f"PASS {inv_count} exact Gaussian-binomial inversions")
    nm=0
    for q in (2,3):
        K=prime(q)
        for a,b in product(range(1,4),repeat=2):
            if a*b>7:
                continue
            counts=Counter()
            for X in product(K.el,repeat=a*b):
                matrix=[X[i*a:(i+1)*a] for i in range(b)]
                d=a-K.rank(matrix)
                counts[d]+=1
            for d in range(a+1):
                assert F(counts[d],q**(a*b))==nullity_probability(a,b,d,q)
            for j in range(a+2):
                exp_ordered=sum(nullity_probability(a,b,d,q)*prod(q**d-q**i for i in range(j))
                                for d in range(a+1))
                assert exp_ordered==F(prod(q**a-q**i for i in range(j)),q**(b*j))
            nm+=1
    print(f"PASS {nm} exact enumerated comparison rank laws and kernel moment vectors")


def restricted_sample(K,H):
    stab=coefficient_stabilizer(K,H)
    Q=len(stab)
    a_size=len(H)**2
    V=tuple(product(H,repeat=2))
    profiles=Counter()
    # The restricted block map need not have independent entries over F0;
    # check its exact histogram structure without assuming equality of finite laws.
    for a in product(K.el,repeat=2):
        loads=Counter(K.total(K.mul(c,x) for c,x in zip(a,v)) for v in V)
        h=loads[0]
        assert len(loads)*h==a_size and all(j==h for j in loads.values())
        d=0
        while Q**d<h:
            d+=1
        assert Q**d==h
        tv=sum(abs(F(loads[u],a_size)-F(1,K.q)) for u in K.el)/2
        assert tv==1-F(len(loads),K.q)
        profiles[d]+=1
    if Q==4:
        for d in range(3):
            assert F(profiles[d],K.q**2)==nullity_probability(2,2,d,4)
    print(f"PASS {K.q**2} restricted-map load histograms, stabilizer size {Q}, nullities {dict(profiles)}")


if __name__=="__main__":
    K,Fs4,H,S=check_cosets()
    tagged_moments(prime(3),{0,1})
    tagged_moments(f9(),{0,1,3})
    tagged_moments(K,S)
    check_rank_laws()
    restricted_sample(K,Fs4)
    restricted_sample(K,H)
