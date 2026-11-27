#!/usr/bin/env python3
"""Enumerated kernels, projective tests, full-row filtering and Moore fibers."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod

def prime(q):
    return (q,lambda x,y:(x+y)%q,lambda x,y:x*y%q)

def binary(deg,poly):
    q=1<<deg
    def mul(x,y):
        z=0
        while y:
            if y&1: z^=x
            x<<=1
            if x&q:x^=poly
            y>>=1
        return z
    return (q,lambda x,y:x^y,mul)

def dot(a,b,field):
    _,add,mul=field
    z=0
    for x,y in zip(a,b): z=add(z,mul(x,y))
    return z

def spans(field,k,r):
    q,add,mul=field
    vecs=list(product(range(q),repeat=k)); zero=(0,)*k
    found={frozenset((zero,))}
    for _ in range(r):
        found={frozenset(tuple(add(a,mul(c,b)) for a,b in zip(z,x))
                         for c in range(q) for z in U)
               for U in found for x in vecs if x not in U}
    return sorted(found,key=lambda U:sorted(U))

def exact_laws(field,k,r):
    q,_,_=field; U=spans(field,k,r); V=spans(field,k,k-r)
    space=list(product(range(q),repeat=k)); dim={q**j:j for j in range(k+1)}
    ref=Counter(); conditional=Counter(); removed=0; total=q**(k*r)
    S=[Counter() for _ in U]
    for rows in product(space,repeat=r):
        ker={x for x in space if all(dot(row,x,field)==0 for row in rows)}
        good=(len(ker)==q**(k-r)); removed+=not good
        for j,T in enumerate(U):
            d=dim[len(ker.intersection(T))]
            if j==0:
                ref[d]+=1
                if good: conditional[d]+=1
            S[j][d]+=1
    assert all(L==ref for L in S)
    n=total-removed
    pi=F(n,total)
    assert pi==prod(1-F(q**j,q**k) for j in range(r))
    nu=F(sum(d*c for d,c in conditional.items()),n)
    mu=F(sum(d*c for d,c in ref.items()),total)
    p=F(ref[0],total)
    assert p==prod(1-F(1,q**j) for j in range(1,r+1))
    for T in U:
        assert F(sum(dim[len(T.intersection(W))] for W in V),len(V))==nu
    assert 0<=mu-nu<=r*(1-pi)<=F(r*q**r,q**k*(q-1))
    assert F(conditional[0],n)>=p and nu<=mu
    if k==r: assert nu==0<mu and F(conditional[0],n)==1>p
    if q==2: assert mu<F(143,168)
    else: assert mu<F(1,q-1)
    return total,len(U),len(V)

def embedding(q,k):
    if (q,k)==(2,3): return binary(3,0b1011),lambda x:x[0]+2*x[1]+4*x[2]
    if (q,k)==(3,2):
        def mul(x,y):
            a,b=x%3,x//3; c,d=y%3,y//3
            return (a*c+2*b*d)%3+3*((a*d+b*c)%3)
        return (9,lambda x,y:(x%3+y%3)%3+3*((x//3+y//3)%3),mul),lambda x:x[0]+3*x[1]
    assert (q,k)==(4,2)
    K=binary(4,0b10011); _,add,mul=K
    sub=next(x for x in range(2,16) if mul(x,x)^x^1==0)
    i=(0,1,sub,sub^1)
    return K,lambda x:add(i[x[0]],mul(2,i[x[1]]))

def evaluations(field,k,r,m):
    q,_,_=field
    (z,add,mul),emb=embedding(q,k)
    coords={emb(x):x for x in product(range(q),repeat=k)}
    assert len(coords)==z
    def fp(x):
        y=1
        for _ in range(q):y=mul(y,x)
        return y
    num=0
    for s in range(1,m+1):
        for W in spans(field,k,s):
            basis=[]
            covered={0}
            for x in sorted(W):
                a=emb(x)
                if a not in covered:
                    basis.append(a)
                    scalars=[emb((i,)+(0,)*(k-1)) for i in range(q)]
                    covered={add(b,mul(c,a)) for b in covered for c in scalars}
            assert len(basis)==s
            map_rows=[]
            for x in basis:
                row=[]
                for _ in range(m):row.append(x); x=fp(x)
                map_rows.append(row)
            laws=Counter(tuple(coords[dot(a,row,(z,add,mul))][:r] for row in map_rows)
                         for a in product(range(z),repeat=m))
            assert len(laws)==q**(r*s)
            assert set(laws.values())=={z**m//q**(r*s)}
            num+=1
    return num

def elementary_sample():
    q,_,mul=binary(4,0b10011)
    D=Counter()
    for x,y in product(range(q),repeat=2):
        z=1; out=0
        for j in range(4):
            out|=(mul(y,z)&1)<<j
            z=mul(z,x)
        D[out]+=1
    def parity(x): return x.bit_count()&1
    bias=max(abs(sum(w*(-1)**parity(mask&a) for a,w in D.items()))
             for mask in range(1,16))
    assert F(bias,q*q)<=F(3,q)
    for W in spans(prime(2),2,1)+spans(prime(2),2,2):
        kill=sum(w for a,w in D.items()
                 if all(not parity(a&((x[0]+2*x[1])<<j)) for j in (0,2) for x in W))
        ref=F(1,len(W)**2)
        assert abs(F(kill,q*q)-ref)<=(1-ref)*F(bias,q*q)
    return sum(D.values()),F(bias,q*q)

def main():
    ns=[exact_laws(field,k,r) for field,k,r in
        ((prime(2),2,2),(prime(2),3,2),(prime(2),4,2),
         (prime(3),3,2),(binary(2,0b111),2,2),(binary(2,0b111),3,2))]
    print(f'Independent matrix-kernel enumeration: {sum(z[0] for z in ns)} maps, {sum(z[1] for z in ns)} test spaces; minimax, conditioning and one-sided filtering PASS')
    counts=[evaluations(field,k,r,m) for field,k,r,m in
            ((prime(2),3,2,2),(prime(3),2,2,2),(binary(2,0b111),2,2,2))]
    print(f'Exact Moore evaluation fibers: {sum(counts)} subspaces over F2, F3 and F4')
    pairs,bias=elementary_sample()
    print(f'Elementary direct-entry sampler: {pairs} seeds, exact maximum character bias {bias}, all small killing events PASS')

if __name__=='__main__': main()
