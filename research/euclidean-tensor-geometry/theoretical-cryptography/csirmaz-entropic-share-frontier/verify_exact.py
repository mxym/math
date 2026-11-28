#!/usr/bin/env python3
"""Independent rank checks of the sharing schemes at the theorem's vertices."""
from fractions import Fraction as Q
from itertools import permutations
from random import Random


def gf(p, modulus=0):
    if not modulus:
        return p, lambda a,b: (a+b)%p, lambda a,b: (a*b)%p, lambda a: -a%p
    size=1<<(modulus.bit_length()-1)
    def mul(a,b):
        z=0
        while b:
            if b&1:
                z^=a
            b>>=1
            a<<=1
            if a&size:
                a^=modulus
        return z
    return size, lambda a,b: a^b, mul, lambda a: a


def linear(field, dimension):
    q,add,mul,neg=field
    inverses={x:next(i for i in range(1,q) if mul(i,x)==1) for x in range(1,q)}
    def rank(vectors):
        basis={}
        for v in vectors:
            v=list(v)
            for i in range(dimension):
                if not v[i]:
                    continue
                if i not in basis:
                    scale=inverses[v[i]]
                    basis[i]=[mul(scale,a) for a in v]
                    break
                t=neg(v[i])
                v=[add(x,mul(t,y)) for x,y in zip(v,basis[i])]
        return len(basis)
    def vec(*indices):
        v=[0]*dimension
        for i,c in indices:
            v[i]=add(v[i],c)
        return v
    return rank,vec


def k2(field):
    _,_,_,neg=field
    data=[]
    def add(gap,cost,s,d,make):
        rank,vec=linear(field,d)
        unit=lambda i: vec((i,1))
        data.append((gap,cost,s,rank,unit,make(vec,unit)))
    add(Q(0),(1,0),1,1,lambda v,u: ([u(0)],[],[],[u(0)]))
    add(Q(0),(0,1),1,1,lambda v,u: ([],[u(0)],[u(0)],[]))
    for ell in (2,3):
        add(Q(1,ell),(Q(1,ell),1),ell,ell+2,
            lambda v,u: ([u(0)], [u(i) for i in range(1,ell+1)],
                          [u(i) for i in range(1,ell)]+[u(ell+1)],
                          [v((0,1),(ell,1),(ell+1,1))]))
    add(Q(1,3),(Q(2,3),Q(1,3)),3,3,
        lambda v,u: ([u(1),u(2)],[u(0)],[v((0,1),(1,1))],[u(2)]))
    add(Q(1,2),(1,Q(1,2)),2,3,
        lambda v,u: ([u(0),u(2)],[u(1)],[v((1,1),(2,1))],[v((0,1),(2,1))]))
    add(Q(1),(1,2),1,4,
        lambda v,u: ([v((0,1),(3,neg(1)))],[u(1),u(3)],[u(2),u(3)],
                     [v((0,1),(1,neg(1)),(2,neg(1)))]))
    add(Q(1),(2,1),1,4,
        lambda v,u: ([u(1),u(2)],[v((0,1),(2,neg(1)))],
                     [v((0,1),(1,neg(1))),u(3)],[v((2,1),(3,neg(1)))]))
    for gap,cost,s,rk,unit,shares in data:
        secret=[unit(i) for i in range(s)]
        assert tuple(Q(rk(shares[i]),s) for i in (0,1))==cost
        for A in range(16):
            view=[r for j,block in enumerate(shares) if A>>j&1 for r in block]
            leak=s+rk(view)-rk(view+secret)
            qualified=any(A & m == m for m in (0b0011,0b0101,0b1110))
            if qualified:
                assert leak==s
            else:
                assert Q(leak,s)<=1-gap
    return len(data),16*len(data)


def flag(k,field,powers,rng):
    q,_,mul,neg=field
    t=(1<<k)-1
    n=k+t-1
    size=t+(t-1)*(t-2)//2
    assert q>=t
    rank,vec=linear(field,size)
    unit=lambda i: vec((i,1))
    pts=list(range(q))
    rng.shuffle(pts)
    pts=pts[:t]
    shares=[[] for _ in range(n)]
    offset=0
    for i,p in enumerate(powers):
        shares[i]=[unit(j) for j in range(offset, offset+p)]
        offset+=p
    cols=[1]*t
    offset=t
    for j in range(1,t):
        additions=[]
        for b in range(j-1):
            shares[k+b].append(unit(offset))
            additions.append((offset,neg(1)))
            offset+=1
        shares[k+j-1].append(vec(*list(enumerate(cols)),*additions))
        cols=[mul(x,y) for x,y in zip(cols,pts)]
    assert offset==size
    secret=[unit(i) for i in range(t)]
    assert tuple(rank(shares[i]) for i in range(k))==tuple(powers)
    if k<=3:
        masks=range(1<<n)
    else:
        masks=set()
        for A in range(1<<k):
            for b in range(t):
                prefix=(1<<b)-1
                masks.add(A|(prefix<<k))
                # Retain arbitrary later tail nodes while omitting the first missing one.
                later=(rng.randrange(1<<(t-1)) >> (b+1)) << (b+1)
                masks.add(A|((prefix|later)<<k))
    for mask in masks:
        view=[x for i,block in enumerate(shares) if mask>>i&1 for x in block]
        # Compare the actual full mask-dependent joint entropy against the
        # missing-coordinate rule; do not discard any partial split rows.
        leak=t+rank(view)-rank(view+secret)
        i=0
        while i<t-1 and mask>>(k+i)&1:
            i+=1
        z=sum(p for j,p in enumerate(powers) if not mask>>j&1)
        assert leak==t-max(z-i,0),(k,q,powers,mask,leak)
        if z>i:
            assert leak<=t-1
        else:
            assert leak==t
    return len(masks)


def main():
    nv=nc=0
    for p in (2,3,5,7):
        n,m=k2(gf(p))
        nv+=n
        nc+=m
    print(f"exact ranks: {nv} four-player field-vertex instances, {nc} full coalition views PASS")
    rng=Random(2652)
    total=0
    for k,field in ((2,gf(3)),(3,gf(2,0b1011)),(3,gf(7)),(4,gf(2,0b10011))):
        orders=list(permutations(1<<i for i in range(k)))
        if k==4:
            orders=[orders[11]]
        for powers in orders:
            total+=flag(k,field,powers,rng)
    print(f"exact ranks: {total} Vandermonde-prefix coalition views including incomplete splits PASS")


if __name__=="__main__":
    main()
