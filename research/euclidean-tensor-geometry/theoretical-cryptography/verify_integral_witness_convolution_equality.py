#!/usr/bin/env python3
"""Finite replay of the integral witness lemma on artificial laws."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import lcm
from random import Random
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form

rng=Random(4420110)
stats=Counter()


def encode(x,sizes):
    return tuple(int(i==v) for v,n in zip(x,sizes) for i in range(n))


def lattice(rows):
    assert rows
    return hermite_normal_form(Matrix(rows).T)


def compress(candidates,sizes):
    # Keep an actual word for each distinct pattern.
    obj={}
    for x,w in candidates:
        obj.setdefault(x,w)
    rows=list(obj)
    cols=[encode(x,sizes) for x in rows]
    mat=Matrix(cols).T
    ids=set(mat.rref()[1])
    got=[(rows[i],obj[rows[i]]) for i in sorted(ids)]
    r=len(got)
    basis=lattice([cols[i] for i in sorted(ids)])
    for i,c in enumerate(cols):
        if i in ids:
            continue
        more=hermite_normal_form(basis.row_join(Matrix(c)))
        if more!=basis:
            got.append((rows[i],obj[rows[i]]))
            basis=more
    m=len(sizes)
    assert 2**(2*(len(got)-r))<=m**r
    assert basis==lattice(cols)
    stats["compressed lists"]+=1
    stats["additional integral words"]+=len(got)-r
    return got


def step(x,P,a):
    x=list(x)
    for k,pk in enumerate(P):
        for _ in range(a):
            x[k]=pk[x[k]]
    return tuple(x)


def replay(sizes,moves,initial,large=False):
    got=[(initial,())]
    whole=[(initial,())]
    width=sum(sizes)
    for N,period,P in moves:
        got=compress([(step(x,P,a),w+(a,)) for x,w in got
                      for a in range(min(N,width))],sizes)
        whole=[(step(x,P,a),w+(a,)) for x,w in whole
               for a in range(min(N,period))]
        actual=lattice([encode(x,sizes) for x,w in whole])
        assert lattice([encode(x,sizes) for x,w in got])==actual
        if large:
            assert N>10**50
        stats["brute prefixes"]+=len(whole)
    for x,w in got:
        assert all(a<N for a,(N,_,_) in zip(w,moves))
        y=initial
        for a,(_,_,P) in zip(w,moves):
            y=step(y,P,a)
        assert y==x
    return got,whole


sizes=(2,2,2)
even=[(x,x) for x in ((0,0,0),(1,1,0),(1,0,1),(0,1,1))]
odd=[(1,0,0)]
arr=even+[(x,x) for x in odd]
assert Matrix([encode(x,sizes) for x,w in even]).rank()==4
assert Matrix([encode(x,sizes) for x,w in arr]).rank()==4
assert lattice([encode(x,sizes) for x,w in even]) != lattice([encode(x,sizes) for x,w in arr])
assert len(compress(arr,sizes))==5
assert all(sum(x)%2==0 for x,w in even) and sum(odd[0])%2==1

# A binary-large cyclic letter: actual permitted words include a whole
# period, but the compressed replay only uses the first width letters.
sizes=(3,5,7,11)
P=tuple(tuple((j+1)%n for j in range(n)) for n in sizes)
got,whole=replay(sizes,[(10**80+123,lcm(*sizes),P)],(0,0,0,0),True)
assert len(whole)>50*len(got)
stats["large cyclic instances"]+=1
for _ in range(50):
    sizes=tuple(rng.randrange(2,5) for j in range(rng.randrange(2,5)))
    initial=tuple(rng.randrange(n) for n in sizes)
    got=[(initial,())]
    whole=got[:]
    for j in range(rng.randrange(2,6)):
        letters=[tuple(tuple(rng.randrange(n) for u in range(n)) for n in sizes)
                 for k in range(rng.randrange(2,4))]
        def go(s,P):
            return tuple(p[x] for x,p in zip(s,P))
        got=compress([(go(x,P),w+(a,)) for x,w in got
                      for a,P in enumerate(letters)],sizes)
        whole=[(go(x,P),w+(a,)) for x,w in whole for a,P in enumerate(letters)]
        assert lattice([encode(x,sizes) for x,w in got])==lattice(
            [encode(x,sizes) for x,w in whole])
        stats["nonbijective prefixes"]+=len(whole)
    for n in (2,3,4,17):
        lab=[[rng.randrange(n) for x in range(k)] for k in sizes]
        f=lambda x:sum(lab[i][b] for i,b in enumerate(x))%n
        assert all(f(x)==0 for x,w in got)==all(f(x)==0 for x,w in whole)
        stats["finite group products"]+=1


def dot(x,y,p):
    return sum(a*b for a,b in zip(x,y))%p


def ftab(t,values,p):
    out=[F(0)]*p
    for x,a in values.items():
        out[dot(t,x,p)]+=a
    return tuple(out)


def add(x,y,p):
    return tuple((a+b)%p for a,b in zip(x,y))


def conv(x,y):
    p=len(x)
    z=[F(0)]*p
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            z[(i+j)%p]+=a*b
    return z


def forward(l,d,p):
    a,ls=l
    z={a:F(1)}
    for A,b in ls:
        Q=Counter()
        for x,w in z.items():
            for u,v in b.items():
                y=tuple(dot(row,u,p) for row in A)
                Q[add(x,y,p)]+=w*v
        z=dict(Q)
    return z


def basis(W,d,p):
    reach={(0,)*d}
    selected=[]
    for y in sorted(W):
        if y not in reach:
            selected.append(y)
            reach={tuple((a+t*b)%p for a,b in zip(x,y))
                   for x in reach for t in range(p)}
    assert reach==W
    return selected


def compare(a,b,d,p):
    Ts=[]
    for side,l in enumerate([a,b]):
        for A,v in l[1]:
            st=sorted(v)
            vals=[ftab(x,v,p) for x in st]
            Ts.append((side,st,vals,A))
    W=[set(),set()]
    for y in product(range(p),repeat=d):
        for side in (0,1):
            if all(len(set(vals[st.index(tuple(dot(y,col,p)
                     for col in zip(*A)))]))>1 for j,st,vals,A in Ts if j==side):
                W[side].add(y)
    if W[0]!=W[1]:
        stats["unequal support"]+=1
        return False
    bs=basis(W[0],d,p)
    shifts=[v[0] for v in (a,b)]
    Ash=tuple(((v-u)%p,) for v,u in zip(*shifts))
    chars=[tuple(F(int(j==i)) for j in range(p)) for i in range(p)]
    Ts.append((0,[(j,) for j in range(p)],chars,Ash))
    sizes=tuple(len(st) for j,st,vals,A in Ts)
    got=[((0,)*len(Ts),())]
    for b0 in bs:
        ds=[tuple(dot(b0,col,p) for col in zip(*A)) for j,st,vals,A in Ts]
        cand=[]
        for x,w in got:
            for t in range(p):
                xx=tuple(st.index(tuple((v+t*u)%p for u,v in zip(dv,st[x[i]])))
                         for i,((j,st,vals,A),dv) in enumerate(zip(Ts,ds)))
                cand.append((xx,w+(t,)))
        got=compress(cand,sizes)
    for x,w in got:
        nums=[list(chars[0]),list(chars[0])]
        for i,(side,st,vals,A) in enumerate(Ts):
            nums[side]=conv(nums[side],vals[x[i]])
        if len(set(u-v for u,v in zip(*nums)))>1:
            stats["found phase/value mismatch"]+=1
            return False
    return True


def random_law(d,p):
    factors=[]
    for i in range(rng.randrange(1,5)):
        r=rng.choice((1,1,2))
        A=tuple(tuple(rng.randrange(p) for j in range(r)) for i in range(d))
        pts=list(product(range(p),repeat=r))
        z=rng.choice(pts)
        B={x:F(1,3*len(pts))+F(2,3)*int(x==z) for x in pts}
        if rng.randrange(2)==0:
            vec=rng.choice(pts)
            B={x:sum(B[tuple((a-t*b)%p for a,b in zip(x,vec))]
                     for t in range(p))/p for x in pts}
        W={x for x in pts if len(set(ftab(x,B,p)))>1}
        assert all(add(x,y,p) in W for x,y in product(W,repeat=2))
        factors.append((A,B))
    return tuple(rng.randrange(p) for j in range(d)),factors


for p in (2,3,5):
    d=2 if p==5 else 3
    for i in range(24):
        a=random_law(d,p)
        if i%3==0:
            o,ls=a
            z=[]
            for A,B in ls:
                u=tuple(rng.randrange(p) for t in A[0])
                o=tuple((v-dot(row,u,p))%p for v,row in zip(o,A))
                z.append((A,{add(x,u,p):v for x,v in B.items()}))
            b=o,z[::-1]
        elif i%3==1:
            b=random_law(d,p)
        else:
            b=(tuple((x+int(i==0))%p for i,x in enumerate(a[0])),a[1])
        u=forward(a,d,p)
        v=forward(b,d,p)
        same=all(u.get(x,0)==v.get(x,0) for x in u.keys()|v.keys())
        assert compare(a,b,d,p)==same
        stats["explicit forward law pairs"]+=1
print("PASS integral witness compression:",dict(stats))
