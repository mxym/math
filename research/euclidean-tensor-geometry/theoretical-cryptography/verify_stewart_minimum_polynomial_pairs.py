#!/usr/bin/env python3
"""Enumerate weighted plane trees with weighted degree passport 3^10, 5^6."""

from collections import Counter
from functools import lru_cache
from itertools import product

CAPS=(3,5)
BMAX,WMAX=10,6

@lru_cache(None)
def forest(color,b,w,s):
    """Ordered forests at a vertex of type 1-color, child weights summing to s."""
    if min(b,w,s)<0:
        return ()
    if not s:
        return ((),) if b==w==0 else ()
    out=[]
    for k in range(1,min(3,s)+1):
        for m,n in product(range(b+1),range(w+1)):
            if (3*m-5*n)*(1-2*color)!=k:
                continue
            a=branch(color,k,m,n)
            if a:
                z=forest(color,b-m,w-n,s-k)
                out.extend(((k,p),)+q for p,q in product(a,z))
    return tuple(out)

@lru_cache(None)
def branch(color,k,b,w):
    """Rooted plane component with the edge of weight k to its parent omitted."""
    if (3*b-5*w)*(1-2*color)!=k:
        return ()
    return forest(1-color,b-(color==0),w-(color==1),CAPS[color]-k)

def edge_rootings():
    for k in range(1,4):
        for b,w in product(range(BMAX+1),range(WMAX+1)):
            a=branch(0,k,b,w)
            if a:
                z=branch(1,k,BMAX-b,WMAX-w)
                for p,q in product(a,z):
                    yield (k,p,q)

def all_encodings(tree):
    colors=[]
    rot=[]
    def node(c):
        v=len(colors)
        colors.append(c); rot.append([])
        return v
    r,s=node(0),node(1)
    weights={}
    def edge(a,b,k):
        rot[a].append(b)
        rot[b].append(a)
        weights[a,b]=weights[b,a]=k
    def descend(a,t):
        for k,sub in t:
            b=node(1-colors[a])
            edge(a,b,k);descend(b,sub)
    k,p,q=tree
    edge(r,s,k)
    descend(r,p);descend(s,q)
    if len(colors)!=16 or sum(colors)!=6:
        raise AssertionError('global vertex count')
    if any(sum(weights[a,b] for b in adj)!=CAPS[colors[a]] for a,adj in enumerate(rot)):
        raise AssertionError('local weighted degree')
    def side(a,b,flip):
        L=rot[a]
        k=L.index(b)
        children=L[k+1:]+L[:k]
        if flip:
            children.reverse()
        return tuple((weights[a,c],side(c,a,flip)) for c in children)
    def roots(flip):
        for a in range(len(colors)):
            if colors[a]==0:
                for b in rot[a]:
                    yield weights[a,b],side(a,b,flip),side(b,a,flip)
    return tuple(roots(False)),tuple(roots(True))

def verify_trees():
    trees=tuple(edge_rootings())
    require(len(trees)==133 and len(set(trees))==133, 'distinct edge rootings')
    require(Counter(t[0] for t in trees)=={1:47,2:39,3:47}, 'rooting weights')
    labs={}
    for i,t in enumerate(trees):
        a,b=all_encodings(t)
        k=min(a)
        if k not in labs:
            labs[k]=(min(b)==k,len(a)//len(set(a)),Counter(w for w,x,y in a))
    require(Counter((real,aut) for real,aut,ws in labs.values()) ==
            {(False,1):6,(False,3):2,(True,1):2,(True,5):1}, 'mirror/automorphism classes')
    require(sum(15//aut for real,aut,ws in labs.values())==len(trees), 'orbit total')
    print('PASS 133 edge-rootings, 11 plane classes, 3 with real structure')


def require(ok,why):
    if not ok:
        raise AssertionError(why)


def irreducible_mod5(P):
    p=[a%5 for a in P]
    require(len(p)==9 and p[-1]!=0, 'monic reduction degree')
    # A reducible degree 8 polynomial over a field has a monic factor of degree <=4.
    for d in (1,2,3,4):
        for a in product(range(5),repeat=d):
            v=p.copy()
            for k in range(8,d-1,-1):
                q=v[k]
                for i in range(d):
                    v[k-d+i] = (v[k-d+i]-q*a[i])%5
                v[k]=0
            require(any(v[:d]), 'irreducible modulo 5')


def count_real_roots(P):
    from fractions import Fraction
    def trim(a):
        while a and not a[-1]:
            a.pop()
        return a
    def rem(p,q):
        r=p.copy()
        while len(r)>=len(q):
            c=r[-1]/q[-1]
            m=len(r)-len(q)
            for i,v in enumerate(q):
                r[m+i]-=c*v
            trim(r)
        return r
    seq=[list(map(Fraction,P)),[Fraction(i*P[i]) for i in range(1,len(P))]]
    while True:
        r=rem(*seq[-2:])
        if not r:
            break
        seq.append([-u for u in r])
    require(len(seq[-1])==1,'Sturm squarefree')
    def v(s):
        m=[(q[-1]>0) if (len(q)-1)%2==0 or s>0 else (q[-1]<0) for q in seq]
        return sum(a!=b for a,b in zip(m,m[1:]))
    return v(-1)-v(1)


def verify_reconstruction(data):
    from fractions import Fraction
    P=[int(a) for a in data['P']]
    irreducible_mod5(P)
    require(count_real_roots(P)==2, 'exactly two real invariant roots')
    require(P[0]!=0, 'parameter does not vanish')
    # Arithmetic in R = Q[X]/(P).
    modulus=[Fraction(a,P[-1]) for a in P[:-1]]
    n=len(modulus)
    def base(c):
        return (Fraction(c),)+(Fraction(0),)*(n-1)
    zero,one=base(0),base(1)
    X=(Fraction(0),Fraction(1))+(Fraction(0),)*(n-2)
    Xinv=tuple(Fraction(-a,P[0]) for a in P[1:])
    def add(a,b):
        return tuple(p+q for p,q in zip(a,b))
    def scale(a,c):
        return tuple(p*c for p in a)
    def mul(a,b):
        m=[Fraction(0)]*(2*n-1)
        for i,p in enumerate(a):
            if p:
                for j,q in enumerate(b):
                    if q:
                        m[i+j]+=p*q
        for k in range(len(m)-1,n-1,-1):
            if m[k]:
                for i,p in enumerate(modulus):
                    m[k-n+i]-=p*m[k]
        return tuple(m[:n])
    reco={k:tuple(Fraction(x) for x in v) for k,v in data['reconstruction'].items()}
    require(set(reco)=={'b4','b6','Z'} and all(len(x)==n for x in reco.values()),'data schema')
    require(mul(X,Xinv)==one, 'exact inverse of the parameter')
    u2=mul(Xinv,Xinv)
    b={2:Xinv,3:Xinv,4:mul(reco['b4'],u2),5:mul(reco['Z'],u2),
       6:mul(reco['b6'],mul(u2,Xinv))}
    require(mul(mul(b[3],b[3]),Xinv)==mul(mul(b[2],b[2]),b[2]), 'parameter gauge')
    f=[one,zero]
    for k in range(2,16):
        h=zero
        for j in range(2,min(6,k)+1):
            h=add(h,scale(mul(b[j],f[k-j]),Fraction(8*j-3*k,3*k)))
        f.append(h)
    require(all(x==zero for x in f[11:15]), 'four exact vanishing conditions')
    require(f[15]!=zero, 'nonzero gap for each algebraic parameter')
    # Since P is irreducible, the displayed nonzero element
    # of Q[X]/(P) stays nonzero under all eight embeddings.
    print('PASS degree-eight reconstruction by rational coefficients and reduction modulo 5')


def main():
    from pathlib import Path
    from json import loads
    verify_trees()
    cert=loads(Path(__file__).with_name('stewart_minimum_polynomial_pairs_certificate.json').read_text())
    verify_reconstruction(cert)


if __name__=='__main__':
    main()
