#!/usr/bin/env python3
"""Small exact forward-convolution identity checks, no external input or samples."""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from math import prod
from random import Random


def add(a,b,p):
    return tuple((x+y)%p for x,y in zip(a,b))


def scale(k,a,p):
    return tuple(k*x%p for x in a)


def dot(a,b,p):
    return sum(x*y for x,y in zip(a,b))%p


def span(rows,p,d):
    a=[list(v) for v in rows if any(v)]
    r=0
    piv=[]
    for j in range(d):
        i=next((k for k in range(r,len(a)) if a[k][j]),None)
        if i is None:
            continue
        a[r],a[i]=a[i],a[r]
        a[r]=list(scale(pow(a[r][j],-1,p),a[r],p))
        for i in range(len(a)):
            if i != r and a[i][j]:
                a[i]=list(add(a[i],scale(-a[i][j],a[r],p),p))
        piv.append(j)
        r+=1
    return tuple(piv),tuple(tuple(x) for x in a[:r])


def proj(a,sp,p):
    pivs,rows=sp
    for j,v in zip(pivs,rows):
        a=add(a,scale(-a[j],v,p),p)
    return tuple(v for j,v in enumerate(a) if j not in pivs)


def line(v,p):
    return scale(pow(next(a for a in v if a),-1,p),v,p)


def sig(A,steps,p,check=True):
    sp=span([v for v,l in steps if l%p==0],p,len(A))
    qA=proj(A,sp,p)
    active=[(proj(v,sp,p),l) for v,l in steps]
    active=[(v,l) for v,l in active if any(v)]
    assert all(l%p for _,l in active)
    D={}
    for v,l in active:
        v0=line(v,p)
        D[v0]=D.get(v0,1)*l
    D={v:t for v,t in D.items() if t!=1}
    if p==2:
        return sp,D,qA
    B=Counter()
    center=qA
    for v,l in active:
        B[scale(l,v,p)]+=1
        B[v]-=1
        center=add(center,scale((l-1)*pow(2,-1,p),v,p),p)
    pp=Counter()
    for v,c in B.items():
        rep=min(v,scale(-1,v,p))
        pp[rep]+=c
    if check:
        # Independently check the group-wise multiplicative/forced parity identity.
        direct={}
        for v,c in B.items():
            if not c:
                continue
            v0=line(v,p)
            t=next(a for a in v if a)
            direct[v0]=direct.get(v0,1)*pow(t,c,p)%p
        assert {v:a for v,a in direct.items() if a!=1}=={
                v:l%p for v,l in D.items() if l%p!=1}
    return sp,D,{v:c for v,c in pp.items() if c},center


def pmf(A,steps,p):
    dist={A:1}
    for v,L in steps:
        n=p if any(v) else 1
        h,r=divmod(L,n)
        shifts=[(scale(j,v,p),h+(j<r)) for j in range(n) if h+(j<r)]
        P=Counter()
        for a,c in dist.items():
            for b,e in shifts:
                P[add(a,b,p)] += c*e
        dist=P
    return dist,sum(dist.values())


def eq(p1,p2):
    a,x=p1
    b,y=p2
    return all(a.get(k,0)*y == b.get(k,0)*x for k in a.keys()|b.keys())


def random_cases():
    rng=Random(8472)
    checks=matches=uniform=0
    for p,d in ((2,1),(2,2),(2,5),(3,1),(3,2),(3,4),(5,2),(5,3),(7,2)):
        def v():
            return tuple(rng.randrange(p) for _ in range(d))
        for i in range(132):
            A=v()
            ls=[(v(),rng.randrange(1,3*p+1)) for _ in range(rng.randrange(0,7))]
            if i%6==0:
                B=A
                ds=[]
                for w,l in reversed(ls):
                    B=add(B,scale(l-1,w,p),p)
                    ds.append((scale(-1,w,p),l))
            elif i%6==1:
                B=A
                ds=[]
                for w,l in ls:
                    m=rng.randrange(1,p+2)
                    ds.extend(((w,m),(scale(m,w,p),l)))
                ls=[(w,l*m) for (w,l),(_,m) in zip(ls,ds[::2])]
            elif i%6==2:
                u,w=v(),v()
                ls=ls+[(u,p),(w,2*p)]
                B=add(A,add(u,w,p),p)
                ds=ls[:-2]+[(u,p),(add(w,u,p),p),(scale(3,w,p),p+1)]
                # The final factor is absorbed by the common uniform span.
            elif i%6==3:
                B=add(A,v(),p)
                ds=ls
            elif i%6==4:
                B=v()
                ds=[(v(),rng.randrange(1,3*p+1)) for _ in range(rng.randrange(0,7))]
            else:
                B=A
                ds=ls+[(v(),1)]
            lhs=eq(pmf(A,ls,p),pmf(B,ds,p))
            s1,s2=sig(A,ls,p),sig(B,ds,p)
            assert lhs==(s1==s2)
            checks+=1
            matches+=lhs
            uniform+=len(s1[0][0])==d
    return checks,matches,uniform


def projective():
    count=0
    for p,d in ((2,3),(3,2),(3,3),(5,2),(5,3),(7,2)):
        P=sorted({line(a,p) for a in product(range(p),repeat=d) if any(a)})
        D=[[dot(a,b,p)!=0 for b in P] for a in P]
        for i,a in enumerate(P):
            for j,b in enumerate(P):
                k=sum(row[i] and row[j] for row in D)
                assert k==(p**(d-1) if i==j else (p-1)*p**(d-2))
                count+=1
    return count


def polycoef(pairs,k):
    out=F(0)
    for x,v in pairs:
        coeff=[F(1)]
        den=F(1)
        for y,w in pairs:
            if x==y:
                continue
            u=[F(0)]*(len(coeff)+1)
            for i,c in enumerate(coeff):
                u[i]-=y*c
                u[i+1]+=c
            coeff=u
            den*=x-y
        out+=v*coeff[k]/den
    return out


def matching_checks():
    trials=queries=0
    for mask in range(512):
        E=[(i,j) for i,j in product(range(3),repeat=2)
           if mask>>(3*i+j)&1]
        if len(E)<3:
            continue
        V=[tuple(int(k==i or k==j+3) for k in range(6)) for i,j in E]
        ans=sum(all((i,j) in E for i,j in enumerate(w))
                for w in permutations(range(3)))
        pairs=[]
        N=len(E)
        for k in range(1,N+2):
            v,_=pmf((0,)*6,[(w,2*k+1) for w in V],2)
            pairs.append((F(k,k+1), F(v.get((1,)*6,0),(k+1)**N)))
            queries+=1
        assert polycoef(pairs,3)==ans
        trials+=1
    return trials,queries


def huge():
    rng=Random(922)
    p=2**61-1
    d=69
    V=[tuple(rng.randrange(p) for _ in range(d)) for _ in range(31)]
    A=V[0]
    B=A
    S=[(v,1+p*i+i) for i,v in enumerate(V)]
    T=[]
    for v,l in reversed(S):
        B=add(B,scale(l-1,v,p),p)
        T.append((scale(-1,v,p),l))
    assert sig(A,S,p)==sig(B,T,p)
    assert sig(A,S,p)!=sig(add(B,V[1],p),T,p)
    return 2


if __name__=="__main__":
    print("PASS: exact pairs/equalities/uniforms, incidence Gram, matchings/queries, large signatures",
          *random_cases(),projective(),*matching_checks(),huge())
