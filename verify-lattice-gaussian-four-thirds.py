#!/usr/bin/env python3
"""Exact finite Gram and polynomial checks for the universal four-thirds proof."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import isqrt

def add(x, y, c=1):
    return tuple(a+c*b for a,b in zip(x,y))

def sc(x, c):
    return tuple(c*a for a in x)

def parity(x):
    return tuple(a % 2 for a in x)

def inverse(g):
    d = len(g)
    a = [[F(v) for v in row]+[F(i==j) for j in range(d)] for i,row in enumerate(g)]
    for k in range(d):
        pivot = a[k][k]
        assert pivot > 0
        a[k] = [v/pivot for v in a[k]]
        for i in range(d):
            if i != k:
                a[i] = list(add(a[i],a[k],-a[i][k]))
    return [row[d:] for row in a]

def deriv(f):
    # Exact derivative at 0 for every polynomial of degree <= 4.
    return (8*(f(1)-f(-1))-(f(2)-f(-2)))/12

def run(g):
    d=len(g)
    gi=inverse(g)
    z=(0,)*d
    basis=tuple(tuple(int(i==j) for i in range(d)) for j in range(d))

    @lru_cache(maxsize=32768)
    def gram_times(y):
        return tuple(sum(a*b for a,b in zip(row,y) if a and b) for row in g)

    def dot(x,y):
        return sum(a*b for a,b in zip(x,gram_times(y)) if a and b)

    @lru_cache(None)
    def qI(x):
        return dot(x,x)

    def q(x):
        return qI(x) if all(isinstance(i,int) for i in x) else dot(x,x)

    def box(R2,center=z):
        bounds=[]
        for i in range(d):
            r=gi[i][i]*R2
            m=isqrt(r.numerator//r.denominator)+2
            c=int(center[i]//1)
            bounds.append(range(c-m,c+m+1))
        return product(*bounds)

    # Coefficient Cauchy bounds from the inverse Gram matrix make these
    # finite searches exhaustive in their stated norm balls.
    reps=list(product((0,1),repeat=d))
    B0=max(q(u) for u in reps)
    mu={}
    mins={}
    for u in box(B0):
        s=parity(u); a=q(u)
        if s not in mu or a<mu[s]:
            mu[s]=a; mins[s]=[u]
        elif a==mu[s]:
            mins[s].append(u)
    assert len(mu)==2**d
    for a,b in product(reps,repeat=2):
        assert mu[parity(add(a,b))]<=mu[a]+mu[b]

    # If |x dot e_i| <= G_ii/2, then ||x||^2 <= R2.
    R2=sum(abs(gi[i][j])*g[i][i]*g[j][j] for i in range(d) for j in range(d))/4
    Fset=sorted({v for v in box(4*R2) if v!=z and q(v)<=4*R2} |
                set(basis) | {sc(v,-1) for v in basis})
    lows=[]
    # The basis inequalities imply simple coefficient bounds in 4V.
    w=[int(2*sum(abs(gi[i][j])*g[j][j] for j in range(d)))+1 for i in range(d)]
    for j in product(*(range(-i,i+1) for i in w)):
        if j==z or q(j)>16*R2:
            continue
        if all(dot(j,v)<2*q(v) for v in Fset):
            lows.append(j)

    lowcols=[]
    for j in lows:
        shortest=next(r for r in mins[parity(j)] if r!=j)
        end=add(j,shortest,-1)
        assert end!=z and parity(end)==z
        h0=sc(shortest,-1)
        a,v=min((F(2*q(v)-dot(j,v),dot(h0,v)),v)
                for v in Fset if dot(h0,v)>0)
        assert 0<a<=1
        h=sc(h0,a)
        alpha=add(j,h)
        assert dot(alpha,v)==2*q(v) and q(h)<=mu[parity(j)]
        assert all(dot(alpha,u)<=2*q(u) for u in Fset)
        # The weighted score differences are affine on the segment.
        # All contacts at alpha are contacts at the terminal point end,
        # hence exactly the translates of minimal parity representatives
        # that also tie at alpha. Cross-check the exhaustive local box
        # independently in the smaller Gram examples.
        hits=[]
        for rr in mins.values():
            for r in rr:
                i=add(end,r)
                B=q(add(i,alpha,-1))-q(h)+mu[parity(j)]-mu[parity(i)]
                assert B>=0
                if B==0:
                    assert abs(dot(add(i,alpha,-1),v))<=q(v)
                    hits.append(i)
        assert j in hits
        if d<=3:
            all_hits=[]
            for i in box(q(h)+max(mu.values()),alpha):
                B=q(add(i,alpha,-1))-q(h)+mu[parity(j)]-mu[parity(i)]
                assert B>=0
                if B==0:
                    all_hits.append(i)
            assert set(all_hits)==set(hits)
        lowcols.append((j,v,alpha,h,hits))
    e=F(1,16)
    while any(q(v)-2*e*dot(h,v)<=0 or
              any(3*q(v)-2*dot(add(i,alpha,-1),v)
                  +e*(2*dot(add(i,alpha,-1),h)+2*q(h)-6*dot(h,v))<=0
                  for i in hits) for j,v,alpha,h,hits in lowcols):
        e/=2
    k=e/2
    while any(any(
            (i!=j and 2*e*dot(add(i,j,-1),h)+k*(mu[parity(i)]-mu[parity(j)])<=0)
            or 3*q(v)-2*dot(add(i,alpha,-1),v)
               +e*(2*dot(add(i,alpha,-1),h)+2*q(h)-6*dot(h,v))
               +k*(mu[parity(i)]-mu[parity(j)])<=0
            for i in hits) for j,v,alpha,h,hits in lowcols):
        k/=2

    def ex(i,j,v,alpha,h,t,companion):
        a=add(alpha,h,-e*t)
        off=q(add(a,j,-1))
        damp=0
        if companion:
            A=4-t
            damp=(A-1)*(2*dot(a,v)-A*q(v))
            a=add(a,v,-A)
        return q(add(i,a,-1))-off+(1-k*t)*(mu[parity(j)]-mu[parity(i)])+damp

    lp=lc=hc=0
    for j,v,alpha,h,hits in lowcols:
        for i in hits:
            def p(t): return ex(i,j,v,alpha,h,t,False)
            assert p(0)==0
            expect=2*e*dot(add(i,j,-1),h)+k*(mu[parity(i)]-mu[parity(j)])
            assert deriv(p)==expect and (i==j or expect>0)
            lp+=int(i!=j)
            b=add(i,v,-4)
            def c(t): return ex(b,j,v,alpha,h,t,True)
            r=add(i,alpha,-1)
            expect=3*q(v)-2*dot(r,v)+e*(2*dot(r,h)+2*q(h)-6*dot(h,v))
            expect+=k*(mu[parity(i)]-mu[parity(j)])
            assert c(0)==0 and deriv(c)==expect>0
            lc+=1
        assert q(sc(h,1-e*F(1,4))) <= (1-k*F(1,4))*mu[parity(j)]

    offsets=[r for r in box(max(mu.values())) if q(r)<=max(mu.values())]
    for j in product(range(-2,3),repeat=d):
        if j==z:
            continue
        h0,v=max((2*dot(j,v)-4*q(v),v) for v in Fset)
        if h0!=0:
            continue
        for r in offsets:
            i=add(add(j,r),v,-4)
            if i==z or q(r)!=mu[parity(i)]-mu[parity(j)]:
                continue
            assert abs(dot(r,v))<=q(v)
            def co(t): return ex(i,j,v,j,z,t,True)
            expect=3*q(v)-2*dot(r,v)+k*q(r)
            assert co(0)==0 and deriv(co)==expect>0
            hc+=1
    return len(lows),lp,lc,hc

SHAPES = [
    ((1,),),
    ((1,F(1,3)),(F(1,3),2)),
    ((1,F(1,2)),(F(1,2),1)),
    ((1,0),(0,3)),
    ((2,1,1),(1,2,1),(1,1,2)),
    ((4,-1,1),(-1,3,1),(1,1,5)),
    ((4,1,0,1),(1,4,1,0),(0,1,4,1),(1,0,1,4)),
]
# Use exact arithmetic throughout, including all breakpoint quotients.
totals=(0,0,0,0)
for g0 in SHAPES:
    result=run(g0)
    totals=add(totals,result)
    print("Gram dimension",len(g0),":",*result)
assert all(totals)
print("PASS: low columns, low-primary contacts, low-companion contacts, high-companion contacts =",totals)
