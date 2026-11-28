#!/usr/bin/env python3
"""Exact path algebra from two independent tensor representations."""
from fractions import Fraction as F
from itertools import permutations, combinations, product
from math import factorial, prod
from collections import defaultdict, Counter
from random import Random

Z=(F(0),F(0))
O=(F(1),F(0))


def add(x,y):
    return (x[0]+y[0],x[1]+y[1])


def neg(x):
    return (-x[0],-x[1])


def mul(x,y):
    a,b=x
    c,d=y
    return (a*c-b*d,a*d+b*c)


def conj(x):
    return (x[0],-x[1])


def scale(a,x):
    return (a*x[0],a*x[1])


def abs2(x):
    return x[0]*x[0]+x[1]*x[1]


def gp(xs):
    total=O
    for x in xs:
        total=mul(total,x)
    return total


def gs(xs):
    total=Z
    for x in xs:
        total=add(total,x)
    return total


def dot(x,y):
    return gs(mul(conj(a),b) for a,b in zip(x,y))


def gram(rows):
    return tuple(tuple(dot(x,y) for y in rows) for x in rows)


def permanent(m):
    return gs(gp(m[i][j] for i,j in enumerate(p)) for p in permutations(range(len(m))))


def table(rows,d):
    # Product of commuting linear polynomials, coefficients indexed by monomial.
    out={(0,)*d:O}
    for v in rows:
        a=defaultdict(lambda:Z)
        for k,z in out.items():
            for j,c in enumerate(v):
                if c!=Z:
                    q=list(k)
                    q[j]+=1
                    q=tuple(q)
                    a[q]=add(a[q],mul(z,c))
        out=a
    return out


def occ_dot(x,y):
    return gs(scale(prod(factorial(j) for j in k),mul(conj(v),y.get(k,Z))) for k,v in x.items())


def lower(P,w):
    out=defaultdict(lambda:Z)
    for k,z in P.items():
        for j,r in enumerate(k):
            if r:
                c=list(k)
                c[j]-=1
                c=tuple(c)
                out[c]=add(out[c],scale(r,mul(z,conj(w[j]))))
    return out


def basis(d):
    return [tuple(O if i==j else Z for i in range(d)) for j in range(d)]


def rot(d,i,j,a,b,c,imag):
    v=[Z]*d
    v[i]=(F(a,c),F(0))
    v[j]=(F(0),F(b,c)) if imag else (F(b,c),F(0))
    return tuple(v)


def det(m):
    return gs(scale((-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p))),
                    gp(m[i][j] for i,j in enumerate(p)))
              for p in permutations(range(len(m))))


def shifted_psd(m,c):
    for r in range(1,len(m)+1):
        for a in combinations(range(len(m)),r):
            x=tuple(tuple(add(m[i][j],(-c,F(0))) if i==j else m[i][j] for j in a) for i in a)
            re,im=det(x)
            if im or re<0:
                return False
    return True


def path_checks():
    rng=Random(115)
    paths=near=0
    for d in range(2,6):
        b=basis(d)
        p=b+[rot(d,i,j,3,4,5,k) for i,j in permutations(range(d),2) for k in (False,True)]
        for t in range(2,min(d+1,5)+1):
            trials=[tuple(rng.choice(p) for _ in range(t)) for j in range(48)]
            if t<=d:
                trials+=[tuple(rot(d,i,(i+1)%d,255,32,257,im) for i in J)
                         for J in combinations(range(d),t) for im in (False,True)]
                trials+=[tuple(b[i] for i in J) for J in combinations(range(d),t)]
            for vs in trials:
                assert all(dot(v,v)==O for v in vs)
                G=gram(vs)
                P,im=permanent(G)
                assert im==0
                C=table(vs,d)
                assert occ_dot(C,C)==(P,0)
                inherited=table(vs[:-1],d)
                z=lower(inherited,vs[-1])
                old=occ_dot(inherited,inherited)
                assert add(old,occ_dot(z,z))==(P,0)
                if P<=F(65,64):
                    S=sum(abs2(G[i][j]) for i in range(t) for j in range(i+1,t))
                    assert S<=F(3,2)*(P-1)<=F(3,128)
                    assert shifted_psd(G,F(3,4))
                    holes=[table(vs[:i]+vs[i+1:],d) for i in range(t)]
                    H=tuple(tuple(occ_dot(h0,h1) for h1 in holes) for h0 in holes)
                    assert shifted_psd(H,F(45,64))
                    near+=1
                paths+=1
    # Wrongly dropping complex conjugation in the B matrix is detectable.
    u=w=basis(2)[0]
    v=tuple(mul((0,1),z) for z in u)
    h=gram((v,u))
    t=tuple(dot(x,w) for x in (u,v))
    delta=permanent(gram((u,v,w)))[0]-permanent(gram((u,v)))[0]
    form=lambda H: gs(gp((conj(t[i]),H[i][j],t[j])) for i in range(2) for j in range(2))
    assert form(tuple(tuple(conj(hh) for hh in row) for row in h))==(delta,0)
    assert form(h)!=(delta,0)
    return paths,near


def one_hole_compression():
    rng=Random(1207)
    entries=0
    for r in range(1,8):
        for rep in range(20):
            L=[[Z for j in range(r)] for i in range(r)]
            for i in range(r):
                L[i][i]=(F(rng.randrange(-4,5)),0)
                for j in range(i):
                    L[i][j]=(F(rng.randrange(-4,5)),F(rng.randrange(-4,5)))
                    L[j][i]=conj(L[i][j])
            holes=[tuple(int(j!=i) for j in range(r)) for i in range(r)]
            for i,x in enumerate(holes):
                for j,y in enumerate(holes):
                    actual=Z
                    for a,b in product(range(r),repeat=2):
                        if not y[b]:
                            continue
                        k=list(y)
                        k[b]-=1
                        k[a]+=1
                        if tuple(k)==x:
                            # Input and output square-root factors multiply to 1
                            # whenever both are single-occupancy states.
                            assert y[b]*(k[a])==1
                            actual=add(actual,L[a][b])
                    expected=(sum(L[k][k][0] for k in range(r) if k!=i),F(0)) if i==j else L[j][i]
                    assert actual==expected
                    entries+=1
    return entries


def occupancy_types(n,hi=None):
    if n==0:
        yield ()
    else:
        for a in range(1,min(hi or n,n)+1):
            for z in occupancy_types(n-a,a):
                yield (a,)+z


def check_basis():
    cases=0
    for t in range(2,11):
        for d in sorted({1,2,3,4,5,6,10,13,64*t*t,80*t*t,128*t*t}):
            A=prod(F(d+j,d) for j in range(t))
            deficit=F(0)
            total=0
            for occ in occupancy_types(t):
                if len(occ)>d:
                    continue
                falling=prod(d-j for j in range(len(occ)))
                per=prod(factorial(j) for j in occ)
                ways=falling//prod(factorial(z) for z in Counter(occ).values())
                ways*=factorial(t)//per
                total+=ways
                deficit+=ways*max(F(0),1-F(per,1)/A)
            assert total==d**t
            observed=deficit/d**t
            if d>=64*t*t:
                assert A-1<=F(1,64)
                assert observed==(1-1/A)*prod(F(d-j,d) for j in range(t))
            if t==3 and d in (2,3,4,5):
                assert observed=={2:F(1,4),3:F(17,90),4:F(7,40),5:F(34,175)}[d]
            cases+=1
    return cases


if __name__ == "__main__":
    a,b=path_checks()
    print(f"Exact Gaussian-rational paths: {a} Gram/occupation recursions, {b} low-permanent spectral checks")
    print(f"One-hole compression: {one_hole_compression()} occupation matrix coefficients, complex transpose control PASS")
    print(f"Repeated basis: {check_basis()} occupancy histograms, birthday finite formula and small-d baselines PASS")
