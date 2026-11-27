#!/usr/bin/env python3
"""Exact dual, branch geometry, and independent local branch sum."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product

S=((1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1))
pairs=list(combinations(range(3),2))

def norm2(v):
    return sum(x*x for x in v)

def certificate(r):
    """Atoms and witness numerators with common radical denominator."""
    a,b,c=r
    if a>=b+c:
        G=a*a+(b+c)**2
        w=(a,b+c,b+c)
        if b+c:
            atoms=[(F(b,b+c),(a,b+c,0),2),(F(c,b+c),(a,0,b+c),1)]
        else:
            atoms=[(F(1),(a,0,0),2)]
    else:
        L=a+b+c
        G=F(L**2,2)
        w=[F(L,2)]*3
        atoms=[]
        for i,j in pairs:
            k=3-i-j
            u=[F(0)]*3
            u[i]=u[j]=F(L,2)
            atoms.append((F(r[i]+r[j]-r[k],L),u,k))
    return G,w,atoms

def branches(atoms,sign):
    # For fixed omitted sign there is one pair, with oppositely directed axes.
    out=[]
    for p,u,k in atoms:
        if p==0: continue
        assert u[k]==0
        for eps in (-1,1):
            a,b=[i for i,s in enumerate(S) if s[k]==eps]
            ua=tuple(u[i]*sign[i]*S[a][i] for i in range(3))
            ub=tuple(u[i]*sign[i]*S[b][i] for i in range(3))
            assert ua==tuple(-t for t in ub)
            out.append((p/2,a,b,ua))
    assert sum(p for p,*_ in out)==1
    return out

def singlet_law(A,B,G):
    out=[[F(0)]*4 for _ in range(4)]
    for p,a,aa,u in A:
        for q,b,bb,v in B:
            cross=F(sum(x*y for x,y in zip(u,v)),G)
            for i,m in ((a,1),(aa,-1)):
                for j,n in ((b,1),(bb,-1)):
                    out[i][j]+=p*q*(1-m*n*cross)/4
    return out

profiles=mixed=dominant=degenerate=middles=negative=0
for raw in combinations_with_replacement(range(9),3):
    if raw==(0,0,0): continue
    r=raw[::-1]
    G,w,atoms=certificate(r)
    profiles+=1
    dominant+=r[0]>=r[1]+r[2]
    degenerate+=r[2]==0
    middles+=r[0]==r[1]+r[2]
    assert max(w[i]**2+w[j]**2 for i,j in pairs)==G
    assert sum(x*y for x,y in zip(w,r))==G
    assert sum(p for p,*_ in atoms)==1 and all(p>=0 for p,*_ in atoms)
    assert all(norm2(u)==G for p,u,k in atoms)
    assert tuple(sum(p*u[i] for p,u,k in atoms) for i in range(3))==r
    left=branches(atoms,(1,1,1))
    for sign in product([-1,1],repeat=3):
        right=branches(atoms,tuple(-t for t in sign))
        P=singlet_law(left,right,G)
        C=[F(sign[i]*r[i]**2,G) for i in range(3)]
        for a,b in product(range(4),repeat=2):
            want=(1+sum(C[i]*S[a][i]*S[b][i] for i in range(3)))/16
            assert P[a][b]==want and want>=0
        assert all(sum(x)==F(1,4) for x in P)
        assert all(sum(x)==F(1,4) for x in zip(*P))
        mixed+=1
    if r[2]:
        unscaled=norm2(r)
        vcrit=F(unscaled,G)
        assert vcrit<1
        v=(1+vcrit)/2
        # True noisy-singlet distribution, but the PS dual strictly excludes it.
        C=[-v*F(x*x,unscaled) for x in r]
        assert all(1+sum(x*y for x,y in zip(C,a))>0 for a in S)
        assert v*G/unscaled>1
        negative+=1

assert singlet_law([(F(1,2),0,1,(0,0,0)),(F(1,2),2,3,(0,0,0))],
                   [(F(1,2),0,1,(0,0,0)),(F(1,2),2,3,(0,0,0))],1) == [[F(1,16)]*4]*4
assert certificate((1,1,1))[0] == F(9,2)
assert F(norm2((1,1,1)),certificate((1,1,1))[0]) == F(2,3)
assert certificate((5,2,1))[0] == 34
print(f"exact dual and atomic means: {profiles} profiles, {dominant} dominant, {middles} transition, {degenerate} zero-coordinate PASS")
print(f"exact independent two-party branch sums: {mixed} signed tables; uniform null case PASS")
print(f"exact above-threshold negative controls: {negative} valid tables excluded")

# One-PS exact KKT and factor squares for d_i=m_i^3. In the
# dominant branch use rational hypotenuse of the last two m's;
# in the balanced branch retain the common radical symbolically.
from math import isqrt
one_balanced=one_dominant=one_transition=0
for raw in combinations_with_replacement(range(1,14),3):
    m=raw[::-1]
    AA=m[0]**2
    BB=m[1]**2+m[2]**2
    q=[x**3 for x in m]
    if AA<=BB:
        V=sum(x*x for x in m)
        Gsquare=F(V**3,2)
        aa=[2*F(x*x,V)**2 for x in m]
        bb=[F(x*x,V) for x in m]
        w2=[F(1,2)]*3
        # a_i=sqrt(2)*alpha_i and g(a)=sum(alpha_i)=1
        # on the balanced branch. The three edge weights are
        # alpha_i+alpha_j-alpha_k, and their means recover a.
        alpha=[F(x*x,V) for x in m]
        assert sum(alpha)==1 and max(alpha)<=F(1,2)
        p={(i,j):alpha[i]+alpha[j]-alpha[3-i-j] for i,j in pairs}
        assert sum(p.values())==1 and min(p.values())>=0
        assert [sum(weight/2 for pair,weight in p.items() if i in pair)
                for i in range(3)]==alpha
        one_balanced+=1
    else:
        h=isqrt(BB)
        if h*h!=BB: continue
        G=q[0]+h**3
        Gsquare=G*G
        aa=[F(q[0],G),F(m[1]**4,h*G),F(m[2]**4,h*G)]
        bb=[F(q[0],G),F(h*m[1]**2,G),F(h*m[2]**2,G)]
        w2=[F(q[0],G),F(h**3,G),F(h**3,G)]
        # a_2+a_3 = h^(3/2)/sqrt(G) and g(a)^2 = 1.
        assert F((m[1]**2+m[2]**2)**2,h*G)==F(h**3,G)
        assert aa[0]+F(h**3,G)==1
        one_dominant+=1
    one_transition+=AA==BB
    assert max(w2[i]+w2[j] for i,j in pairs)==1
    assert sum(bb)==1
    assert all(aa[i]*bb[i]==F(q[i]**2,Gsquare) for i in range(3))
    assert F(sum(q)**2,Gsquare)<1  # the visibility-one case is excluded
assert one_balanced>0 and one_dominant>0 and one_transition>0
print(f"exact one-PS boundary factors: {one_balanced} balanced, {one_dominant} dominant, {one_transition} transition PASS")
