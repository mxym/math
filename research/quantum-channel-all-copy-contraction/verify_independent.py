#!/usr/bin/env python3
"""Independent qutrit channel check over the exact Eisenstein integers."""
from collections import defaultdict
from itertools import product
from math import comb
from fractions import Fraction as Q


ZERO=(0,0)
ONE=(1,0)
W=(ONE,(0,1),(-1,-1))


def add(x,y):
    return (x[0]+y[0],x[1]+y[1])


def mul(x,y):
    a,b=x
    c,d=y
    return (a*c-b*d,a*d+b*c-b*d)


def conj(x):
    return (x[0]-x[1],-x[1])


def sumE(seq):
    out=ZERO
    for x in seq:
        out=add(out,x)
    return out


def powprod(seq):
    out=ONE
    for x in seq:
        out=mul(out,x)
    return out


def n2(x):
    return mul(x,conj(x))[0]


F=3
labels=list(product(range(F),repeat=2))
zero=(0,0)
others=labels[1:]
neg=lambda v: tuple(-x%F for x in v)
# Physical Kraus operators |f(i)><i|: measure the basis and map
# 0,1->0 and 2->1. D_v=omega^(ab/2) X^a Z^b; input/output
# with a!=0 are respectively killed/absent. T scaled by 3.
f=(0,0,1)
T={}
for b,j in product(range(F),repeat=2):
    v=sumE(W[(b*i-j*f[i])%F] for i in range(F))
    if v!=ZERO: T[(0,j),(0,b)]=v
A={(a,b):v for (a,b),v in T.items() if a!=zero and b!=zero}
assert sum(n2(v) for v in T.values())==27
assert sum(n2(v) for v in A.values())==12
u=Q(12,9*8)
assert u==Q(1,6)
assert sumE(A.get((j,j),ZERO) for j in others)==ZERO

# Each symplectic matrix maps D_v to D_Mv; each character phase
# multiplies D_v by omega^(t.v). Weyl phases are exact on all 216 cases.
sl=[(a,b,c,d) for a,b,c,d in product(range(F),repeat=4) if (a*d-b*c)%F==1]
assert len(sl)==24
maps=[]
Ts=[]
As=[]
for a,b,c,d in sl:
    act={v:((a*v[0]+b*v[1])%F,(c*v[0]+d*v[1])%F) for v in labels}
    for s,t in labels:
        phase={v:(s*v[0]+t*v[1])%F for v in labels}
        R={(x,y):mul(T[act[x],act[y]],W[(phase[y]-phase[x])%F])
           for x,y in product(labels,repeat=2) if (act[x],act[y]) in T}
        Ts.append(R)
        As.append({(x,y):v for (x,y),v in R.items() if x!=zero and y!=zero})
        maps.append((act,phase))
assert len(Ts)==216
# Irreducible adjoint ensemble verified directly via character cancellation.
for x,y in product(others,repeat=2):
    test=defaultdict(lambda:ZERO)
    for act,p in maps:
        rev={w:v for v,w in act.items()}
        i,j=rev[x],rev[y]
        test[i,j]=add(test[i,j],W[(p[j]-p[i])%F])
    assert all(test[i,j]==((27 if x==y and i==j else 0),0)
               for i,j in product(others,repeat=2))

for kind in (False,True):
    for x,y in product(others,repeat=2):
        value=sumE(mul(conj(M.get((z,x) if not kind else (x,z),ZERO)),
                       M.get((z,y) if not kind else (y,z),ZERO))
                   for M in As for z in others)
        assert value==((324 if x==y else 0),0)  # 216 * 9 * u
print("qutrit 216 Weyl-symplectic actions: 64 covariance matrix units; both Gram isotropies exactly u=1/6")

# All entries of the full 2/3-copy averaged maps are obtained by
# independently tensoring the uncompressed T channels. Then compare
# each diagonal subblock to the compressed moment, checking the zeros.
def moments(mats,k):
    out=defaultdict(lambda:ZERO)
    for L in mats:
        for ls in product(L.items(),repeat=k):
            x=tuple(entry[0][0] for entry in ls)
            y=tuple(entry[0][1] for entry in ls)
            out[x,y]=add(out[x,y],powprod(entry[1] for entry in ls))
    return {k:v for k,v in out.items() if v!=ZERO}


mom={k:moments(As,k) for k in (1,2,3)}
for k in (2,3):
    full=moments(Ts,k)
    cnt=0
    for (x,y),value in full.items():
        sx=[i for i,v in enumerate(x) if v!=zero]
        sy=[i for i,v in enumerate(y) if v!=zero]
        assert set(sy)<=set(sx)
        if sx==sy:
            r=len(sx)
            if r==0:
                assert value==(216*3**k,0)
            else:
                tx,ty=tuple(x[i] for i in sx),tuple(y[i] for i in sy)
                w=mom[r][tx,ty]
                assert value==tuple(v*3**(k-r) for v in w)
            cnt+=1
    assert cnt==1+sum(comb(k,j)*len(mom[j]) for j in range(1,k+1))
    print(f"qutrit exact full moment r={k}: {len(full)} nonzero entries, {cnt} diagonal-sector entries")

# In the complex Weyl basis the invariant bilinear vector is
# sum_{v!=0} e_v tensor e_{-v}. Its checked eigenvalue is u.
for x in product(others,repeat=2):
    got=sumE(mom[2].get((x,(v,neg(v))),ZERO) for v in others)
    assert got==((324 if x[1]==neg(x[0]) else 0),0)
print("qutrit complex Weyl basis: S2 canonical-vector eigenvalue u exactly")

# Direct traceless diagonal test for HS expansion. This CPTP channel
# sends diag(1,1,-2) to diag(2,-2,0), norm^2 ratio 4/3.
v=(1,1,-2)
image=tuple(sum(v[i] for i in range(F) if f[i]==j) for j in range(F))
assert Q(sum(x*x for x in image),sum(x*x for x in v))==Q(4,3)
assert sum(image)==0
print("nonunital control: one-step squared Hilbert-Schmidt norm ratio 4/3, so pointwise contraction would be false")
assert tuple(f[f[i]] for i in range(F))==(0,0,0)
print("the same untwirled channel squares to replacement: covariance beta<1 is sufficient, not necessary")
