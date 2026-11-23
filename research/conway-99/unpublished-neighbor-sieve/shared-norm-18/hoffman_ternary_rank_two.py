"""Rank-two ternary Hoffman designs: six color decks, four integer pair contradictions."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from math import comb

A=list(product(range(3),repeat=2))
V=[v for v in A if any(v) and next(x for x in v if x)==1]
pos={v:i for i,v in enumerate(A)}
DECKS=[
 (2,1,4,2,2,2,3,3,3),
 (3,1,3,1,3,2,3,2,4),
 (3,2,2,2,2,2,2,2,5),
 (4,1,2,1,2,3,2,3,4),
 (5,1,1,2,2,2,3,3,3),
 (6,2,2,2,2,2,2,2,2),
]
def dot(v,w):return sum(a*b for a,b in zip(v,w))%3
def neg(v):return tuple(-x%3 for x in v)
def decks():
    perms=[tuple(pos[(dot(x,u),dot(x,v))] for x in A)
           for u,v in product(A,repeat=2) if (u[0]*v[1]-u[1]*v[0])%3]
    assert len(set(perms))==48
    M=[[(0,1,-1)[dot(f,v)] for v in V] for f in V]
    assert all(sum(a*b for a,b in zip(x,y))==3*(x==y) for x in M for y in M)
    orbits=set()
    for j in range(5):
        for high in combinations(range(4),j):
            low=sorted(set(range(4))-set(high))
            for signs in product((1,-1),repeat=len(low)):
                c=[0]*9;c[0]=2+j
                for i,v in enumerate(V):
                    m=20-j-(12 if any(M[f][i]==0 for f in high) else 15)
                    d=sum(e*M[f][i] for e,f in zip(signs,low))
                    assert -m<=d<=m and (m+d)%2==0
                    c[pos[v]]=(m+d)//2;c[pos[neg(v)]]=(m-d)//2
                orbits.add(min(tuple(c[i] for i in p) for p in perms))
    return sorted(orbits)

def model(deck):
    blocks=[B for B in combinations_with_replacement(range(9),4)
            if all(n<=deck[i] for i,n in Counter(B).items())
            and all(sum(A[i][k] for i in B)%3==0 for k in range(2))]
    def rows(k):
        keys=sorted({p for B in blocks for p in combinations(B,k)})
        coeffs=[Counter(combinations(B,k)) for B in blocks]
        from math import prod
        cap=[prod(comb(deck[i],n) for i,n in Counter(p).items()) for p in keys]
        return [[h[p] for h in coeffs] for p in keys],cap
    P,p=rows(2)
    assert sum(p)==comb(22,2)
    T,t=rows(3)
    return blocks, [r+[2*n] for r,n in zip(P,p)], T,t

def rref(M):
    n=len(M[0])-1
    R=[list(map(F,r)) for r in M]; piv=[]
    for j in range(n):
        k=len(piv)
        i=next((i for i in range(k,len(R)) if R[i][j]),None)
        if i is None:continue
        R[i],R[k]=R[k],R[i]
        R[k]=[v/R[k][j] for v in R[k]]
        for i,a in enumerate(R):
            if i!=k and a[j]:
                R[i]=[x-a[j]*y for x,y in zip(a,R[k])]
        piv.append(j)
    assert not any(any(r) for r in R[len(piv):])
    return R[:len(piv)],piv

def check():
    assert decks()==DECKS
    expected={0:(0,F(-11,3)),1:(5,F(-11,3)),3:(0,F(11,3)),4:(6,F(8,3))}
    exact_controls={}
    for i,d in enumerate(DECKS):
        blocks,P,T,t=model(d)
        R,piv=rref(P)
        free=sorted(set(range(len(blocks)))-set(piv))
        if i in expected:
            j,k=expected[i];r=R[piv.index(j)]
            assert r[-1]==k and k.denominator==3 and all(r[h].denominator==1 for h in free)
            print(i,"exclusion:",tuple(A[x] for x in blocks[j]),"= integer +",k)
        else:
            upper=[min([r[-1]//r[j] for r in P if r[j]]+
                       [g//r[j] for r,g in zip(T,t) if r[j]]) for j in range(len(blocks))]
            counts=0
            for x in product(*(range(upper[j]+1) for j in free)):
                z=[F(0)]*len(blocks)
                for j,v in zip(free,x):z[j]=F(v)
                for j,r in zip(piv,R):
                    z[j]=r[-1]-sum(r[h]*v for h,v in zip(free,x))
                    if z[j].denominator!=1 or not 0<=z[j]<=upper[j]:break
                else:
                    if all(sum(x*y for x,y in zip(r,z))<=b for r,b in zip(T,t)):
                        assert all(sum(x*y for x,y in zip(r,z))==r[-1] for r in P)
                        counts+=1
            exact_controls[i]=counts
    assert exact_controls=={2:25,5:15}
    print("Exactly two decks survive integer color pair/triple marginals (25/15 controls, not designs).")
if __name__=="__main__":check()
