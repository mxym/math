#!/usr/bin/env python3
"""Independent incidence enumeration in F2[a]/(a^4+a+1)."""
from itertools import combinations, product

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

K=tuple(range(16))

def mul(x,y):
    ans=0
    while y:
        if y&1:
            ans^=x
        y>>=1
        x<<=1
        if x&16:
            x^=19
    return ans

M=[[mul(x,y) for y in K] for x in K]
I=[0]+[M[x].index(1) for x in K[1:]]
F=tuple(x for x in K if M[M[x][x]][M[x][x]]==x)
U=tuple(x for x in K if M[M[M[x][x]][M[x][x]]][x]==1)
assert len(F)==4 and len(U)==5

def norm(v):
    scale=I[next(x for x in v if x)]
    return tuple(M[scale][x] for x in v)

def cross(a,b):
    return tuple(M[a[i]][b[j]]^M[a[j]][b[i]] for i,j in ((1,2),(2,0),(0,1)))

def dot(a,b):
    return M[a[0]][b[0]]^M[a[1]][b[1]]^M[a[2]][b[2]]

def subline(P,Q,R):
    i,j=next((i,j) for i,j in ((0,1),(0,2),(1,2))
             if M[P[i]][Q[j]]!=M[P[j]][Q[i]])
    a=M[R[i]][Q[j]]^M[R[j]][Q[i]]
    b=M[P[i]][R[j]]^M[P[j]][R[i]]
    assert a and b
    S={norm(tuple(M[a][x]^M[M[b][t]][y] for x,y in zip(P,Q))) for t in F}
    S.add(Q)
    assert len(S)==5 and P in S and Q in S and R in S
    return frozenset(S)

def compatible(base, first,second):
    l,A=first
    m,B=second
    if l==m or any(dot(l,b)==0 for b in B) or any(dot(m,a)==0 for a in A):
        return False
    return all(dot(norm(cross(a,b)),c)!=0 for a,b,c in product(A,B,base))

def main():
    P=[(1,y,z) for y,z in product(K,repeat=2)]+[(0,1,z) for z in K]+[(0,0,1)]
    A={(1,0,x) for x in U}
    B={(0,1,x) for x in U}
    base=A|B
    forbidden={norm(cross(a,b)) for a,b in product(A,B)}
    eligible={p for p in P if p[0] and p[1] and
              all(dot(p,l) for l in forbidden)}
    direct={(1,t,z) for t in U for z in U}|{(1,t,0) for t in K[1:] if t not in U}
    assert eligible==direct and len(eligible)==35
    candidates=set()
    for l in P:
        if any(dot(l,p)==0 for p in base):
            continue
        hits=sorted(p for p in eligible if dot(l,p)==0)
        for a,b,c in combinations(hits,3):
            D=subline(a,b,c)
            if D<=eligible:
                candidates.add((l,D))
    supports={l for l,S in candidates}
    assert len(P)==273 and len(candidates)==7 and len(supports)==6
    witness=((1,1,0),frozenset((1,1,s) for s in U))
    assert witness in candidates
    good=sum(compatible(base,a,b) for a,b in combinations(candidates,2))
    assert good==0
    assert not compatible(base,witness,witness)
    print("Geometry: 273 projective points; 35 eligible; 7 sublines / 6 supports; 0 pairs")
    print("Explicit 3-block witness and coinciding-support negative control PASS")

if __name__=="__main__":
    main()
