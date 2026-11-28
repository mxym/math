"""Finite checks for the signed-grid threshold and two-row separator.

Only fixed small synthetic cases. The script is not a general decoder.
"""
from itertools import product, combinations
from random import Random

def add(a,b,q,scale=1):
    return tuple((u+scale*v)%q for u,v in zip(a,b))

def shift(a,h,q):
    d=len(a)
    return tuple((-1 if j<h else 1)*a[(j-h)%d]%q for j in range(d))

def D(a,h,q):
    return add(a,shift(a,h,q),q,-1)

def syndrome(x,y,W,q):
    return add(D(x,W,q),D(y,1,q),q,-1)

def cols(W,q):
    d=W*W
    return [(i,(i+h)%d,s%q,(s*(-1 if i+h<d else 1))%q)
            for h,s in ((W,1),(1,-1)) for i in range(d)]

def interior(i,W):
    return 0<i%W<W-1 and 0<i//W<W-1

def adj(i,j,W):
    return abs(i%W-j%W)+abs(i//W-j//W)==1

triple_calls,syndrome_calls,unit_calls=0,0,0
rng=Random(683557)
for W,q in ((4,3),(4,9),(8,3)):
    d=W*W
    A=cols(W,q)
    B=[i for i in range(d) if interior(i,W)]
    possible=set()
    for i,j in combinations(range(2*d),2):
        for v,w in product(range(1,q),repeat=2):
            digits={}
            for a,b,x,y in [(A[i][0],A[i][1],A[i][2]*v,A[i][3]*v),
                            (A[j][0],A[j][1],A[j][2]*w,A[j][3]*w)]:
                digits[a]=(digits.get(a,0)+x)%q
                digits[b]=(digits.get(b,0)+y)%q
            T=tuple(sorted(k for k in digits if digits[k]))
            if len(T)==3 and all(digits[k]==q//3 and interior(k,W) for k in T):
                possible.add(T)
            syndrome_calls+=1
    for T in combinations(B,3):
        good=any(all(adj(i,j,W) for j in T if j!=i) for i in T)
        assert (T in possible)==good
        triple_calls+=1
    for _ in range(90):
        s=tuple(rng.randrange(q) for i in range(d))
        x,y=D(s,1,q),D(s,W,q)
        assert syndrome(x,y,W,q)==(0,)*d
        # Check the signs of the two fixed rows against literal columns.
        X=tuple(rng.randrange(q) for i in range(d))
        Y=tuple(rng.randrange(q) for i in range(d))
        literal=[0]*d
        for (u,v,a,b),f in zip(A,X+Y):
            literal[u]=(literal[u]+a*f)%q
            literal[v]=(literal[v]+b*f)%q
        assert syndrome(X,Y,W,q)==tuple(literal)
        # (1-X^h) (1+...+X^{d-h})=2 as an identity on a toy vector.
        for h in (1,W):
            r=(0,)*d
            for k in range(0,d,h):
                r=add(r,shift(s,k,q),q)
            assert D(r,h,q)==tuple(2*z%q for z in s)
            unit_calls+=1

component_calls=0
for terminal in range(1,181):
    for neutral in range(0,18):
        for extra in range(4):
            e=terminal+neutral-1+extra
            if terminal%3==0:
                good=(terminal,neutral,e)==(3,0,2)
                assert 3*e>=2*terminal
                assert (3*e==2*terminal)==good
                if not good: assert 6*e-4*terminal>=terminal
                component_calls+=1
            if neutral>0:
                assert 3*e>2*terminal and 6*e-4*terminal>=terminal
                component_calls+=1

# A single nonunit row's image separates into two disjoint coefficient
# groups at dimension eight, from a fixed base dimension-four factor.
def mul(x,y,q):
    d=len(x); u=[0]*d
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            u[(i+j)%d]+=(-1 if i+j>=d else 1)*a*b
    return tuple(v%q for v in u)
F=(2,1,1,0)  # X^2+X+2, one F3 factor of X^4+1
A=(2,0,1,0,1,0,0,0)  # F(X^2)
J={mul(F,x,3) for x in product(range(3),repeat=4)}
target={mul(A,x,3) for x in product(range(3),repeat=8)}
split={(a[0],b[0],a[1],b[1],a[2],b[2],a[3],b[3])
       for a,b in product(J,repeat=2)}
assert target==split and len(target)==len(J)**2==81
print("PASS: induced triples, low support checks, unit identities, component cases, split image:",
      triple_calls,syndrome_calls,unit_calls,component_calls,len(target))
