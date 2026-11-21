#!/usr/bin/env python3
"""Independent finite checks. Standard library, safe under python -O."""
from itertools import combinations, product
from math import gcd, prod

def chk(b,s):
    if not b:raise ArithmeticError(s)
def fac(n):
    d=2;a={}
    while d*d<=n:
        while n%d==0:a[d]=a.get(d,0)+1;n//=d
        d+=1
    if n>1:a[n]=1
    return a
def det(A):
    n=len(A)
    if not n:return 1
    if n==1:return A[0][0]
    return sum((-1)**j*x*det([r[:j]+r[j+1:] for r in A[1:]]) for j,x in enumerate(A[0]) if x)
def smith(a):
    # gcd of all k-minors; output nonzero Smith factors in increasing order
    prev=1;out=[];rows=range(len(a));cols=range(len(a[0])) if a else ()
    for n in range(1,min(len(rows),len(cols))+1):
        g=0
        for I in combinations(rows,n):
            for J in combinations(cols,n):
                g=gcd(g,det([[a[i][j] for j in J] for i in I]))
        if not g:break
        chk(g%prev==0,"minor divisors");out.append(g//prev);prev=g
    return out
def generated(n,F):
    vals={1}
    for p in F:
        added=set();x=1
        while x not in added:
            added.add(x);x=min(x*p%n,-x*p%n)
        vals={min(x*y%n,-x*y%n) for x in added for y in vals}
    return vals
def acyclic(V,E,F):
    left=V-set(F)
    while left:
        end={v for v in left if not (E[v]&left)}
        if not end:return False
        left-=end
    return True
def scc(V,E):
    reach={}
    for v in V:
        a={v}
        while True:
            b=a|set().union(*(E[u] for u in a))
            if a==b:break
            a=b
        reach[v]=a
    return {tuple(sorted(u for u in reach[v] if v in reach[u])) for v in V}
def invariant_tail(n,J):
    U=sorted({min(u,-u%n) for u in range(1,n) if gcd(u,n)==1})
    ans=1
    for l,a in fac(len(U)).items():
        old=1
        for j in range(1,a+1):
            h=sum(pow(u,l**j,n) in (1,n-1) for u in U)
            q=h//old;rank=0
            while q%l==0:q//=l;rank+=1
            chk(q==1,"group layer");ans*=l**max(rank-J,0);old=h
    return ans
feedback=cases=blocks=0
for n in range(8,46,2):
    V={p for p in range(3,n-1,2) if gcd(p,n)==1 and fac(p)=={p:1}}
    E={p:set(fac(n-p)) for p in V}
    chk(all(x<=V for x in E.values()),"forward closure")
    U={min(u,-u%n) for u in range(1,n) if gcd(u,n)==1}
    chk(generated(n,V)==U,"all prime generators")
    for size in range(len(V)+1):
        for F in combinations(V,size):
            if acyclic(V,E,F):
                chk(generated(n,F)==U,("feedback",n,F));feedback+=1
    T=1;J=0
    for D in scc(V,E):
        a=[[int(p==q)-fac(n-p).get(q,0) for q in D] for p in D]
        ss=smith(a);J+=len(D)-len(ss);T*=prod(ss);blocks+=1
    chk(T%invariant_tail(n,J)==0,("tail",n));cases+=1
print("genuine finite centers, SCCs, exhaustive feedback sets:",cases,blocks,feedback)
# Triangular presentations with singular blocks and off-diagonal coupling.
synth=0
for diag in product((0,2,3),repeat=3):
    for off in product((0,1,6),repeat=3):
        a=[[diag[0],off[0],off[1]],[0,diag[1],off[2]],[0,0,diag[2]]]
        J=diag.count(0);T=prod(x for x in diag if x)
        # A finite quotient by adding three extra relators with diagonal 6,12,18.
        b=a+[[6,0,0],[0,12,0],[0,0,18]]
        inv=smith(b)[::-1];chk(T%prod(inv[J:])==0,(a,inv));synth+=1
# A large coupling really can create torsion: do not claim all torsion bounded by T.
chk(smith([[0,77],[0,0]])==[77],"large transient/coupling control")
print("finite quotients of singular/nonsingular block presentations:",synth,"PASS")
