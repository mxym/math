"""Exact extension of the finite sanity check to mandatory rank anchors."""
from itertools import permutations
from functools import lru_cache
from collections import Counter
cnt=Counter()
def need(a,msg):
    if not a:raise ArithmeticError(msg)
def sub(S):
    T=S
    while True:
        yield T
        if not T:break
        T=(T-1)&S
def bits(S):
    while S:
        m=S&-S;yield m.bit_length()-1;S^=m
def check(P):
    n=len(P);full=2**n-1
    @lru_cache(None)
    def ext(S):
        if not S:return [()]
        return [(v,)+t for v in bits(S) if P[v]&S==0 for t in ext(S^(1<<v))]
    @lru_cache(None)
    def count(S,z):return Counter(t.index(z)+1 for t in ext(S))
    filters=[full^S for S in range(full+1) if all(not(P[v]&~S) for v in bits(S))]
    for A in filters:
        for B in filters:
            H=A&B;Y=A|B
            for z in bits(H):
                ra,rb,rh,ry=[count(s,z) for s in (A,B,H,Y)]
                for D in sub(P[z]&H):
                    if not D:continue # separately tested in verify.py
                    r=D.bit_count()+1
                    for j in range(r,n+1):
                        need(ra[r]*rb[j]<=rh[r]*ry[j],(P,D,A,B,z,r,j))
                        cnt['nonempty-compulsory-set tests']+=1
    for x,y,z in permutations(range(n),3):
        C=Counter()
        for w in ext(full):
            rx,ry,rz=map(w.index,(x,y,z))
            if rx<ry<rz:C[ry-rx,rz-ry]+=1
        if not C:continue
        # Compute open-interval sizes from intersections of observed elements
        # strictly between the marks in every order satisfying x<y<z.
        ab,bc=full,full
        for w in ext(full):
            a,b,c=map(w.index,(x,y,z))
            if a<b<c:
                ab&=sum(1<<v for v in w[a+1:b]);bc&=sum(1<<v for v in w[b+1:c])
        a,b=1+ab.bit_count(),1+bc.bit_count()
        need(a==min(i for i,j in C) and b==min(j for i,j in C),'individual minimum')
        if a==b==1:continue
        for i in range(a,n):
            for j in range(b,n-i):
                need(C[a,b]*C[i,j]<=C[i,b]*C[a,j],(P,x,y,z,a,b,i,j))
                cnt['shifted rectangle tests']+=1
    cnt['naturally labelled orders']+=1
def go(P):
    check(P);n=len(P)
    if n<5:
        for S in range(1<<n):
            if all(not(P[v]&~S) for v in bits(S)):go(P+(S,))
go((0,))
need(cnt['naturally labelled orders']==407,'enumeration')
for k in sorted(cnt):print(k+':',cnt[k])
print('PASS. Direct permutation counts; individual anchors verified after imposing the order of the marked triple.')
