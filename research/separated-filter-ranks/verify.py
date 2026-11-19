"""Exact finite cross-check, no libraries beyond Python. No assert statements."""
from collections import Counter
from itertools import combinations, permutations
from math import factorial
from functools import lru_cache

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)

def bits(mask):
    while mask:
        s=mask&-mask; yield s.bit_length()-1; mask^=s

def check(P):
    n=len(P);U=2**n-1
    def mins(s): return [i for i in bits(s) if not(P[i]&s)]
    @lru_cache(None)
    def e(s): return sum(e(s^(1<<i)) for i in mins(s)) if s else 1
    @lru_cache(None)
    def ranks(s,z):
        if not(s>>z&1):return ()
        row=[0]*(n+1)
        for i in mins(s):
            if i==z:row[1]+=e(s^(1<<i))
            else:
                for j,u in enumerate(ranks(s^(1<<i),z)[:-1]): row[j+1]+=u
        need(sum(row)==e(s),('bad rank sum',s,z))
        return tuple(row)
    ideals=[s for s in range(U+1) if all(not(P[x]&~s) for x in bits(s))]
    fil=[U^s for s in ideals]
    for A in fil:
        for B in fil:
            H=A&B;Y=A|B
            for z in bits(H):
                ra,rb,rh,ry=[ranks(s,z) for s in (A,B,H,Y)]
                for i in range(1,n+1):
                    for j in range(i,n+1):
                        if j-i < (B&~A).bit_count():continue
                        need(ra[i]*rb[j]<=rh[i]*ry[j],('spread',P,A,B,z,i,j))
                        cnt['spread inequalities']+=1
                        if B&~A==0 and A!=B and i<j:
                            cnt['strictly nested rank-ratio tests']+=1
    # Independent route for original F: direct enumeration, no filter identities.
    EE=[]
    for perm in permutations(range(n)):
        idx=tuple(perm.index(z) for z in range(n))
        if all(idx[i]<idx[j] for j in range(n) for i in bits(P[j])):EE.append(idx)
    need(len(EE)==e(U),('full extension count',P))
    for x,y,z in permutations(range(n),3):
        EE0=[v for v in EE if v[x]<v[y]<v[z]]
        if not EE0:continue
        F=Counter((v[y]-v[x],v[z]-v[y]) for v in EE0)
        def inc(x,y):return any(v[x]<v[y] for v in EE0) and any(v[x]>v[y] for v in EE0)
        I=[v for v in range(n) if inc(v,y)]
        Delta=max((sum(inc(v,w) for w in I) for v in I),default=0)
        for a in range(1,n-1):
            for b in range(1,n-a):
                for r in range(max(Delta,1),n-a-b):
                    for t in range(max(Delta,1),n-a-b-r):
                        need(F[a,b]*F[a+r,b+t]<=F[a+r,b]*F[a,b+t],('gap',P,x,y,z,a,b,r,t))
                        cnt['in-range gap comparisons']+=1
        # k,l≥2 require n≥7 to make both diagonal factors positive.
    cnt['naturally labelled orders']+=1

cnt=Counter()
def go(P):
    check(P)
    n=len(P)
    if n==5:return
    for ideal in range(1<<n):
        if all(not(P[v]&~ideal) for v in bits(ideal)):
            go(P+(ideal,))
go((0,))
need(cnt['naturally labelled orders']==1+2+7+40+357,'missing orders')
for k in sorted(cnt):print(k+':',cnt[k])
print('PASS. All naturally labelled finite orders through five points, all applicable filter pairs and in-range gaps.')
