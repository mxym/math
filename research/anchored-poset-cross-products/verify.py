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
                for j in range(1,n+1):
                    cnt['filter inequalities']+=1
                    need(ra[1]*rb[j]<=rh[1]*ry[j],('filter',P,A,B,z,j))
                if ra[1] and H!=(1<<z):
                    s,t=A^(1<<z),H^(1<<z)
                    pp={w:e(s^(1<<w)) for w in mins(s)}
                    qq={b:e(t^(1<<b)) for b in mins(t)}
                    # Scaled to common denominator e(s)e(t).
                    out=sum(v*e(t) for w,v in pp.items() if not(H>>w&1))
                    short={b:qq.get(b,0)*e(s)-pp.get(b,0)*e(t) for b in bits(t)}
                    need(min(short.values())>=0 and sum(short.values())==out,('coupling balance',P,A,B,z))
                    cnt['coupling balances']+=1
    # Independent route for original F: direct enumeration, no filter identities.
    EE=[]
    for perm in permutations(range(n)):
        idx=tuple(perm.index(z) for z in range(n))
        if all(idx[i]<idx[j] for j in range(n) for i in bits(P[j])):EE.append(idx)
    need(len(EE)==e(U),('full extension count',P))
    for x,y,z in permutations(range(n),3):
        F=Counter((v[y]-v[x],v[z]-v[y]) for v in EE)
        for i in range(1,n-1):
            for j in range(1,n-i):
                need(F[1,1]*F[i,j]<=F[i,1]*F[1,j],('corner',P,x,y,z,i,j))
                cnt['corner inequalities']+=1
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
print('PASS. All naturally labelled finite orders through five points, all filter pairs, all marked triples.')
