#!/usr/bin/env python3
"""OR-tree optimum and all greedy ties by separate exact recurrences."""
from functools import lru_cache
from itertools import combinations
from fractions import Fraction
from random import Random

if not __debug__:
    raise RuntimeError("enable Python assertions")

def all_upsets(n):
    N=1<<n
    later=[sum(1<<j for j in range(i+1,N) if i&j not in [i,j]) for i in range(N)]
    upper=[sum(1<<j for j in range(N) if i&j==i) for i in range(N)]
    def rec(rest,truth):
        yield truth
        while rest:
            b=rest&-rest
            rest-=b
            i=b.bit_length()-1
            yield from rec(rest&later[i],truth|upper[i])
    yield from rec((1<<N)-1,0)

def solve(n,w):
    full=(1<<n)-1
    @lru_cache(None)
    def opt(S):
        if not(S&(S-1)):
            return 0
        a=(S-1)&S
        ans=None
        first=S&-S
        while a:
            if a&first:
                z=opt(a)+opt(S^a)
                ans=z if ans is None else min(ans,z)
            a=(a-1)&S
        return w[S]+ans
    @lru_cache(None)
    def greedies(state):
        if len(state)==1:
            return 0,0
        pairs=[(w[a|b],a,b) for a,b in combinations(state,2)]
        v=min(z for z,a,b in pairs)
        vals=[greedies(tuple(sorted([x for x in state if x not in (a,b)]+[a|b])))
              for z,a,b in pairs if z==v]
        return v+min(t[0] for t in vals),v+max(t[1] for t in vals)
    lo,hi=greedies(tuple(1<<i for i in range(n)))
    return opt(full),lo,hi

def check(n,w,D):
    O,g,G=solve(n,w)
    k=n//2
    R=w[-1]
    assert R<=O<=g<=G
    assert G<=O+(k-1)*R and G<=k*O
    assert 3*(D+2*G)<=(2*k+1)*(D+2*O)
    return O,g,G

monotone=0
for n,want in [(2,6),(3,20),(4,168),(5,7581)]:
    seen=set()
    for u in all_upsets(n):
        assert u not in seen
        seen.add(u)
        w=tuple(u>>s&1 for s in range(1<<n))
        check(n,w,1)
    assert len(seen)==want
    monotone+=len(seen)

crowns=0
for n in range(4,11):
    k=n//2
    left=list(range((n+1)//2))
    right=list(range((n+1)//2,n))
    b=(k-1) if n%2==0 else k
    safe=set(zip(left[:b],right[:b]))
    eq=[(1<<i)|(1<<j) for i,j in [*combinations(left,2),*combinations(right,2)]]
    cross=[(1<<i)|(1<<j) for i in left for j in right if (i,j) not in safe]
    main=[int(any(S&m==m for m in cross)) for S in range(1<<n)]
    pert=[int(any(S&m==m for m in eq)) for S in range(1<<n)]
    O,g,G=check(n,main,1)
    assert O==1 and G==k
    for D in [n,n*n,10*n]:
        w=tuple((D-1)*a+b for a,b in zip(main,pert))
        O,g,G=check(n,w,D)
        assert O==D+n-2 and g==G==k*D-(n%2==0)
        crowns+=1
    # Lower family is monotone but not subadditive.
    p=cross[0]
    assert main[p]==1 and main[p&-p]==main[p^(p&-p)]==0

cnt=0
for n in range(2,129):
    k=n//2
    for clusters in range(2,n+1):
        for frontier in range(max(2,2*clusters-n),n+1):
            G,O=clusters-1,frontier-1
            assert G-O<=k-1 and G<=k*O
            cnt+=1

rand=Random(115)
coverage=0
for n in range(2,9):
    H=sum((Fraction(1,r) for r in range(2,n+1)),Fraction(0))
    for _ in range(20):
        support=[rand.randrange(1,1<<n) for _ in range(7)]
        w=tuple(sum(bool(m&S) for m in support) for S in range(1<<n))
        O,lo,hi=check(n,w,7)
        assert hi<=4*H*O
        coverage+=1
print(f"exact recurrences: {monotone} Boolean monotone costs; {crowns} strict two-DNF instances; {coverage} coverage instances")
print(f"threshold arithmetic: {cnt} integer cases; non-subadditive negative control PASS")
print("verify_exact: PASS")
