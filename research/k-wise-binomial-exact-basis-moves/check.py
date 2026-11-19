"""Exact finite phase checks. Python 3 standard library. No floating point or assert."""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
from math import comb,prod

def require(ok):
    if not ok: raise ArithmeticError("finite phase certificate failed")
def bases(N,k):
    return [tuple(x for a in st for x in (a,a+1)) for st in combinations(range(N),k//2)
            if all(v-u>=2 for u,v in zip(st,st[1:]))]
@lru_cache(None)
def C(N,J):
    # Numerators of signed cardinal weights. Each actual denominator has known sign.
    return tuple(tuple((-1)**(len(J)-1-j)*prod(x-h for h in J if h!=s)
                       for x in range(N+1)) for j,s in enumerate(J))
def signs(N,J,mu):
    return tuple(sum(a*b for a,b in zip(row,mu)) for row in C(N,J))
def require_jump(J,K):
    gone=set(J)-set(K);new=set(K)-set(J)
    require(gone and new=={t+2 for t in gone})
    require(all((b==a+1 if a in gone else b==a) for a,b in zip(J[::2],K[::2])))
    return len(gone)
counts=[0,0,0,0,0]
for n in range(3,14):
    N=n-1
    for k in range(2,N+1,2):
        bs=bases(N,k); sampled={}; pure_at={}; shared=set()
        def probe(p):
            if p in sampled:return
            sampled[p]=True
            a,b=p.numerator,p.denominator
            mu=[comb(N,x)*a**x*(b-a)**(N-x) for x in range(N+1)]
            which=[]
            for J in bs:
                w=signs(N,J,mu)
                if min(w)>=0:which.append((J,min(w)>0))
            require(which)
            if any(pos for _,pos in which):
                require(len(which)==1)
                pure_at[p]=which[0][0]
            else:shared.update((J,K) for J,_ in which for K,_ in which)
        for a in range(1,192):probe(F(a,192))
        for level in range(31):
            items=sorted(pure_at.items())
            gaps=[(p,v) for (p,J),(v,K) in zip(items,items[1:])
                  if J!=K and sum(K[::2])-sum(J[::2])!=1 and (J,K) not in shared]
            if not gaps:break
            for p,v in gaps:
                for h in (1,2,3):probe(p+(v-p)*h/4)
        else:raise ArithmeticError("could not certify coverage of a narrow phase")
        pure=[]
        for p,J in sorted(pure_at.items()):
            if not pure or pure[-1]!=J:pure.append(J)
        require(pure[0]==tuple(range(k)) and pure[-1]==tuple(range(n-k,n)))
        counts[0]+=1
        if k==N:
            require(len(pure)==2 and (pure[0],pure[1]) in shared)
            require(set(pure[0])-set(pure[1])=={0} and set(pure[1])-set(pure[0])=={N})
            counts[4]+=1
            continue
        total=0
        for J,K in zip(pure,pure[1:]):
            delta=sum(K[::2])-sum(J[::2])
            # No positive-length phase can be missing: the integer sum of starts
            # strictly increases (#220); otherwise a common feasible parameter
            # certifies adjacent closed intervals (#220). The new +2 rule is NOT
            # assumed in this coverage test.
            require(delta==1 or (J,K) in shared)
            r=require_jump(J,K);total+=r
            counts[1]+=1;counts[2]+=r==1;counts[3]+=r>1
        require(total==(k//2)*(n-k))
print("All n=3..13 and all even 2<=k<=n-1.")
print("instances, proper-range transitions, single, simultaneous, boundary instances:",*counts)
# Also test BEKK's larger simultaneous examples directly at p=1/2.
for n,J in [(23,(6,7,10,11,14,15)),(28,(8,9,13,14,17,18)),(35,(11,12,16,17,21,22))]:
    N=n-1;mu=[comb(N,x) for x in range(N+1)];w=signs(N,J,mu)
    require(min(w)>=0 and min(w[1::2])>0)
    K=tuple(t+(w[2*(i//2)]==0) for i,t in enumerate(J))
    v=signs(N,K,mu)
    require(min(v)>=0 and min(v[::2])>0 and {x for x,a in zip(J,w) if a}=={x for x,a in zip(K,v) if a})
    r=require_jump(J,K);require(r>=2)
    print("six-wise at p=1/2: n =",n,"actual departures =",r)
print("PASS")
