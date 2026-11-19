"""Reproducible exact checks for the ordinary Boston rank paper (standard library)."""
from collections import Counter
from functools import lru_cache
from fractions import Fraction as F
from itertools import permutations,product
from math import comb,factorial,prod

def ck(x):
    if not x: raise ArithmeticError("exact identity failed")

@lru_cache(None)
def trans(k,D):
    # j distinct free schools are hit; inclusion-exclusion within their labels.
    x=[F(comb(k,j)*sum((-1)**(j-h)*comb(j,h)*(D-k+h)**k for h in range(j+1)),D**k) for j in range(k+1)]
    ck(sum(x)==1 and min(x)>=0)
    return x

@lru_cache(None)
def tail(k,D):
    # (rounds until completion, total subsequent bids), conditional on a boundary.
    if not k:return {(0,0):F(1)}
    out=Counter()
    for j,p in enumerate(trans(k,D)):
        if p:
            for (rounds,bids),q in tail(k-j,D-1).items():out[rounds+1,bids+k]+=p*q
    return out

def direct(profile,school_specific):
    n=len(profile);left=list(range(n));free=set(range(n));count=0
    for r in range(n):
        count+=len(left);win={}
        for i in left:
            h=profile[i][r]
            if h in free:
                # Fixed priorities: common or cyclically different by house.
                priority=(i-h)%n if school_specific else i
                if h not in win or priority<win[h][0]:win[h]=priority,i
        free.difference_update(win);matched={i for _,i in win.values()}
        left=[i for i in left if i not in matched]
        if not left:return r+1,count
    raise ArithmeticError("incomplete match")

def main():
    cases=0
    for n in range(1,5):
        rows=list(permutations(range(n)))
        bins=[Counter(),Counter()]
        for ps in product(rows,repeat=n):
            for mode in (0,1):bins[mode][direct(ps,mode)]+=1;cases+=1
        for b in bins:
            ck({k:F(v,factorial(n)**n) for k,v in b.items()}==tail(n,n))
    print("Exact complete preference-profile/priority cases:",cases,"joint worst rank / total rank histograms match")
    kcases=0
    for D in range(1,32):
        for k in range(1,D+1):
            q=trans(k,D)
            ck(q[k]==F(factorial(k),D**k) and q[k]<=F(1,D))
            ck(sum((k-j)*p for j,p in enumerate(q))==k*F(D-1,D)**k)
            prob=F(1)
            for a in range(D+1):
                ck(prob==F(comb(D-a,k),comb(D,k))**k)
                kcases+=1
                if a<D:prob*=F(max(D-a-k,0),D-a)**k
    print("Exact holding-time probabilities:",kcases,"; final hazard and one-step drift also match")
    sta=0
    # Independently implement sequential proposal exposure, including round ties.
    # Multiplying event weights yields the one-success normalized martingale identity
    # E B_n=H_n−sum_k E[d_k]/(n k). Here only rank ages, not priorities, matter.
    for n in range(1,11):
        p={(n,n):F(1)};deficit=F(0)
        for r in range(n):
            D=n-r;after=Counter()
            for (start,k),prob in p.items():
                ck(start==k)
                states={k:prob}
                for _ in range(start):
                    new=Counter()
                    for current,weight in states.items():
                        hit=F(current,D)*weight
                        if hit:
                            new[current-1]+=hit
                            deficit+=hit*F(r,n*current)
                        if weight>hit:new[current]+=weight-hit
                    states=new
                for k2,weight in states.items():after[k2,k2]+=weight
            p=after
        ck(p=={(0,0):F(1)})
        eb=sum(F(bids,n)*prob for (R,bids),prob in tail(n,n).items())
        hn=sum(F(1,k) for k in range(1,n+1))
        ck(eb==hn-deficit)
        ew=sum(R*val for (R,bids),val in tail(n,n).items())
        ck(ew>=F(n+1,2))
        sta+=1
    print("Exact finite mean deficit identities and terminal rank bounds:",sta)
    a=prod(F(j*j,j*j+1) for j in range(1,21))
    ck(a<F(5,17) and (11-17*a)/6>1)
    print("Strict additive comparison, 20-factor rational upper bound on a_1: PASS")
if __name__=='__main__':main()
