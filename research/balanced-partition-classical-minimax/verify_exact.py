#!/usr/bin/env python3
"""Enumerate all maps, the full flat-source game, and arbitrary no-E caps."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb


def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0


def hyper(N,K,D):
    a,r=divmod(N,D)
    den=2*K*D*comb(N,K)
    return F(sum(multip*choose(b,t)*choose(N-b,K-t)*abs(D*t-K)
                 for b,multip in [(a,D-r),(a+1,r)] if multip
                 for t in range(K+1)),den)


def test_flat():
    maps, games, balanced_families = 0,0,0
    for N,D in product(range(1,6),range(1,5)):
        for K in range(1,N+1):
            A = tuple(combinations(range(N),K))
            best_average = F(1)
            balanced_count=0
            balanced_columns = [0]*len(A)
            known_support = F(1)
            for f in product(range(D),repeat=N):
                cells = [sum(abs(D*sum(f[x]==j for x in a)-K) for j in range(D)) for a in A]
                best_average=min(best_average,F(sum(cells),2*D*K*len(A)))
                known_support=min(known_support,F(cells[0],2*D*K))
                counts=[f.count(j) for j in range(D)]
                if max(counts)-min(counts)<=1:
                    balanced_count+=1
                    for i,val in enumerate(cells):
                        balanced_columns[i]+=val
                maps+=1
            V = hyper(N,K,D)
            assert best_average==V
            assert all(F(c,2*D*K*balanced_count)==V for c in balanced_columns)
            r=K%D
            assert known_support==F(r*(D-r),K*D)
            games+=1
            balanced_families+=balanced_count
    return maps,games,balanced_families


def test_real_caps():
    # Independent brute-force checks against the conditional HG with one fractional atom.
    games,maps=0,0
    for N,D in product(range(2,6),range(1,5)):
        for g in (F(2,3),F(2,5),F(3,4),F(3,10),F(3,7),F(5,11)):
            if g<F(1,N):
                continue
            K=int(1/g)
            r=1-K*g
            p=(g,)*K+(r,)+(0,)*(N-K-1)
            assert len(p)==N and r>0 and sum(p)==1
            perms=set(permutations(p))
            a,v=divmod(N,D)

            def W(b):
                total=0
                for j in (0,1):
                    if not 0<=b-j<=N-1:
                        continue
                    p_j=F(b if j else N-b,N)
                    total+=p_j*sum(F(choose(K,h)*choose(N-1-K,b-j-h),choose(N-1,b-j))
                                    *abs(g*h+r*j-F(1,D)) for h in range(K+1))
                return total

            exact=((D-v)*W(a)+(v*W(a+1) if v else 0))/2
            best=F(1)
            for f in product(range(D),repeat=N):
                b=tuple(f.count(j) for j in range(D))
                avg=sum(sum(abs(sum(w[i] for i in range(N) if f[i]==j)-F(1,D)) for j in range(D))
                        for w in perms)/(2*len(perms))
                best=min(best,avg)
                if max(b)-min(b)<=1:
                    assert avg==exact
                maps+=1
            assert best==exact
            games+=1
    return games,maps


def test_single_atom():
    checks=0
    for N in range(2,71):
        for D in range(2,N+1):
            if N%D:
                continue
            for K in range(1,N):
                b=N//D
                t=K//D
                atom=F(choose(b-1,t)*choose(N-b-1,K-1-t),choose(N-2,K-1))
                assert hyper(N,K,D)==F(D-1,D)*F(N-K,N-1)*atom
                checks+=1
    return checks


if __name__ == "__main__":
    a,b,c=test_flat()
    print(f"Classical flat games: {b} games, {a} deterministic map averages, {c} balanced map entries")
    print(f"Divisible alphabets: {test_single_atom()} single-atom identities")
    a,b=test_real_caps()
    print(f"Real caps: {a} exact games, {b} exhaustive deterministic map averages")
