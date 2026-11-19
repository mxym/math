"""Brute-force finite EF allocations versus rank-prefix forcing assertions.
Python standard library. This verifies a deterministic lemma on all nontrivial
3-by-4 relative preference profiles and several parameterized cardinal tables;
it does not prove the random local limit or asymptotic theorem."""
from fractions import Fraction as F
from itertools import permutations, product
from functools import lru_cache
from collections import Counter
def ck(x,s):
    if not x:raise ArithmeticError(s)
def requests(lists,active,k):
    n=len(lists); old=[set() for _ in range(n)]; rounds=0
    while True:
        new=[]
        for i,row in enumerate(lists):
            if not active[i]:new.append(set());continue
            J=set()
            for j in row[:k]:
                J.add(j)
                if not any(j in old[z] for z in range(n) if z!=i):break
            new.append(J)
        if new==old:return new,rounds
        ck(all(a<=b for a,b in zip(old,new)),'lost request')
        old=new;rounds+=1
def main():
    n,m,k=3,4,3
    alloc=[a for a in product(range(n),repeat=m) if len(set(a))==n]
    # By relabeling chores, fix the first preference ordering to identity.
    orders=list(permutations(range(m))); profiles=checks=ef=forbidden=rounds=0
    for order1,order2 in product(orders,repeat=2):
        lists=[tuple(range(m)),order1,order2]
        # All 2^n choices of easy/strained rows, independently of their rankings.
        for active in product((0,1),repeat=n):
            ranks=[[11,12,13,50] if z else [1,5,10,14] for z in active]
            costs=[[rs[row.index(j)] for j in range(m)] for row,rs in zip(lists,ranks)]
            req,t=requests(lists,active,k);rounds=max(t,rounds); profiles+=1
            blocked={j for j in range(m) if sum(j in s for s in req)>=2}
            forbidden+=len(blocked)>2*(m-n)
            for a in alloc:
                b=[[0]*n for _ in range(n)]
                for i in range(n):
                    for j,w in enumerate(a):b[i][w]+=costs[i][j]
                checks+=1
                if not all(b[i][i]==min(b[i]) for i in range(n)):continue
                ef+=1;sing={j for j,w in enumerate(a) if a.count(w)==1}
                ck(not(sing & blocked),'forbidden singleton in an EF partition')
                ck(all(a[j]==i for i,J in enumerate(req) for j in J&sing),'unsound request')
    print(f'Exhaustive n=3,m=4,k=3 up to chore relabeling, all good/bad row patterns: {profiles} profiles, {checks} nonempty allocations, {ef} EF allocations; all requests valid.')
    print(f'Maximum rounds to stabilize: {rounds}; {forbidden} profiles with immediate counting contradiction.')
    # Lower-bound the thinning recursion with exact rationals. At level v use
    # exp(-v) <= 1 / sum_{i=0}^40 v^i/i!, and round p down to millionths.
    for ratio in (F(5,4),F(19,10),F(39,20),F(199,100),F(1999,1000)):
        p=F(0)
        for rr in range(1,13):
            l=F(9,10)/ratio*sum(p**i for i in range(40))
            l=F(int(l*10**6),10**6)
            a=F(1); total=F(1)
            for j in range(1,41): a=a*l/j; total+=a
            p=F(int((1-1/total)*10**6),10**6)
            f=1-(1+l)/total
            if f>2*(1-1/ratio):break
        ck(f>2*(1-1/ratio),'explicit finite strict obstruction not certified')
        print(f'c={ratio}, K=40, t={rr}: strict forcing margin certified by rational bounds.')
    print('PASS')
if __name__=='__main__':main()
