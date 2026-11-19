#!/usr/bin/env python3
"""Finite exact consistency checks. Standard Python; no assert/optimization dependence."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations, product
from math import comb, factorial
from random import Random


def require(condition, msg):
    if not condition: raise ArithmeticError(msg)


def types(p):
    seen=set(); out=[]; pred=[-1]*len(p)
    for i,j in enumerate(p): pred[j]=i
    for i in range(len(p)):
        if i in seen: continue
        c=[]; j=i
        while j not in seen: c.append(j);seen.add(j);j=p[j]
        out.append(tuple(c))
    return tuple(pred),tuple(out)


@lru_cache(None)
def perms(n):
    ans=[]
    for p in permutations(range(n)):
        pre,cs=types(p)
        if sum(len(c)==1 for c in cs)>1: continue
        if not any(len(c)==1 for c in cs): g=1
        else: g=0
        core=tuple(c for c in cs if len(c)%2)
        sign=(-1)**sum(len(c)>2 and len(c)%2==0 for c in cs)
        ans.append((p,pre,core,sign,g))
    return ans


def instance(lists):
    n=len(lists);rank=[{j:t for t,j in enumerate(list(lists[i])+[i])} for i in range(n)]
    valid=[]
    for p,pre,core,sgn,g in perms(n):
        wr=[row[j] for row,j in zip(rank,p)]
        if any(rank[i][pre[i]]>wr[i] for i in range(n)): continue
        if any(rank[i][j]<wr[i] and rank[j][i]<wr[j] for i in range(n) for j in range(i)): continue
        valid.append((core,sgn,g))
    require(valid,'no stable partition')
    core=valid[0][0];X=sum(map(len,core))
    require(all(c==core for c,_,_ in valid),'different invariant odd cores')
    require(sum(sign for _,sign,_ in valid)==1,'signed count != 1')
    require(sum(sign*g for _,sign,g in valid)==valid[0][2],'fixed-free cancellation')
    return len(valid),X,any(len(c)==1 for c in core),int((n%2==0 and not core)or(n%2==1 and X==1))


def profiles():
    for n in (3,4):
        ans=Counter();cnt=0
        for lists in product(*[permutations([j for j in range(n) if i!=j]) for i in range(n)]):
            v,x,f,sol=instance(lists);cnt+=1;ans[sol]+=1
        require(F(ans[1],cnt)=={3:F(3,4),4:F(26,27)}[n],'known probability')
        print('all labeled profiles, n =',n,':',cnt,'solvable',ans[1])
    rnd=Random(20261119)
    for n,rep in ((5,80),(6,60),(7,16),(8,4)):
        stats=Counter(); maxv=0
        for _ in range(rep):
            lists=[rnd.sample([j for j in range(n) if i!=j],n-1) for i in range(n)]
            v,x,_,_=instance(lists);stats[x]+=1;maxv=max(v,maxv)
        print('seeded complete rankings, n =',n,':',rep,'mass histogram',sorted(stats.items()),'max stable permutations',maxv)
    # Prescribed disjoint 3- and 4-cycles; top predecessor and second successor.
    cs=[(0,1,2),(3,4,5,6)]; n=7; lists=[None]*n
    for cyc in cs:
        for h,i in enumerate(cyc):
            first=[cyc[h-1],cyc[(h+1)%len(cyc)]]; lists[i]=first+[j for j in range(n) if j!=i and j not in first]
    v,x,f,sol=instance(lists);require((v,x,f,sol)==(3,3,False,0),'mixed-core fixture');print('mixed odd/even rotation fixture:',(v,x,f,sol))


def cyclepart(m,lo=3):
    if m==0: yield ()
    for l in range(lo,m+1):
        for tail in cyclepart(m-l,l):yield (l,)+tail


def multisetweight(P):
    w=1
    for l,k in Counter(P).items():w*=l**k*factorial(k)
    return F(1,w)


def coeff_checks():
    # Signed labelled cycle-partition enumeration vs. marked exponential differentiation.
    M=36; R=6
    @lru_cache(None)
    def h(m): # (1+z) exp(-z+z²/2)
        if m<0:return F(0)
        def e(k):
            if k<0:return F(0)
            return sum(F((-1)**(k-2*j),factorial(k-2*j)*2**j*factorial(j)) for j in range(k//2+1))
        return e(m)+e(m-1)
    @lru_cache(None)
    def der(m,r):
        if r==0:return h(m)
        return sum(comb(r-1,j-1)*l**(j-1)*der(m-l,r-j) for j in range(1,r+1) for l in range(3,m+1,2))
    for m in range(M+1):
        t=[F(0)]*(R+1)
        for cs in cyclepart(m):
            w=(-1)**sum(l%2==0 for l in cs)*multisetweight(cs);x=sum(l for l in cs if l%2)
            for r in range(R+1):t[r]+=w*x**r
        require(t==[der(m,r) for r in range(R+1)],'signed marker coefficients')
    print('exact r-th coefficients: m=0..36, r=0..6:',(M+1)*(R+1),'comparisons')


def factors():
    def dfac(s):
        k=1
        for j in range(s,0,-2):k*=j
        return k
    count=0
    for n in range(1,151):
        A=F(1)
        for m in range(n%2,n+1,2):
            a=F(factorial(n)*dfac(n-m-1),factorial(n-m)*dfac(n+m-1))
            require(a==A,'parity product');A*=F(n-m,n+m+1);count+=1
    print('exact parity multipliers through n=150:',count)


def exact_integral(n,sizes):
    # One oriented permutation with this type. Integrate the blocking-pair
    # polynomial term by term, setting the singleton score to 1 if present.
    start=0;fixed=[]; skip=set();ex=[0]*n
    for l in sizes:
        if l==1: fixed.append(start)
        for a in range(start,start+l):
            b=start+(a-start+1)%l
            if a!=b:skip.add(tuple(sorted((a,b))))
            if l>=3:ex[a]=1
        start+=l
    require(start==n and len(fixed)<=1,'invalid cycle type')
    edge=[(i,j) for i in range(n) for j in range(i+1,n) if (i,j) not in skip]
    poly=Counter({tuple(ex):1})
    for i,j in edge:
        delta=Counter()
        for e,v in poly.items():
            if not v:continue
            a=list(e);a[i]+=i not in fixed;a[j]+=j not in fixed;delta[tuple(a)]-=v
        poly.update(delta)
    return sum(F(v,prod(a[i]+1 for i in range(n) if i not in fixed)) for a,v in poly.items() if v)


def prod(X):
    t=1
    for x in X:t*=x
    return t


def exact_small_odd():
    for n,expected in ((3,F(3,4)),(5,F(4075,6912)),(7,F(246462083,518400000))):
        value=0
        for P in cyclepart(n-1,2):
            if any(i%2 for i in P):continue
            typ=(1,)+P
            count=factorial(n)*multisetweight(typ)
            value+=(-1)**sum(l>=4 for l in P)*count*exact_integral(n,typ)
        require(value==expected,'Mertens odd-size probability (21a-c)')
        print('singleton-stable solvability by exact signed integration, n =',n,':',value)


if __name__=='__main__':
    profiles();coeff_checks();factors();exact_small_odd();print('PASS')
