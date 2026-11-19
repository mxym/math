"""Exact finite checks. Standard library, no imports from author code, fails closed."""
from fractions import Fraction as F
from itertools import product,combinations
from math import comb,prod

def check(ok,info):
    if not ok: raise ArithmeticError(info)

def slots(d):
    n=len(d)
    kids=[[] for _ in range(n)]
    for u in range(1,n):kids[d[u]].append(u)
    return sum(len(ch)==3 and z not in ch and all(not kids[c] for c in ch) for z,ch in enumerate(kids) if z)

def tree(d):
    for x in range(1,len(d)):
        seen=set()
        while x:
            if x in seen:return False
            seen.add(x);x=d[x]
    return True

def choose(u,v):
    return comb(u,v) if 0<=v<=u else 0

def independent_count(d):
    n=len(d);ans=[0]*(n+1)
    for b in range(1<<n):
        if not any((b>>u&1) and (b>>d[u]&1) for u in range(1,n)):
            ans[b.bit_count()]+=1
    return ans

def test():
    allmaps=alltrees=allflips=allcoeff=ratio=0
    for n in (5,6):
        z={(-1,)+a:slots((-1,)+a) for a in product(range(n),repeat=n-1)}
        check(sum(z.values())==(n-1)*comb(n-2,3)*(n-4)**(n-4),('expect',n))
        for p,v in z.items():
            for i in range(1,n):
                for y in range(p[i]+1,n):
                    new=p[:i]+(y,)+p[i+1:]
                    check(abs(v-z[new])<=6,('flip',p,new));allflips+=1
            if tree(p):
                alltrees+=1;a=independent_count(p)
                for l in range(v+1):
                    for k,total in enumerate(a):
                        lower=sum(comb(l,j)*choose(n-k-j+1,k-3*j) for j in range(l+1))
                        check(total>=lower,('lower',p,l,k));allcoeff+=1
        allmaps+=len(z)
        check(sum(tree(d) for d in z)==n**(n-2),('tree-prob',n))
    # Exact coefficient ratio with odd n endpoint and every valid s incl. endpoints.
    for n in range(5,151):
        for k in range(3,(n+1)//2+1):
            for s in range(k//3):
                a=n-k-s+1;b=k-3*s
                C=(b*(b-1)*(b-2));D=a*(a-b+1)*(a-b+2)
                check(comb(a-1,b-3)*D==comb(a,b)*C,('ratio',n,k,s));ratio+=1
    # 2- and 3-slot cases with repeated/shared and distinct attachment parents,
    # absent in exhaustive small trees. Use independently enumerated subset counts.
    corecases=0
    for t in (1,2,3):
        for h in (2,3):
            for parents in combinations(range(t+h-1),h):
                a=tuple(v-i for i,v in enumerate(parents))
                p=[-1]+[i-1 for i in range(1,t)]
                for u in a:
                    center=len(p);p.extend([u,center,center,center])
                poly=independent_count(p);n=len(p)
                check(slots(p)>=h,('slots',p))
                for l in range(h+1):
                    for k,total in enumerate(poly):
                        check(total>=sum(comb(l,j)*choose(n-k-j+1,k-3*j) for j in range(l+1)),('multi',p,k,l));allcoeff+=1
                corecases+=1
    print('Parent pointer maps:',allmaps,'single-pointer unordered flips:',allflips,'rooted labeled trees:',alltrees)
    print('Path-core multi-slot attachments:',corecases,'individual coefficient bounds:',allcoeff,'exact binomial neighbor ratios:',ratio)
    print('PASS')
if __name__=='__main__':test()
