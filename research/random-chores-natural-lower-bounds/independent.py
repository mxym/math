#!/usr/bin/env python3
"""Independent rational intervals for both constants; no external modules or float tests."""
from fractions import Fraction as Q
from math import factorial,comb,prod
from itertools import product,permutations
from functools import lru_cache
def ck(p,m):
    if not p:raise ValueError(m)
def plus(a,b):return a[0]+b[0],a[1]+b[1]
def times(t,a):return tuple(sorted([t*a[0],t*a[1]]))
@lru_cache(None)
def logunit(q):
    ck(Q(1,2)<=q<=1,'interval')
    # -log(q)=sum (1-q)^i/i; use termwise positive and geometric tail.
    r=1-q; power=Q(1);s=Q(0);N=82
    for i in range(1,N+1):
        power*=r;s+=power/i
    R=power*r/(N+1)/(1-r)
    return -s-R,-s
def log(q):
    k=0
    while q>1:q/=2;k+=1
    while q<Q(1,2):q*=2;k-=1
    return plus(logunit(q),times(-k,logunit(Q(1,2))))
def H(q):return plus(times(-q,log(q)),times(q-1,log(1-q)))
def at(u,a):
    # Algebraically: J=H(a)+u H(a/u)+c log(c)-c log(1-a)-c.
    c=1+u;v=plus(plus(H(a),times(u,H(a/u))),times(c,plus(log(c),times(-1,log(1-a)))))
    J=plus(v,(-c,-c))
    D=plus(log((1-a)*(u-a)/(a*a)),(c/(1-a),c/(1-a)))
    return J,D
def gridout(x):return (x*10**18).__floor__()
for end,a0,sign in [('0.26016893448','0.24517056613318965',-1),('0.26016893449','0.24517056614238555',1)]:
    u=Q(end);a=Q(a0);J,D=at(u,a)
    lo=J[0];hi=J[1]+max(0,D[1]*(u-a),-D[0]*a)
    ck((hi<0) if sign<0 else lo>0,'first moment')
    print('u',end,'bounds on max(J) in 1e-18 units',gridout(lo),gridout(hi)+1)
def em(q):
    ck(0<=q<=3,'exp radius')
    N=42;term=s=Q(1)
    for j in range(1,N+1):
        term*=q/j;s+=term
    r=term*q/(N+1)/(1-q/(N+2))
    return 1/(s+r),1/s
def g(z,mode):
    return (3-z)/(1+z) if mode=='full' else 2-z
lams=[('full','1.36145148634','1.77931268854109573615',1),('full','1.36145148635','1.77931268852057998428',-1),('two','1.25532039069','1.39598750402847827058',1),('two','1.25532039070','1.39598750401462550470',-1)]
for mode,c0,x0,s in lams:
    c=Q(c0);x=Q(x0);dy=Q(1,10**18)
    a,b=x-dy,x+dy
    ck(g(em(a)[1],mode)>c*a and g(em(b)[0],mode)<c*b,'fixed point bracket')
    lo=1-(1+a)*em(a)[1]-2*(1-1/c);hi=1-(1+b)*em(b)[0]-2*(1-1/c)
    ck(lo>0 if s==1 else hi<0,'strict forcing margin sign')
    print(mode,c0,'fixed-point forcing margin 1e-18 units',gridout(lo),gridout(hi)+1)
# Finite verification of ordinal row probability through permutations.
tests=0
for s in range(1,7):
    for b in range(2,9-s):
        N=s+b
        ords=sum(1 for z in permutations(range(N)) if all(v<b for v in z[:b]))
        ck(Q(ords,factorial(N))==Q(1,comb(N,b)),'ordinal factor')
        tests+=1
# Enumerate all small nonempty assignments, with independent rank-event
# probabilities, aggregate directly vs compositions.
cases=0
for n in range(2,5):
    for m in range(n,min(2*n,8)):
        d={}
        from collections import Counter
        counts=Counter(tuple(z.count(i) for i in range(n)) for z in product(range(n),repeat=m))
        for sizes,numb in counts.items():
            if min(sizes)==0:continue
            s=sizes.count(1);r=n-s;prob=Q(1,s**s)
            for b in sizes:
                if b>1:prob/=comb(s+b,b)
            d[r]=d.get(r,0)+numb*prob
        for r,ans in d.items():
            s=n-r
            if not r:ck(ans==Q(factorial(n),n**n),'perfect rank assignment');continue
            v=0
            for h in product(range(1,m-n+1),repeat=r):
                if sum(h)!=m-n:continue
                v+=Q(comb(n,r)*factorial(m),s**s)*prod(Q(factorial(s),factorial(s+1+i)) for i in h)
            bound=Q(comb(n,r)*comb(m-n-1,r-1)*factorial(m),s**m)
            ck(v==ans<=bound,'composition identity')
        cases+=1
print('ordinal permutation tests',tests,'; exhaustive labeled allocation markets',cases)
print('PASS')
