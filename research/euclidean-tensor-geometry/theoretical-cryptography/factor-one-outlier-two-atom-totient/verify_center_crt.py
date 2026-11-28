#!/usr/bin/env python3
from fractions import Fraction
from itertools import combinations
from math import gcd

def trim(p):
    p=[Fraction(x) for x in p]
    while len(p)>1 and p[-1]==0: p.pop()
    return p
def add(a,b):
    c=[Fraction(0)]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=x
    return trim(c)
def sub(a,b): return add(a,[-x for x in b])
def mul(a,b):
    c=[Fraction(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return trim(c)
def powp(a,n):
    r=[Fraction(1)]
    while n:
        if n&1:r=mul(r,a)
        a=mul(a,a);n//=2
    return r
def der(a): return trim([i*a[i] for i in range(1,len(a))] or [0])
def ev(a,x):
    s=Fraction(0);x=Fraction(x)
    for c in reversed(a):s=s*x+c
    return s
def divmodp(a,b):
    a=trim(a);b=trim(b);q=[Fraction(0)]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        z=a[-1]/b[-1];h=len(a)-len(b);q[h]=z
        for i,c in enumerate(b):a[i+h]-=z*c
        a=trim(a)
    return trim(q),a
def monic(a):
    a=trim(a)
    return a if a==[0] else [x/a[-1] for x in a]
def posnorm(a):
    a=trim(a)
    return a if a==[0] else [x/abs(a[-1]) for x in a]
def gcdp(a,b):
    while trim(b)!=[0]:
        _,r=divmodp(a,b);a,b=b,r
    return monic(a)
def sturm(a):
    g=gcdp(a,der(a));a,_=divmodp(a,g)
    s=[posnorm(a),posnorm(der(a))]
    while s[-1]!=[0]:
        _,r=divmodp(s[-2],s[-1])
        if r==[0]:break
        s.append(posnorm([-x for x in r]))
    return s
def variations(s,x):
    z=[]
    for p in s:
        v=ev(p,x)
        if v:z.append(1 if v>0 else -1)
    return sum(z[i]!=z[i-1] for i in range(1,len(z)))
def roots_open(poly,a,b):
    p=trim(poly)
    for x in (Fraction(a),Fraction(b)):
        while ev(p,x)==0:
            p,r=divmodp(p,[-x,1]);assert r==[0]
    if len(p)<=1:return 0
    s=sturm(p)
    return variations(s,a)-variations(s,b)
def center_poly(N,T,k):
    m=k-1;xm=[0]*m+[1];om=powp([-1,1],m)
    return sub(mul(om,sub([N],xm)),[T*x for x in xm])
def primes_upto(n):
    out=[]
    for x in range(2,n+1):
        if all(x%p for p in out if p*p<=x):out.append(x)
    return out
def isprime(n):
    if n<2:return False
    p=2
    while p*p<=n:
        if n%p==0:return False
        p+=1
    return True
def nextprime(n):
    while not isprime(n):n+=1
    return n
def bisect_root(poly,a,b,steps=90):
    lo,hi=Fraction(a),Fraction(b)
    assert roots_open(poly,lo,hi)==1
    for _ in range(steps):
        md=(lo+hi)/2
        if roots_open(poly,lo,md):hi=md
        else:lo=md
    return (lo+hi)/2
def require(x,m):
    if not x:raise AssertionError(m)

pr=primes_upto(31)[:8]
tuples=intervals=crt=0
for k in range(3,8):
  for ps in combinations(pr,k):
    N=T=1
    for p in ps:N*=p;T*=p-1
    C=center_poly(N,T,k)
    require(roots_open(C,1,N)==2,"two positive-domain centers")
    require(roots_open(C,ps[0],ps[-2])>=1,"left interlacing")
    require(roots_open(C,ps[1],ps[-1])>=1,"right interlacing")
    intervals+=2
    if gcd(N,T)==1:
      B=(ps[0]+ps[-1])//2
      z=(-pow(N,-1,T))%T
      K=B+N*z;M=N*T
      require(K%N==B%N and K%T==(B-1)%T,"CRT")
      for p in ps:
        w=p-B;v=w+K
        require(v%p==0 and v%(p-1)==0,"two divisor congruences")
        require(gcd(v,M)%(p*(p-1))==0,"unknown divisor")
        crt+=1
    tuples+=1

examples=0
for k in range(3,8):
  cluster=[];z=1009
  for _ in range(k-1):
    z=nextprime(z);cluster.append(z);z+=1
  for q,ps in [
      (nextprime(1600),tuple(cluster+[nextprime(1600)])),
      (nextprime(601),tuple([nextprime(601)]+[nextprime(1600+20*i) for i in range(k-1)]))
  ]:
    ps=tuple(sorted(ps));N=T=1
    for p in ps:N*=p;T*=p-1
    if q==ps[-1]:a,b=ps[0],ps[-2];cl=ps[:-1]
    else:a,b=ps[1],ps[-1];cl=ps[1:]
    C=center_poly(N,T,k);x=bisect_root(C,a,b)
    y=Fraction(N,1)/(x**(k-1))
    W=cl[-1]-cl[0];gap=min(abs(q-cl[0]),abs(q-cl[-1]))
    require(abs(y-q)*gap<=20*max(1,W*W),"two-atom error scale")
    examples+=1

require(tuples==218,"tuple count")
print("one-outlier totient center checker")
print(f"tuples_checked = {tuples}")
print(f"interlacing_intervals_checked = {intervals}")
print(f"CRT_factor_congruences_checked = {crt}")
print(f"two_atom_examples = {examples}")
print("two_center_sturm_count = PASS")
print("cluster_interlacing = PASS")
print("CRT_unknown_divisor_identity = PASS")
print("two_atom_error_scale = PASS")
print("standard_library_only = PASS")
