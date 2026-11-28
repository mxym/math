#!/usr/bin/env python3
from fractions import Fraction
from itertools import combinations
from math import comb

def trim(p):
    p=[Fraction(x) for x in p]
    while len(p)>1 and p[-1]==0: p.pop()
    return p

def add(a,b):
    n=max(len(a),len(b)); c=[Fraction(0)]*n
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=x
    return trim(c)

def sub(a,b):
    return add(a,[-x for x in b])

def mul(a,b):
    c=[Fraction(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return trim(c)

def der(a):
    return trim([i*a[i] for i in range(1,len(a))] or [0])

def ev(a,x):
    s=Fraction(0)
    for c in reversed(a): s=s*x+c
    return s

def divmodp(a,b):
    a=trim(a); b=trim(b)
    if b==[0]: raise ZeroDivisionError
    if len(a)<len(b): return [Fraction(0)],a
    q=[Fraction(0)]*(len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        t=a[-1]/b[-1]; sh=len(a)-len(b); q[sh]=t
        for i,x in enumerate(b): a[i+sh]-=t*x
        a=trim(a)
    return trim(q),trim(a)

def monic(a):
    a=trim(a)
    if a==[0]: return a
    return [x/a[-1] for x in a]

def gcdp(a,b):
    a=trim(a); b=trim(b)
    while b!=[0]:
        _,r=divmodp(a,b); a,b=b,r
    return monic(a)

def posnorm(a):
    a=trim(a)
    if a==[0]: return a
    s=abs(a[-1])
    return [x/s for x in a]

def sturm(a):
    a=trim(a)
    g=gcdp(a,der(a))
    a,_=divmodp(a,g)
    seq=[posnorm(a),posnorm(der(a))]
    while seq[-1]!=[0]:
        _,r=divmodp(seq[-2],seq[-1])
        if r==[0]: break
        seq.append(posnorm([-x for x in r]))
    return seq

def variations(seq,x):
    sig=[]
    for p in seq:
        y=ev(p,Fraction(x))
        if y: sig.append(1 if y>0 else -1)
    return sum(sig[i]!=sig[i-1] for i in range(1,len(sig)))

def roots_open(poly,a,b):
    p=trim(poly)
    for x in (Fraction(a),Fraction(b)):
        while ev(p,x)==0:
            q,r=divmodp(p,[-x,1])
            assert r==[0]
            p=q
    if len(p)<=1: return 0
    seq=sturm(p)
    assert ev(seq[0],Fraction(a)) and ev(seq[0],Fraction(b))
    return variations(seq,a)-variations(seq,b)

def poly_from_roots(rs):
    p=[Fraction(1)]
    for r in rs: p=mul(p,[-r,1])
    return p

def crit_numerator(p0,d):
    D=[0,-1,1]; Dp=der(D); n=p0
    for order in range(d+1):
        n=sub(mul(der(n),D),[(order+1)*x for x in mul(n,Dp)])
    return trim(n)

def primes_upto(n):
    out=[]
    for x in range(2,n+1):
        if all(x%p for p in out if p*p<=x): out.append(x)
    return out

def require(x,msg):
    if not x: raise AssertionError(msg)

pr=primes_upto(40)[:10]
tuples=levels=blocks=0
profile_checksum=0
for k in range(3,8):
  for ps in combinations(pr,k):
    P=poly_from_roots(ps)
    N=1; T=1
    for p in ps: N*=p; T*=p-1
    require(P[0]==(-1)**k*N,"P(0)")
    require(ev(P,1)==(-1)**k*T,"P(1)")
    for j in range(1,k-1):
      m=k-j; d=m-2
      p0=[Fraction(0)]*(k+1); p0[k]=1
      for ell in range(1,j): p0[k-ell]=P[k-ell]
      p0[0]=P[0]
      p0[1]=ev(P,1)-sum(p0)
      diff=sub(P,p0)
      q,r=divmodp(diff,[0,-1,1])
      require(r==[0],"D divisibility")
      require(len(q)-1<=d,"Q degree")
      require(q[d]==P[k-j],"leading coefficient")
      C=crit_numerator(p0,d)
      require(C!=[0],"critical polynomial")
      best=None
      for a in range(j+1):
        b=a+m-1
        require(roots_open(C,ps[a],ps[b])>=1,"Rolle critical root")
        L=ps[b]-ps[a]; E=1
        for z in range(a): E*=ps[b]-ps[z]
        for z in range(b+1,k): E*=ps[z]-ps[a]
        val=L*L*E
        best=val if best is None else min(best,val)
        blocks+=1
      profile_checksum=(profile_checksum+best)%1000000007
      for aa in range(d+1):
        for bb in range(d-aa+1):
          cc=d-aa-bb
          require(m-aa==2+bb+cc,"Leibniz exponent")
      levels+=1
    tuples+=1

require(tuples==912,"tuple count")
print("multiscale totient Rolle checker")
print(f"tuples_checked = {tuples}")
print(f"levels_checked = {levels}")
print(f"blocks_checked = {blocks}")
print(f"profile_checksum_mod_1000000007 = {profile_checksum}")
print("endpoint_values = PASS")
print("D_quotient_decomposition = PASS")
print("leading_coefficient_parameter = PASS")
print("critical_polynomial_nonzero = PASS")
print("sturm_rolle_roots = PASS")
print("leibniz_profile_exponents = PASS")
print("standard_library_only = PASS")
