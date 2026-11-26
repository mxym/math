from fractions import Fraction as F
from itertools import product
from math import isqrt

def prime(p):
    return p >= 2 and all(p%d for d in range(2,isqrt(p)+1))

def support(n):
    out = []
    d = 2
    while d*d <= n:
        if n%d == 0:
            out.append(d)
            while n%d == 0:
                n //= d
        d += 1
    if n>1:
        out.append(n)
    return frozenset(out)

Q=10**9
SMALL, LARGE = 1000, 10000
LOW=(0, 8000000, 33000000, 86000000, 173000000)
HIGH=(0, 1000000, 6000000, 17000000, 39000000)
MINS=(7,13,19,31)

def ceildiv(x,y):
    return (x+y-1)//y

def vectors(t, cap, n=1):
    if t==0:
        yield n
        return
    for a in range(cap+1):
        yield from vectors(t-1,cap-a,n*MINS[t-1]**a)

from math import comb
for t in range(1,5):
    for cutoff, budget in [(SMALL,LOW[t]),(LARGE,HIGH[t])]:
        scaled = sum(ceildiv(Q,max(cutoff-1,isqrt(n)-2))
                     for n in vectors(t,20) if n>1)
        scaled += ceildiv(Q*4*comb(20+t,t-1)*2**21,5**21)
        assert scaled < budget

small=[]
medium=[]
for s in range(5,LARGE+1,6):
    if prime(s):
        u=support(s*s+s+1)
        if len(u)<=4:
            (small if s<=SMALL else medium).append((s,u))

unions={frozenset()}
for s,u in small:
    unions |= {u|v for v in unions if len(u|v)<=4 and
               (len(u|v)<4 or any(x%12==1 for x in u|v))}
assert (len(small),len(medium),len(unions))==(86,525,22851)

def first_primes(res,mod,count,excluded):
    result=[]
    while len(result)<count:
        if res not in excluded and prime(res):
            result.append(res)
        res+=mod
    return result

def cap(x):
    return F(x,x-1)

from math import prod
hard=[0]*5
high=[F(0)]*5
for U in unions:
    ordinary={s for s,u in small if u<=U}
    ordinary_cap=prod(F(s*s+s+1,s*s) for s in ordinary)
    early=first_primes(5,6,len(ordinary)+3,set())
    gains=sorted((F(s**3,s**3-1) if s in ordinary else cap(s)
                  for s in early),reverse=True)
    for t in range(max(1,len(U)),5):
        choices=[p for p in U if p%12==1]
        if len(U)<t:
            choices += first_primes(13,12,4,U)
        for p in choices:
            fixed=U-{p}
            if len(fixed)>t-1:
                continue
            other=first_primes(7,6,t-1-len(fixed),U|{p})
            base=ordinary_cap*cap(p)*prod(map(cap,list(fixed)+other))*prod(gains[:4-t])
            if base < 2*(1-F(LOW[t],Q)):
                continue
            hard[t]+=1
            group={}
            for s,V in medium:
                outside=V-U
                if len(outside)>t-len(U):
                    continue
                if len(outside)==t-len(U) and p not in U and not any(r%12==1 for r in outside):
                    continue
                key=min(outside,default=0)
                group[key]=group.get(key,0)+ceildiv(Q,s-1)
            additive=group.pop(0,0)+sum(sorted(group.values(),reverse=True)[:t-len(U)])+HIGH[t]
            assert additive<Q
            bound=base/(1-F(additive,Q))
            assert bound < F(197,100)
            high[t]=max(high[t],bound)
assert hard==[0,0,0,2,46]
print((len(small),len(medium),len(unions)),hard,[float(x) for x in high])
