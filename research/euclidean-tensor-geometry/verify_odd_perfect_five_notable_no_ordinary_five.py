from fractions import Fraction as F
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

from math import comb, prod

Q=10**9
X,Y,Z=1000,10000,30000
CUTOFFS=(X,Y,Z)
BUDGETS=((0,8000000,33000000,86000000,173000000,305000000),
         (0,1000000,6000000,17000000,39000000,76000000),
         (0,1000000,6000000,17000000,18000000,37000000))
MINS=(7,13,19,31,37)

def ceildiv(x,y):
    return (x+y-1)//y

def vectors(t, cap, n=1):
    if t==0:
        yield n
        return
    for a in range(cap+1):
        yield from vectors(t-1,cap-a,n*MINS[t-1]**a)

for t in range(1,6):
    for cutoff,budget in zip(CUTOFFS,BUDGETS):
        scaled=sum(ceildiv(Q,max(cutoff-1,isqrt(n)-2))
                   for n in vectors(t,22) if n>1)
        scaled+=ceildiv(Q*4*comb(22+t,t-1)*2**23,5**23)
        assert scaled<budget[t],(t,cutoff,scaled)

small=[]
bands=[[],[]]
for s in range(11,Z+1,6): # 5 is not an ordinary root in this branch.
    if prime(s):
        U=support(s*s+s+1)
        if len(U)<=5:
            if s<=X:
                small.append((s,U))
            else:
                bands[s>Y].append((U,ceildiv(Q,s-1)))

unions={frozenset()}
smallmap={}
for s,U in small:
    smallmap.setdefault(U,[]).append(s)
    unions |= {U|V for V in unions if len(U|V)<=5 and
               (len(U|V)<5 or any(p%12==1 for p in U|V))}
assert (len(small),*(len(x) for x in bands),len(unions))==(85,530,1017,172928)

def first_primes(res,mod,count,excluded):
    L=[]
    while len(L)<count:
        if res not in excluded and prime(res):
            L.append(res)
        res+=mod
    return L

def cap(s):
    return F(s,s-1)

def subwords(U):
    subs=[frozenset()]
    for x in U:
        subs+=[V|{x} for V in subs]
    return subs

def medium(U,t,P,band):
    group={}
    slots=t-len(U)
    for V,z in band:
        W=V-U
        if len(W)>slots:
            continue
        if len(W)==slots and P not in U and not any(r%12==1 for r in W):
            continue
        key=min(W,default=0)
        group[key]=group.get(key,0)+z
    return group.pop(0,0)+sum(sorted(group.values(),reverse=True)[:slots])

hard=[0]*6
last=[]
L,H,J=BUDGETS
for U in unions:
    A={s for V in subwords(U) for s in smallmap.get(V,[])}
    base=prod(F(s*s+s+1,s*s) for s in A)
    early=first_primes(5,6,len(A)+4,set())  # 5 may still be notable.
    gains=sorted((F(s**3,s**3-1) if s in A else cap(s)
                  for s in early),reverse=True)
    for t in range(max(1,len(U)),6):
        choices=[P for P in U if P%12==1]
        if len(U)<t:
            choices+=first_primes(13,12,5,U)
        for P in choices:
            fixed=U-{P}
            if len(fixed)>t-1:
                continue
            other=first_primes(7,6,t-1-len(fixed),U|{P})
            B=base*cap(P)*prod(map(cap,list(fixed)+other))*prod(gains[:5-t])
            if B<2*F(Q-L[t],Q):
                continue
            hard[t]+=1
            D=medium(U,t,P,bands[0])
            if B<2*F(Q-D-H[t],Q):
                continue
            E=medium(U,t,P,bands[1])
            assert Q-D-E-J[t]>0
            result=B*F(Q,Q-D-E-J[t])
            assert result<F(1993,1000)
            last.append((tuple(sorted(U)),P,t,result))
assert hard==[0,0,0,8,1497,12075]
assert len(last)==6 and all(P==13 and t==4 for U,P,t,B in last)
print(hard,sorted((U,P,t,float(B)) for U,P,t,B in last))
