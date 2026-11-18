"""Rigorous FEI lower-bound certificate, standard library only. No inputs."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations
from collections import Counter
from hashlib import sha256

def check(t, name):
    if not t: raise ArithmeticError(name)

class Iv:
    def __init__(self, l, r=None):
        self.l=Q(l); self.r=Q(l if r is None else r)
    def __add__(self,b):
        if not isinstance(b,Iv): b=Iv(b)
        return Iv(self.l+b.l,self.r+b.r)
    __radd__=__add__
    def __mul__(self,b):
        b=Q(b)
        return Iv(self.l*b,self.r*b) if b>=0 else Iv(self.r*b,self.l*b)
    __rmul__=__mul__
    def __neg__(self): return self*(-1)
    def __sub__(self,b): return self+(-b)
    def __truediv__(self,b):return self*(1/Q(b))
    def show(self,n=16):
        s=10**n
        def fmt(k):return str(k//s)+'.'+str(k%s).zfill(n)
        a=self.l*s; b=self.r*s
        return '['+fmt(a.__floor__())+', '+fmt(b.__ceil__())+']'

def lnunit(x,terms=19):
    # Valid for 1<=x<=2. Positive tail bounded by a geometric series.
    z=(x-1)/(x+1); u=z*z; w=z; lo=Q(0)
    for i in range(terms):
        lo+=2*w/(2*i+1); w*=u
    return Iv(lo,lo+2*w/((2*terms+1)*(1-u)))

LN2=lnunit(Q(2))
@lru_cache(None)
def log2rat(x):
    if x<=0: raise ValueError("log domain")
    k=x.numerator.bit_length()-x.denominator.bit_length()
    m=x/(Q(2)**k)
    if m<1:m*=2;k-=1
    check(1<=m<2,"normalization")
    l=lnunit(m)
    return Iv(l.l/LN2.r,l.r/LN2.l)+k

def entropy_term(p):
    return log2rat(p)*(-p) if p else Iv(0)

# Reconstruct the public n=18 seed from graph theory, not from its truth table.
match=[sum(1<<(3*i+j) for i,j in enumerate(pi)) for pi in permutations(range(3))]
lines=[sum(1<<(3*i+j) for j in range(3)) for i in range(3)]+[sum(1<<(3*i+j) for i in range(3)) for j in range(3)]
active={};u=[];v=[]
for x in range(512):
    if any((x&b)==b for b in match): u.append(-1);v.append(0)
    elif any((x&b)==0 for b in lines): u.append(1);v.append(0)
    else:
        ok=[]
        for i in range(3):
            for j in range(3):
                c=3*i+j; arm=(lines[i]|lines[3+j])^(1<<c)
                if (x&~(1<<c))==arm: ok.append(c)
        check(len(ok)==1,"unique active edge")
        c=ok[0];active[x]=c;u.append(0);v.append(1-2*((x>>c)&1))
check(Counter(u)=={1:247,0:18,-1:247},"core partition")
# To compare to the published SHA-256, convert our natural row-major host
# numbering to Numaro's historical auxiliary-coordinate ordering.
hist_order=[0,4,7,1,3,6,8,5,2]
seed=[(u[i&511] or 1-2*((i>>(9+hist_order[active[i&511]]))&1)) for i in range(1<<18)]
check(sha256(','.join(map(str,seed)).encode()).hexdigest()=='f8a7bb2c738d86368305111633376b1a3a83d8ee1f1abcc9a37d841b0f9c7839','published seed hash')
for c in range(18):
    check(all(seed[x]>=seed[x|1<<c] for x in range(1<<18) if not (x>>c)&1),"logic monotonicity")
def walsh_direct(w,m):
    return sum(v*(-1 if ((x&m).bit_count()&1) else 1) for x,v in enumerate(w))

rows=Counter()
for m in range(512):
    a=walsh_direct(u,m); b=walsh_direct(v,m)
    check(a%2==0 and b%2==0,'integer half-coefficients')
    a//=2;b//=2
    rows[abs(a), int(b if a>0 else -b if a<0 else abs(b))]+=1
expected={(0,0):46,(1,1):108,(1,9):1,(2,-6):12,(2,2):72,(3,-5):18,(4,4):18,(5,-3):36,(8,0):72,(9,1):72,(19,3):12,(22,-2):36,(57,1):9}
check(rows==expected,'orbit spectrum')
rho=Q(57,256); lam=Q(1,256); total=9*lam
def core_entropy(t):
    return sum((cnt*entropy_term(((a+b*t)/256)**2) for (a,b),cnt in rows.items()),Iv(0))
H0=core_entropy(Q(0))+16*total
I0=9*rho+9*lam
check(I0==Q(261,128),"baseline influence")
old=H0/(I0-1);print("Old C lower-bound witness ratio",old.show())
check(Q('6.5218457109230465')<old.l<=old.r<Q('6.5218457109230466'),"Numaro interval")
# Chain d copies along one private coordinate, and graft nine chains into
# edge charts. Each of the nine chains shares exactly one bit with the core.
def graft(Hg,Ig,t):
    HG=core_entropy(t)+total*(Hg-entropy_term(t*t)+16*(1-t*t))
    IG=I0+total*(Ig-1)
    return HG,IG,HG/(IG-1)
# Simpler 162-bit witness, using a rare auxiliary as the shared coordinate.
Hs,Is,Rs=graft(H0,I0,lam)
print("162-bit amplified ratio",Rs.show(),"I =",Is)
check(Rs.l>Q('6.52185008365860'),"162-bit bound")
# 621-bit witness: four core-to-core copies with a distinguished endpoint.
t=rho**4
K=1+rho+rho**2+rho**3
Hg=K*H0;Ig=1+K*(I0-1)
H,I,R=graft(Hg,Ig,t)
print("621-bit amplified ratio",R.show(),"I =",I)
check(R.l>Q('6.52185093166203'),"621-bit bound")
# Strict positivity of the first variation (integer comparison, no logarithms).
check(2**864*5**540*11**1584>3**1539*19**1197,"first variation")
# Perform the same four-link + nine-graft operation one more time.
# The marked outer core influence increases by exactly lam*t: of the nine
# distinct center edges, only its own has that core coordinate free.
beta1=rho+lam*t
K1=1+beta1+beta1**2+beta1**3
H2,I2,R2=graft(K1*H,1+K1*(I-1),beta1**4)
print("22,329-bit amplified ratio",R2.show(),"I =",I2)
check(R2.l>Q('6.52185115673538'),"22329-bit bound")
for val,left,right in [
 (Rs,'6.5218500836586124','6.5218500836586125'),
 (R,'6.5218509316620414','6.5218509316620415'),
 (R2,'6.5218511567353856','6.5218511567353857')]:
    check(Q(left)<val.l<=val.r<Q(right),"strict printed endpoints")
for j in range(9):
    check(walsh_direct(u,1<<j)==114 and walsh_direct(v,1<<j)==2,"core singleton")
from math import prod
num=prod(a**(-a*b*c) for (a,b),c in rows.items() if a*b<0)
den=prod(a**(a*b*c) for (a,b),c in rows.items() if a*b>0)
check(Q(num,den)==Q(2**864*5**540*11**1584,3**1539*19**1197),"derivative factorization")


# Actual H/I of a finite ordinary disjoint self-composition, not the seed proxy.
# The number of input bits is 22,329**d; this is an implicit Boolean formula,
# not its truth table. Use an endpoint already strictly below R2.
L = Q("6.5218511567353856")
check(R2.l > L and I2 > 1, "lower endpoint for finite amplification")
for d, target in [(20, "6.5218457109230466"), (48, "6.52185115673538")]:
    finite_floor = L*(1-I2**(-d))
    check(finite_floor > Q(target), "finite disjoint composition")
    print("Actual H/I of depth", d, "strictly exceeds", target)
