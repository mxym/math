"""Finite rational checks for the two analytic proofs. Python standard library."""
from fractions import Fraction as Q
from itertools import product

def req(x):
    if not x: raise ArithmeticError('rational check failed')

# A finite (a=1, n=4096) instance of the continuum estimates.
# If L = -log G >= 2, then E exp[-1/(L+E)] >= exp(-1/L), so (L')^2 <= L^2 + 2+1/4.
# If L < 2, the integral to exp(-2) itself is >= exp(-5/2); this also bounds G_1.
# Thus L_n^2 <= (5/2)^2+(9/4)(n-1). For the prophet the saddle gives y+n/y>=2sqrt(n).
# Bound its integral to 3sqrt(n) by this constant integrand bound; beyond, integrate exp(-y).
n=4096; a=64
req(a*a==n)
Lbound=Q(25,4)+Q(9,4)*(n-1)
req(Lbound<97**2)
# G_n>exp(-97); M_n<193 exp(-128); e>2.
lower=Q(2**(2*a-97),3*a+1)
req(lower>10_000_000)
print('Explicit finite check for the continuous a=1 law: n=4096 gives ratio >10,000,000.')

# Independently sum ordered iid samples and verify the second-smallest recurrence.
cases=0
for costs,ps in [([Q(0),Q(1,3),Q(2,3)],[Q(1,4),Q(1,4),Q(1,2)]),
                 ([Q(1,50),Q(2,7),Q(9,10)],[Q(1,7),Q(2,7),Q(4,7)]),
                 ([Q(0),Q(1,6)],[Q(1,2),Q(1,2)])]:
    prev=sum(x*p for x,p in zip(costs,ps))
    for n in range(2,8):
        mn=snd=0
        for v in product(range(len(ps)),repeat=n):
            a,b=sorted(costs[i] for i in v)[:2]; wt=Q(1)
            for i in v:wt*=ps[i]
            mn+=wt*a;snd+=wt*b
        req(snd==mn+n*(prev-mn));prev=mn;cases+=1
print('Exact second-order-statistic identities checked on',cases,'discrete law/horizon pairs.')

# Finite rational examples of the envelope's comparison and Bellman restart.
stages=0
for j,n,b in [(2,64,8),(3,128,16),(4,256,32),(5,512,64)]:
    p=Q(1,2**j);q=1-2*p;A=(q/(1-p))**n;H=Q(1,4)
    req(H*q**b>=A and 0<A<H)
    def step(x):return p*min(A,x)+q*min(H,x)
    gb=p*A+q*H
    for _ in range(1,b):gb=step(gb)
    req(gb>=H*q**b and gb>=A)
    g=gb
    for _ in range(b,n):g=step(g)
    req(g>=A*(1-p)**(n-b))
    req(A*(1-p)**n==q**n)
    req(g/(4*q**n)>=(1-p)**(-b)/4)
    stages+=1
print('Exact three-level Bellman, offline balance and restart checks:',stages,'scales.')
